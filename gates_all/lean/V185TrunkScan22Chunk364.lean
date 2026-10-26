import V185TrunkScan22Chunk363

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3246212 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 7]
def baseStart_3246212 : Nat := 118140960795 + 3246212 * 2 ^ 59
def prefixEnd_3246212 : Nat := 4983230072969 + 3 ^ 40 * 3246212 * 2
def baseEnd_3246212 : Nat := 370414902754035203182433

theorem tailTrace_3246212 : CollatzResearch.WordTrace tailWord_3246212 prefixEnd_3246212 370414902754035203182433 := by
  unfold tailWord_3246212
  simp only [CollatzResearch.WordTrace]
  refine ⟨59199539257767903857982445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78932719010357205143976593 59199539257767903857982445)
  ·
    refine ⟨22199827221662963946743417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59199539257767903857982445 22199827221662963946743417)
    ·
      refine ⟨16649870416247222960057563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22199827221662963946743417 16649870416247222960057563)
      ·
        refine ⟨24974805624370834440086345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16649870416247222960057563 24974805624370834440086345)
        ·
          refine ⟨18731104218278125830064759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24974805624370834440086345 18731104218278125830064759)
          ·
            refine ⟨28096656327417188745097139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18731104218278125830064759 28096656327417188745097139)
            ·
              refine ⟨42144984491125783117645709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28096656327417188745097139 42144984491125783117645709)
              ·
                refine ⟨15804369184172168669117141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42144984491125783117645709 15804369184172168669117141)
                ·
                  refine ⟨370414902754035203182433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15804369184172168669117141 370414902754035203182433)
                  ·
                    rfl

theorem cell22_3246212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_3246212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246212 prefixEnd_3246212 := by exact prefixLift 3246212
  have htrace : WordTrace (prefixWord ++ tailWord_3246212) baseStart_3246212 baseEnd_3246212 := by
    simpa [prefixWord, tailWord_3246212, baseEnd_3246212] using wordTrace_append hprefix tailTrace_3246212
  have hstable : (prefixWord ++ tailWord_3246212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246212).length < 2 ^ (prefixWord ++ tailWord_3246212).sum := by decide
  have hdescent : baseEnd_3246212 < baseStart_3246212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246216 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 3, 3]
def baseStart_3246216 : Nat := 118140960795 + 3246216 * 2 ^ 59
def prefixEnd_3246216 : Nat := 4983230072969 + 3 ^ 40 * 3246216 * 2
def baseEnd_3246216 : Nat := 1111246077543850932447287

theorem tailTrace_3246216 : CollatzResearch.WordTrace tailWord_3246216 prefixEnd_3246216 1111246077543850932447287 := by
  unfold tailWord_3246216
  simp only [CollatzResearch.WordTrace]
  refine ⟨59199612203760658199555251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78932816271680877599407001 59199612203760658199555251)
  ·
    refine ⟨88799418305640987299332877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59199612203760658199555251 88799418305640987299332877)
    ·
      refine ⟨33299781864615370237249829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88799418305640987299332877 33299781864615370237249829)
      ·
        refine ⟨6243709099615381919484343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33299781864615370237249829 6243709099615381919484343)
        ·
          refine ⟨9365563649423072879226515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6243709099615381919484343 9365563649423072879226515)
          ·
            refine ⟨14048345474134609318839773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9365563649423072879226515 14048345474134609318839773)
            ·
              refine ⟨5268129552800478494564915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14048345474134609318839773 5268129552800478494564915)
              ·
                refine ⟨7902194329200717741847373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5268129552800478494564915 7902194329200717741847373)
                ·
                  refine ⟨2963322873450269153192765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7902194329200717741847373 2963322873450269153192765)
                  ·
                    refine ⟨1111246077543850932447287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2963322873450269153192765 1111246077543850932447287)
                    ·
                      rfl

theorem cell22_3246216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_3246216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246216 prefixEnd_3246216 := by exact prefixLift 3246216
  have htrace : WordTrace (prefixWord ++ tailWord_3246216) baseStart_3246216 baseEnd_3246216 := by
    simpa [prefixWord, tailWord_3246216, baseEnd_3246216] using wordTrace_append hprefix tailTrace_3246216
  have hstable : (prefixWord ++ tailWord_3246216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246216).length < 2 ^ (prefixWord ++ tailWord_3246216).sum := by decide
  have hdescent : baseEnd_3246216 < baseStart_3246216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246287 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 1, 6]
def baseStart_3246287 : Nat := 118140960795 + 3246287 * 2 ^ 59
def prefixEnd_3246287 : Nat := 4983230072969 + 3 ^ 40 * 3246287 * 2
def baseEnd_3246287 : Nat := 1111270382294830413922069

theorem tailTrace_3246287 : CollatzResearch.WordTrace tailWord_3246287 prefixEnd_3246287 1111270382294830413922069 := by
  unfold tailWord_3246287
  simp only [CollatzResearch.WordTrace]
  refine ⟨118401813990264095524945115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78934542660176063683296743 118401813990264095524945115)
  ·
    refine ⟨177602720985396143287417673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118401813990264095524945115 177602720985396143287417673)
    ·
      refine ⟨133202040739047107465563255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177602720985396143287417673 133202040739047107465563255)
      ·
        refine ⟨199803061108570661198344883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133202040739047107465563255 199803061108570661198344883)
        ·
          refine ⟨299704591662855991797517325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199803061108570661198344883 299704591662855991797517325)
          ·
            refine ⟨112389221873570996924068997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299704591662855991797517325 112389221873570996924068997)
            ·
              refine ⟨21072979101294561923262937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112389221873570996924068997 21072979101294561923262937)
              ·
                refine ⟨15804734325970921442447203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21072979101294561923262937 15804734325970921442447203)
                ·
                  refine ⟨23707101488956382163670805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15804734325970921442447203 23707101488956382163670805)
                  ·
                    refine ⟨1111270382294830413922069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23707101488956382163670805 1111270382294830413922069)
                    ·
                      rfl

theorem cell22_3246287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_3246287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246287 prefixEnd_3246287 := by exact prefixLift 3246287
  have htrace : WordTrace (prefixWord ++ tailWord_3246287) baseStart_3246287 baseEnd_3246287 := by
    simpa [prefixWord, tailWord_3246287, baseEnd_3246287] using wordTrace_append hprefix tailTrace_3246287
  have hstable : (prefixWord ++ tailWord_3246287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246287).length < 2 ^ (prefixWord ++ tailWord_3246287).sum := by decide
  have hdescent : baseEnd_3246287 < baseStart_3246287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246340 : List Nat := [2, 3, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_3246340 : Nat := 118140960795 + 3246340 * 2 ^ 59
def prefixEnd_3246340 : Nat := 4983230072969 + 3 ^ 40 * 3246340 * 2
def baseEnd_3246340 : Nat := 1111288525277955942346907

theorem tailTrace_3246340 : CollatzResearch.WordTrace tailWord_3246340 prefixEnd_3246340 1111288525277955942346907 := by
  unfold tailWord_3246340
  simp only [CollatzResearch.WordTrace]
  refine ⟨59201873529536042788312237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78935831372714723717749649 59201873529536042788312237)
  ·
    refine ⟨22200702573576016045617089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59201873529536042788312237 22200702573576016045617089)
    ·
      refine ⟨16650526930182012034212817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22200702573576016045617089 16650526930182012034212817)
      ·
        refine ⟨12487895197636509025659613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16650526930182012034212817 12487895197636509025659613)
        ·
          refine ⟨4682960699113690884622355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12487895197636509025659613 4682960699113690884622355)
          ·
            refine ⟨7024441048670536326933533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682960699113690884622355 7024441048670536326933533)
            ·
              refine ⟨2634165393251451122600075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7024441048670536326933533 2634165393251451122600075)
              ·
                refine ⟨3951248089877176683900113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634165393251451122600075 3951248089877176683900113)
                ·
                  refine ⟨2963436067407882512925085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3951248089877176683900113 2963436067407882512925085)
                  ·
                    refine ⟨1111288525277955942346907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2963436067407882512925085 1111288525277955942346907)
                    ·
                      rfl

theorem cell22_3246340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_3246340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246340 prefixEnd_3246340 := by exact prefixLift 3246340
  have htrace : WordTrace (prefixWord ++ tailWord_3246340) baseStart_3246340 baseEnd_3246340 := by
    simpa [prefixWord, tailWord_3246340, baseEnd_3246340] using wordTrace_append hprefix tailTrace_3246340
  have hstable : (prefixWord ++ tailWord_3246340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246340).length < 2 ^ (prefixWord ++ tailWord_3246340).sum := by decide
  have hdescent : baseEnd_3246340 < baseStart_3246340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246385 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 3, 3]
def baseStart_3246385 : Nat := 118140960795 + 3246385 * 2 ^ 59
def prefixEnd_3246385 : Nat := 4983230072969 + 3 ^ 40 * 3246385 * 2
def baseEnd_3246385 : Nat := 1111303929697590824971769

theorem tailTrace_3246385 : CollatzResearch.WordTrace tailWord_3246385 prefixEnd_3246385 1111303929697590824971769 := by
  unfold tailWord_3246385
  simp only [CollatzResearch.WordTrace]
  refine ⟨118405388343909058262012609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78936925562606038841341739 118405388343909058262012609)
  ·
    refine ⟨88804041257931793696509457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118405388343909058262012609 88804041257931793696509457)
    ·
      refine ⟨66603030943448845272382093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88804041257931793696509457 66603030943448845272382093)
      ·
        refine ⟨24976136603793316977143285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66603030943448845272382093 24976136603793316977143285)
        ·
          refine ⟨2341512806605623466607183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24976136603793316977143285 2341512806605623466607183)
          ·
            refine ⟨3512269209908435199910775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341512806605623466607183 3512269209908435199910775)
            ·
              refine ⟨5268403814862652799866163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512269209908435199910775 5268403814862652799866163)
              ·
                refine ⟨7902605722293979199799245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5268403814862652799866163 7902605722293979199799245)
                ·
                  refine ⟨2963477145860242199924717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7902605722293979199799245 2963477145860242199924717)
                  ·
                    refine ⟨1111303929697590824971769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2963477145860242199924717 1111303929697590824971769)
                    ·
                      rfl

theorem cell22_3246385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_3246385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246385 prefixEnd_3246385 := by exact prefixLift 3246385
  have htrace : WordTrace (prefixWord ++ tailWord_3246385) baseStart_3246385 baseEnd_3246385 := by
    simpa [prefixWord, tailWord_3246385, baseEnd_3246385] using wordTrace_append hprefix tailTrace_3246385
  have hstable : (prefixWord ++ tailWord_3246385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246385).length < 2 ^ (prefixWord ++ tailWord_3246385).sum := by decide
  have hdescent : baseEnd_3246385 < baseStart_3246385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246398 : List Nat := [4, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_3246398 : Nat := 118140960795 + 3246398 * 2 ^ 59
def prefixEnd_3246398 : Nat := 4983230072969 + 3 ^ 40 * 3246398 * 2
def baseEnd_3246398 : Nat := 370436126621087708132243

theorem tailTrace_3246398 : CollatzResearch.WordTrace tailWord_3246398 prefixEnd_3246398 370436126621087708132243 := by
  unfold tailWord_3246398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14800732811607745185279481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78937241661907974321490565 14800732811607745185279481)
  ·
    refine ⟨11100549608705808888959611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14800732811607745185279481 11100549608705808888959611)
    ·
      refine ⟨16650824413058713333439417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11100549608705808888959611 16650824413058713333439417)
      ·
        refine ⟨12488118309794035000079563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16650824413058713333439417 12488118309794035000079563)
        ·
          refine ⟨18732177464691052500119345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12488118309794035000079563 18732177464691052500119345)
          ·
            refine ⟨14049133098518289375089509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18732177464691052500119345 14049133098518289375089509)
            ·
              refine ⟨2634212455972179257829283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14049133098518289375089509 2634212455972179257829283)
              ·
                refine ⟨3951318683958268886743925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634212455972179257829283 3951318683958268886743925)
                ·
                  refine ⟨370436126621087708132243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3951318683958268886743925 370436126621087708132243)
                  ·
                    rfl

theorem cell22_3246398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_3246398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246398 prefixEnd_3246398 := by exact prefixLift 3246398
  have htrace : WordTrace (prefixWord ++ tailWord_3246398) baseStart_3246398 baseEnd_3246398 := by
    simpa [prefixWord, tailWord_3246398, baseEnd_3246398] using wordTrace_append hprefix tailTrace_3246398
  have hstable : (prefixWord ++ tailWord_3246398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246398).length < 2 ^ (prefixWord ++ tailWord_3246398).sum := by decide
  have hdescent : baseEnd_3246398 < baseStart_3246398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246426 : List Nat := [3, 1, 1, 2, 1, 2, 1, 7, 4]
def baseStart_3246426 : Nat := 118140960795 + 3246426 * 2 ^ 59
def prefixEnd_3246426 : Nat := 4983230072969 + 3 ^ 40 * 3246426 * 2
def baseEnd_3246426 : Nat := 370439321611826794898881

theorem tailTrace_3246426 : CollatzResearch.WordTrace tailWord_3246426 prefixEnd_3246426 370439321611826794898881 := by
  unfold tailWord_3246426
  simp only [CollatzResearch.WordTrace]
  refine ⟨29601720934190130566063783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78937922491173681509503421 29601720934190130566063783)
  ·
    refine ⟨44402581401285195849095675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29601720934190130566063783 44402581401285195849095675)
    ·
      refine ⟨66603872101927793773643513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44402581401285195849095675 66603872101927793773643513)
      ·
        refine ⟨49952904076445845330232635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66603872101927793773643513 49952904076445845330232635)
        ·
          refine ⟨74929356114668767995348953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49952904076445845330232635 74929356114668767995348953)
          ·
            refine ⟨56197017086001575996511715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74929356114668767995348953 56197017086001575996511715)
            ·
              refine ⟨84295525629002363994767573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56197017086001575996511715 84295525629002363994767573)
              ·
                refine ⟨1975676381929742906127365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84295525629002363994767573 1975676381929742906127365)
                ·
                  refine ⟨370439321611826794898881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1975676381929742906127365 370439321611826794898881)
                  ·
                    rfl

theorem cell22_3246426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_3246426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246426 prefixEnd_3246426 := by exact prefixLift 3246426
  have htrace : WordTrace (prefixWord ++ tailWord_3246426) baseStart_3246426 baseEnd_3246426 := by
    simpa [prefixWord, tailWord_3246426, baseEnd_3246426] using wordTrace_append hprefix tailTrace_3246426
  have hstable : (prefixWord ++ tailWord_3246426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246426).length < 2 ^ (prefixWord ++ tailWord_3246426).sum := by decide
  have hdescent : baseEnd_3246426 < baseStart_3246426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246471 : List Nat := [1, 1, 4, 2, 2, 1, 5, 6]
def baseStart_3246471 : Nat := 118140960795 + 3246471 * 2 ^ 59
def prefixEnd_3246471 : Nat := 4983230072969 + 3 ^ 40 * 3246471 * 2
def baseEnd_3246471 : Nat := 123481485472790585257945

theorem tailTrace_3246471 : CollatzResearch.WordTrace tailWord_3246471 prefixEnd_3246471 123481485472790585257945 := by
  unfold tailWord_3246471
  simp only [CollatzResearch.WordTrace]
  refine ⟨118408525021597494949643267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78939016681064996633095511 118408525021597494949643267)
  ·
    refine ⟨177612787532396242424464901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118408525021597494949643267 177612787532396242424464901)
    ·
      refine ⟨33302397662324295454587169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177612787532396242424464901 33302397662324295454587169)
      ·
        refine ⟨24976798246743221590940377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33302397662324295454587169 24976798246743221590940377)
        ·
          refine ⟨18732598685057416193205283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24976798246743221590940377 18732598685057416193205283)
          ·
            refine ⟨28098898027586124289807925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18732598685057416193205283 28098898027586124289807925)
            ·
              refine ⟨2634271690086199152169493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28098898027586124289807925 2634271690086199152169493)
              ·
                refine ⟨123481485472790585257945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2634271690086199152169493 123481485472790585257945)
                ·
                  rfl

theorem cell22_3246471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 6].length) (baseStart_3246471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246471 prefixEnd_3246471 := by exact prefixLift 3246471
  have htrace : WordTrace (prefixWord ++ tailWord_3246471) baseStart_3246471 baseEnd_3246471 := by
    simpa [prefixWord, tailWord_3246471, baseEnd_3246471] using wordTrace_append hprefix tailTrace_3246471
  have hstable : (prefixWord ++ tailWord_3246471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246471).length < 2 ^ (prefixWord ++ tailWord_3246471).sum := by decide
  have hdescent : baseEnd_3246471 < baseStart_3246471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246473 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 2, 4]
def baseStart_3246473 : Nat := 118140960795 + 3246473 * 2 ^ 59
def prefixEnd_3246473 : Nat := 4983230072969 + 3 ^ 40 * 3246473 * 2
def baseEnd_3246473 : Nat := 1111334053895987928771499

theorem tailTrace_3246473 : CollatzResearch.WordTrace tailWord_3246473 prefixEnd_3246473 1111334053895987928771499 := by
  unfold tailWord_3246473
  simp only [CollatzResearch.WordTrace]
  refine ⟨118408597967590249291216073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78939065311726832860810715 118408597967590249291216073)
  ·
    refine ⟨88806448475692686968412055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118408597967590249291216073 88806448475692686968412055)
    ·
      refine ⟨133209672713539030452618083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88806448475692686968412055 133209672713539030452618083)
      ·
        refine ⟨199814509070308545678927125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133209672713539030452618083 199814509070308545678927125)
        ·
          refine ⟨9366305112670713078699709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 199814509070308545678927125 9366305112670713078699709)
          ·
            refine ⟨3512364417251517404512391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9366305112670713078699709 3512364417251517404512391)
            ·
              refine ⟨5268546625877276106768587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512364417251517404512391 5268546625877276106768587)
              ·
                refine ⟨7902819938815914160152881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5268546625877276106768587 7902819938815914160152881)
                ·
                  refine ⟨5927114954111935620114661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7902819938815914160152881 5927114954111935620114661)
                  ·
                    refine ⟨1111334053895987928771499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5927114954111935620114661 1111334053895987928771499)
                    ·
                      rfl

theorem cell22_3246473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 4].length) (baseStart_3246473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246473 prefixEnd_3246473 := by exact prefixLift 3246473
  have htrace : WordTrace (prefixWord ++ tailWord_3246473) baseStart_3246473 baseEnd_3246473 := by
    simpa [prefixWord, tailWord_3246473, baseEnd_3246473] using wordTrace_append hprefix tailTrace_3246473
  have hstable : (prefixWord ++ tailWord_3246473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246473).length < 2 ^ (prefixWord ++ tailWord_3246473).sum := by decide
  have hdescent : baseEnd_3246473 < baseStart_3246473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246503 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 3, 3]
def baseStart_3246503 : Nat := 118140960795 + 3246503 * 2 ^ 59
def prefixEnd_3246503 : Nat := 4983230072969 + 3 ^ 40 * 3246503 * 2
def baseEnd_3246503 : Nat := 1111344323509077850521407

theorem tailTrace_3246503 : CollatzResearch.WordTrace tailWord_3246503 prefixEnd_3246503 1111344323509077850521407 := by
  unfold tailWord_3246503
  simp only [CollatzResearch.WordTrace]
  refine ⟨118409692157481564414808163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78939794771654376276538775 118409692157481564414808163)
  ·
    refine ⟨177614538236222346622212245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118409692157481564414808163 177614538236222346622212245)
    ·
      refine ⟨8325681479822922497916199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 177614538236222346622212245 8325681479822922497916199)
      ·
        refine ⟨12488522219734383746874299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8325681479822922497916199 12488522219734383746874299)
        ·
          refine ⟨18732783329601575620311449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12488522219734383746874299 18732783329601575620311449)
          ·
            refine ⟨14049587497201181715233587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18732783329601575620311449 14049587497201181715233587)
            ·
              refine ⟨21074381245801772572850381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14049587497201181715233587 21074381245801772572850381)
              ·
                refine ⟨7902892967175664714818893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21074381245801772572850381 7902892967175664714818893)
                ·
                  refine ⟨2963584862690874268057085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7902892967175664714818893 2963584862690874268057085)
                  ·
                    refine ⟨1111344323509077850521407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2963584862690874268057085 1111344323509077850521407)
                    ·
                      rfl

theorem cell22_3246503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_3246503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246503 prefixEnd_3246503 := by exact prefixLift 3246503
  have htrace : WordTrace (prefixWord ++ tailWord_3246503) baseStart_3246503 baseEnd_3246503 := by
    simpa [prefixWord, tailWord_3246503, baseEnd_3246503] using wordTrace_append hprefix tailTrace_3246503
  have hstable : (prefixWord ++ tailWord_3246503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246503).length < 2 ^ (prefixWord ++ tailWord_3246503).sum := by decide
  have hdescent : baseEnd_3246503 < baseStart_3246503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246576 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 1, 5]
def baseStart_3246576 : Nat := 118140960795 + 3246576 * 2 ^ 59
def prefixEnd_3246576 : Nat := 4983230072969 + 3 ^ 40 * 3246576 * 2
def baseEnd_3246576 : Nat := 1111369312900929993446183

theorem tailTrace_3246576 : CollatzResearch.WordTrace tailWord_3246576 prefixEnd_3246576 1111369312900929993446183 := by
  unfold tailWord_3246576
  simp only [CollatzResearch.WordTrace]
  refine ⟨59206177343108548941107791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78941569790811398588143721 59206177343108548941107791)
  ·
    refine ⟨88809266014662823411661687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59206177343108548941107791 88809266014662823411661687)
    ·
      refine ⟨133213899021994235117492531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88809266014662823411661687 133213899021994235117492531)
      ·
        refine ⟨199820848532991352676238797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133213899021994235117492531 199820848532991352676238797)
        ·
          refine ⟨74932818199871757253589549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199820848532991352676238797 74932818199871757253589549)
          ·
            refine ⟨28099806824951908970096081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74932818199871757253589549 28099806824951908970096081)
            ·
              refine ⟨21074855118713931727572061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28099806824951908970096081 21074855118713931727572061)
              ·
                refine ⟨7903070669517724397839523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21074855118713931727572061 7903070669517724397839523)
                ·
                  refine ⟨11854606004276586596759285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7903070669517724397839523 11854606004276586596759285)
                  ·
                    refine ⟨1111369312900929993446183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11854606004276586596759285 1111369312900929993446183)
                    ·
                      rfl

theorem cell22_3246576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_3246576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246576 prefixEnd_3246576 := by exact prefixLift 3246576
  have htrace : WordTrace (prefixWord ++ tailWord_3246576) baseStart_3246576 baseEnd_3246576 := by
    simpa [prefixWord, tailWord_3246576, baseEnd_3246576] using wordTrace_append hprefix tailTrace_3246576
  have hstable : (prefixWord ++ tailWord_3246576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246576).length < 2 ^ (prefixWord ++ tailWord_3246576).sum := by decide
  have hdescent : baseEnd_3246576 < baseStart_3246576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246593 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3246593 : Nat := 118140960795 + 3246593 * 2 ^ 59
def prefixEnd_3246593 : Nat := 4983230072969 + 3 ^ 40 * 3246593 * 2
def baseEnd_3246593 : Nat := 1111375132348347615771131

theorem tailTrace_3246593 : CollatzResearch.WordTrace tailWord_3246593 prefixEnd_3246593 1111375132348347615771131 := by
  unfold tailWord_3246593
  simp only [CollatzResearch.WordTrace]
  refine ⟨118412974727155509785584433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78941983151437006523722955 118412974727155509785584433)
  ·
    refine ⟨88809731045366632339188325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118412974727155509785584433 88809731045366632339188325)
    ·
      refine ⟨16651824571006243563597811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88809731045366632339188325 16651824571006243563597811)
      ·
        refine ⟨24977736856509365345396717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16651824571006243563597811 24977736856509365345396717)
        ·
          refine ⟨9366651321191012004523769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24977736856509365345396717 9366651321191012004523769)
          ·
            refine ⟨7024988490893259003392827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9366651321191012004523769 7024988490893259003392827)
            ·
              refine ⟨10537482736339888505089241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7024988490893259003392827 10537482736339888505089241)
              ·
                refine ⟨7903112052254916378816931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10537482736339888505089241 7903112052254916378816931)
                ·
                  refine ⟨11854668078382374568225397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7903112052254916378816931 11854668078382374568225397)
                  ·
                    refine ⟨1111375132348347615771131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11854668078382374568225397 1111375132348347615771131)
                    ·
                      rfl

theorem cell22_3246593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3246593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246593 prefixEnd_3246593 := by exact prefixLift 3246593
  have htrace : WordTrace (prefixWord ++ tailWord_3246593) baseStart_3246593 baseEnd_3246593 := by
    simpa [prefixWord, tailWord_3246593, baseEnd_3246593] using wordTrace_append hprefix tailTrace_3246593
  have hstable : (prefixWord ++ tailWord_3246593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246593).length < 2 ^ (prefixWord ++ tailWord_3246593).sum := by decide
  have hdescent : baseEnd_3246593 < baseStart_3246593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246606 : List Nat := [4, 1, 1, 2, 3, 11]
def baseStart_3246606 : Nat := 118140960795 + 3246606 * 2 ^ 59
def prefixEnd_3246606 : Nat := 4983230072969 + 3 ^ 40 * 3246606 * 2
def baseEnd_3246606 : Nat := 13720735586592838459211

theorem tailTrace_3246606 : CollatzResearch.WordTrace tailWord_3246606 prefixEnd_3246606 13720735586592838459211 := by
  unfold tailWord_3246606
  simp only [CollatzResearch.WordTrace]
  refine ⟨14801681109513551625725959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78942299250738942003871781 14801681109513551625725959)
  ·
    refine ⟨22202521664270327438588939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14801681109513551625725959 22202521664270327438588939)
    ·
      refine ⟨33303782496405491157883409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22202521664270327438588939 33303782496405491157883409)
      ·
        refine ⟨24977836872304118368412557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33303782496405491157883409 24977836872304118368412557)
        ·
          refine ⟨9366688827114044388154709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24977836872304118368412557 9366688827114044388154709)
          ·
            refine ⟨13720735586592838459211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9366688827114044388154709 13720735586592838459211)
            ·
              rfl

theorem cell22_3246606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 11].length) (baseStart_3246606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246606 prefixEnd_3246606 := by exact prefixLift 3246606
  have htrace : WordTrace (prefixWord ++ tailWord_3246606) baseStart_3246606 baseEnd_3246606 := by
    simpa [prefixWord, tailWord_3246606, baseEnd_3246606] using wordTrace_append hprefix tailTrace_3246606
  have hstable : (prefixWord ++ tailWord_3246606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246606).length < 2 ^ (prefixWord ++ tailWord_3246606).sum := by decide
  have hdescent : baseEnd_3246606 < baseStart_3246606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246612 : List Nat := [2, 4, 3, 1, 1, 2, 1, 4, 4]
def baseStart_3246612 : Nat := 118140960795 + 3246612 * 2 ^ 59
def prefixEnd_3246612 : Nat := 4983230072969 + 3 ^ 40 * 3246612 * 2
def baseEnd_3246612 : Nat := 370460545478879299848691

theorem tailTrace_3246612 : CollatzResearch.WordTrace tailWord_3246612 prefixEnd_3246612 370460545478879299848691 := by
  unfold tailWord_3246612
  simp only [CollatzResearch.WordTrace]
  refine ⟨59206833857043338015263045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78942445142724450687017393 59206833857043338015263045)
  ·
    refine ⟨11101281348195625877861821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59206833857043338015263045 11101281348195625877861821)
    ·
      refine ⟨4162980505573359704198183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11101281348195625877861821 4162980505573359704198183)
      ·
        refine ⟨6244470758360039556297275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4162980505573359704198183 6244470758360039556297275)
        ·
          refine ⟨9366706137540059334445913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6244470758360039556297275 9366706137540059334445913)
          ·
            refine ⟨7025029603155044500834435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9366706137540059334445913 7025029603155044500834435)
            ·
              refine ⟨10537544404732566751251653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7025029603155044500834435 10537544404732566751251653)
              ·
                refine ⟨1975789575887356265859685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10537544404732566751251653 1975789575887356265859685)
                ·
                  refine ⟨370460545478879299848691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1975789575887356265859685 370460545478879299848691)
                  ·
                    rfl

theorem cell22_3246612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_3246612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246612 prefixEnd_3246612 := by exact prefixLift 3246612
  have htrace : WordTrace (prefixWord ++ tailWord_3246612) baseStart_3246612 baseEnd_3246612 := by
    simpa [prefixWord, tailWord_3246612, baseEnd_3246612] using wordTrace_append hprefix tailTrace_3246612
  have hstable : (prefixWord ++ tailWord_3246612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246612).length < 2 ^ (prefixWord ++ tailWord_3246612).sum := by decide
  have hdescent : baseEnd_3246612 < baseStart_3246612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246706 : List Nat := [3, 2, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_3246706 : Nat := 118140960795 + 3246706 * 2 ^ 59
def prefixEnd_3246706 : Nat := 4983230072969 + 3 ^ 40 * 3246706 * 2
def baseEnd_3246706 : Nat := 1111413814557652987695785

theorem tailTrace_3246706 : CollatzResearch.WordTrace tailWord_3246706 prefixEnd_3246706 1111413814557652987695785 := by
  unfold tailWord_3246706
  simp only [CollatzResearch.WordTrace]
  refine ⟨29604274043936532521111993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78944730783830753389631981 29604274043936532521111993)
  ·
    refine ⟨22203205532952399390833995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29604274043936532521111993 22203205532952399390833995)
    ·
      refine ⟨33304808299428599086250993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22203205532952399390833995 33304808299428599086250993)
      ·
        refine ⟨24978606224571449314688245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33304808299428599086250993 24978606224571449314688245)
        ·
          refine ⟨2341744333553573373252023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24978606224571449314688245 2341744333553573373252023)
          ·
            refine ⟨3512616500330360059878035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341744333553573373252023 3512616500330360059878035)
            ·
              refine ⟨5268924750495540089817053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512616500330360059878035 5268924750495540089817053)
              ·
                refine ⟨1975846781435827533681395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5268924750495540089817053 1975846781435827533681395)
                ·
                  refine ⟨2963770172153741300522093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975846781435827533681395 2963770172153741300522093)
                  ·
                    refine ⟨1111413814557652987695785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2963770172153741300522093 1111413814557652987695785)
                    ·
                      rfl

theorem cell22_3246706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_3246706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246706 prefixEnd_3246706 := by exact prefixLift 3246706
  have htrace : WordTrace (prefixWord ++ tailWord_3246706) baseStart_3246706 baseEnd_3246706 := by
    simpa [prefixWord, tailWord_3246706, baseEnd_3246706] using wordTrace_append hprefix tailTrace_3246706
  have hstable : (prefixWord ++ tailWord_3246706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246706).length < 2 ^ (prefixWord ++ tailWord_3246706).sum := by decide
  have hdescent : baseEnd_3246706 < baseStart_3246706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246743 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 4, 4]
def baseStart_3246743 : Nat := 118140960795 + 3246743 * 2 ^ 59
def prefixEnd_3246743 : Nat := 4983230072969 + 3 ^ 40 * 3246743 * 2
def baseEnd_3246743 : Nat := 1111426480413797224520671

theorem tailTrace_3246743 : CollatzResearch.WordTrace tailWord_3246743 prefixEnd_3246743 1111426480413797224520671 := by
  unfold tailWord_3246743
  simp only [CollatzResearch.WordTrace]
  refine ⟨118418445676612085403544883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78945630451074723602363255 118418445676612085403544883)
  ·
    refine ⟨177627668514918128105317325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118418445676612085403544883 177627668514918128105317325)
    ·
      refine ⟨66610375693094298039493997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177627668514918128105317325 66610375693094298039493997)
      ·
        refine ⟨24978890884910361764810249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66610375693094298039493997 24978890884910361764810249)
        ·
          refine ⟨18734168163682771323607687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24978890884910361764810249 18734168163682771323607687)
          ·
            refine ⟨28101252245524156985411531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18734168163682771323607687 28101252245524156985411531)
            ·
              refine ⟨42151878368286235478117297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28101252245524156985411531 42151878368286235478117297)
              ·
                refine ⟨31613908776214676608587973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42151878368286235478117297 31613908776214676608587973)
                ·
                  refine ⟨5927607895540251864110245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31613908776214676608587973 5927607895540251864110245)
                  ·
                    refine ⟨1111426480413797224520671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5927607895540251864110245 1111426480413797224520671)
                    ·
                      rfl

theorem cell22_3246743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_3246743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246743 prefixEnd_3246743 := by exact prefixLift 3246743
  have htrace : WordTrace (prefixWord ++ tailWord_3246743) baseStart_3246743 baseEnd_3246743 := by
    simpa [prefixWord, tailWord_3246743, baseEnd_3246743] using wordTrace_append hprefix tailTrace_3246743
  have hstable : (prefixWord ++ tailWord_3246743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246743).length < 2 ^ (prefixWord ++ tailWord_3246743).sum := by decide
  have hdescent : baseEnd_3246743 < baseStart_3246743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246745 : List Nat := [1, 2, 1, 2, 1, 2, 5, 3, 2, 3]
def baseStart_3246745 : Nat := 118140960795 + 3246745 * 2 ^ 59
def prefixEnd_3246745 : Nat := 4983230072969 + 3 ^ 40 * 3246745 * 2
def baseEnd_3246745 : Nat := 1111427165054669885970665

theorem tailTrace_3246745 : CollatzResearch.WordTrace tailWord_3246745 prefixEnd_3246745 1111427165054669885970665 := by
  unfold tailWord_3246745
  simp only [CollatzResearch.WordTrace]
  refine ⟨118418518622604839745117689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78945679081736559830078459 118418518622604839745117689)
  ·
    refine ⟨88813888966953629808838267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118418518622604839745117689 88813888966953629808838267)
    ·
      refine ⟨133220833450430444713257401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88813888966953629808838267 133220833450430444713257401)
      ·
        refine ⟨99915625087822833534943051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133220833450430444713257401 99915625087822833534943051)
        ·
          refine ⟨149873437631734250302414577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99915625087822833534943051 149873437631734250302414577)
          ·
            refine ⟨112405078223800687726810933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149873437631734250302414577 112405078223800687726810933)
            ·
              refine ⟨10537976083481314474388525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112405078223800687726810933 10537976083481314474388525)
              ·
                refine ⟨3951741031305492927895697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10537976083481314474388525 3951741031305492927895697)
                ·
                  refine ⟨2963805773479119695921773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3951741031305492927895697 2963805773479119695921773)
                  ·
                    refine ⟨1111427165054669885970665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2963805773479119695921773 1111427165054669885970665)
                    ·
                      rfl

theorem cell22_3246745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 3].length) (baseStart_3246745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246745 prefixEnd_3246745 := by exact prefixLift 3246745
  have htrace : WordTrace (prefixWord ++ tailWord_3246745) baseStart_3246745 baseEnd_3246745 := by
    simpa [prefixWord, tailWord_3246745, baseEnd_3246745] using wordTrace_append hprefix tailTrace_3246745
  have hstable : (prefixWord ++ tailWord_3246745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246745).length < 2 ^ (prefixWord ++ tailWord_3246745).sum := by decide
  have hdescent : baseEnd_3246745 < baseStart_3246745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246897 : List Nat := [1, 2, 2, 3, 2, 1, 2, 4, 2, 3]
def baseStart_3246897 : Nat := 118140960795 + 3246897 * 2 ^ 59
def prefixEnd_3246897 : Nat := 4983230072969 + 3 ^ 40 * 3246897 * 2
def baseEnd_3246897 : Nat := 1111479197760992156170199

theorem tailTrace_3246897 : CollatzResearch.WordTrace tailWord_3246897 prefixEnd_3246897 1111479197760992156170199 := by
  unfold tailWord_3246897
  simp only [CollatzResearch.WordTrace]
  refine ⟨118424062518054169704650945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78949375012036113136433963 118424062518054169704650945)
  ·
    refine ⟨88818046888540627278488209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118424062518054169704650945 88818046888540627278488209)
    ·
      refine ⟨66613535166405470458866157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88818046888540627278488209 66613535166405470458866157)
      ·
        refine ⟨24980075687402051422074809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66613535166405470458866157 24980075687402051422074809)
        ·
          refine ⟨18735056765551538566556107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24980075687402051422074809 18735056765551538566556107)
          ·
            refine ⟨28102585148327307849834161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18735056765551538566556107 28102585148327307849834161)
            ·
              refine ⟨21076938861245480887375621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28102585148327307849834161 21076938861245480887375621)
              ·
                refine ⟨3951926036483527666382929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21076938861245480887375621 3951926036483527666382929)
                ·
                  refine ⟨2963944527362645749787197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3951926036483527666382929 2963944527362645749787197)
                  ·
                    refine ⟨1111479197760992156170199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2963944527362645749787197 1111479197760992156170199)
                    ·
                      rfl

theorem cell22_3246897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_3246897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246897 prefixEnd_3246897 := by exact prefixLift 3246897
  have htrace : WordTrace (prefixWord ++ tailWord_3246897) baseStart_3246897 baseEnd_3246897 := by
    simpa [prefixWord, tailWord_3246897, baseEnd_3246897] using wordTrace_append hprefix tailTrace_3246897
  have hstable : (prefixWord ++ tailWord_3246897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246897).length < 2 ^ (prefixWord ++ tailWord_3246897).sum := by decide
  have hdescent : baseEnd_3246897 < baseStart_3246897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246899 : List Nat := [1, 1, 1, 2, 6, 2, 3, 2, 4]
def baseStart_3246899 : Nat := 118140960795 + 3246899 * 2 ^ 59
def prefixEnd_3246899 : Nat := 4983230072969 + 3 ^ 40 * 3246899 * 2
def baseEnd_3246899 : Nat := 370493294133954939206731

theorem tailTrace_3246899 : CollatzResearch.WordTrace tailWord_3246899 prefixEnd_3246899 370493294133954939206731 := by
  unfold tailWord_3246899
  simp only [CollatzResearch.WordTrace]
  refine ⟨118424135464046924046223751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78949423642697949364149167 118424135464046924046223751)
  ·
    refine ⟨177636203196070386069335627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118424135464046924046223751 177636203196070386069335627)
    ·
      refine ⟨266454304794105579104003441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177636203196070386069335627 266454304794105579104003441)
      ·
        refine ⟨199840728595579184328002581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266454304794105579104003441 199840728595579184328002581)
        ·
          refine ⟨9367534152917774265375121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 199840728595579184328002581 9367534152917774265375121)
          ·
            refine ⟨7025650614688330699031341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9367534152917774265375121 7025650614688330699031341)
            ·
              refine ⟨2634618980508124012136753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7025650614688330699031341 2634618980508124012136753)
              ·
                refine ⟨1975964235381093009102565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2634618980508124012136753 1975964235381093009102565)
                ·
                  refine ⟨370493294133954939206731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1975964235381093009102565 370493294133954939206731)
                  ·
                    rfl

theorem cell22_3246899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 4].length) (baseStart_3246899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246899 prefixEnd_3246899 := by exact prefixLift 3246899
  have htrace : WordTrace (prefixWord ++ tailWord_3246899) baseStart_3246899 baseEnd_3246899 := by
    simpa [prefixWord, tailWord_3246899, baseEnd_3246899] using wordTrace_append hprefix tailTrace_3246899
  have hstable : (prefixWord ++ tailWord_3246899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246899).length < 2 ^ (prefixWord ++ tailWord_3246899).sum := by decide
  have hdescent : baseEnd_3246899 < baseStart_3246899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246918 : List Nat := [6, 1, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_3246918 : Nat := 118140960795 + 3246918 * 2 ^ 59
def prefixEnd_3246918 : Nat := 4983230072969 + 3 ^ 40 * 3246918 * 2
def baseEnd_3246918 : Nat := 1111486386490155101395135

theorem tailTrace_3246918 : CollatzResearch.WordTrace tailWord_3246918 prefixEnd_3246918 1111486386490155101395135 := by
  unfold tailWord_3246918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3700775889093065321598919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78949885633985393527443605 3700775889093065321598919)
  ·
    refine ⟨5551163833639597982398379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3700775889093065321598919 5551163833639597982398379)
    ·
      refine ⟨8326745750459396973597569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5551163833639597982398379 8326745750459396973597569)
      ·
        refine ⟨6245059312844547730198177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8326745750459396973597569 6245059312844547730198177)
        ·
          refine ⟨4683794484633410797648633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6245059312844547730198177 4683794484633410797648633)
          ·
            refine ⟨3512845863475058098236475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4683794484633410797648633 3512845863475058098236475)
            ·
              refine ⟨5269268795212587147354713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512845863475058098236475 5269268795212587147354713)
              ·
                refine ⟨3951951596409440360516035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5269268795212587147354713 3951951596409440360516035)
                ·
                  refine ⟨5927927394614160540774053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3951951596409440360516035 5927927394614160540774053)
                  ·
                    refine ⟨1111486386490155101395135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5927927394614160540774053 1111486386490155101395135)
                    ·
                      rfl

theorem cell22_3246918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_3246918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246918 prefixEnd_3246918 := by exact prefixLift 3246918
  have htrace : WordTrace (prefixWord ++ tailWord_3246918) baseStart_3246918 baseEnd_3246918 := by
    simpa [prefixWord, tailWord_3246918, baseEnd_3246918] using wordTrace_append hprefix tailTrace_3246918
  have hstable : (prefixWord ++ tailWord_3246918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246918).length < 2 ^ (prefixWord ++ tailWord_3246918).sum := by decide
  have hdescent : baseEnd_3246918 < baseStart_3246918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246955 : List Nat := [1, 1, 1, 1, 2, 2, 5, 4, 5]
def baseStart_3246955 : Nat := 118140960795 + 3246955 * 2 ^ 59
def prefixEnd_3246955 : Nat := 4983230072969 + 3 ^ 40 * 3246955 * 2
def baseEnd_3246955 : Nat := 370499684115433112740007

theorem tailTrace_3246955 : CollatzResearch.WordTrace tailWord_3246955 prefixEnd_3246955 370499684115433112740007 := by
  unfold tailWord_3246955
  simp only [CollatzResearch.WordTrace]
  refine ⟨118426177951844045610262319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78950785301229363740174879 118426177951844045610262319)
  ·
    refine ⟨177639266927766068415393479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118426177951844045610262319 177639266927766068415393479)
    ·
      refine ⟨266458900391649102623090219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177639266927766068415393479 266458900391649102623090219)
      ·
        refine ⟨399688350587473653934635329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266458900391649102623090219 399688350587473653934635329)
        ·
          refine ⟨299766262940605240450976497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399688350587473653934635329 299766262940605240450976497)
          ·
            refine ⟨224824697205453930338232373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299766262940605240450976497 224824697205453930338232373)
            ·
              refine ⟨21077315363011305969209285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224824697205453930338232373 21077315363011305969209285)
              ·
                refine ⟨3951996630564619869226741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21077315363011305969209285 3951996630564619869226741)
                ·
                  refine ⟨370499684115433112740007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3951996630564619869226741 370499684115433112740007)
                  ·
                    rfl

theorem cell22_3246955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 5].length) (baseStart_3246955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246955 prefixEnd_3246955 := by exact prefixLift 3246955
  have htrace : WordTrace (prefixWord ++ tailWord_3246955) baseStart_3246955 baseEnd_3246955 := by
    simpa [prefixWord, tailWord_3246955, baseEnd_3246955] using wordTrace_append hprefix tailTrace_3246955
  have hstable : (prefixWord ++ tailWord_3246955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246955).length < 2 ^ (prefixWord ++ tailWord_3246955).sum := by decide
  have hdescent : baseEnd_3246955 < baseStart_3246955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247017 : List Nat := [1, 2, 1, 1, 1, 1, 5, 6, 4]
def baseStart_3247017 : Nat := 118140960795 + 3247017 * 2 ^ 59
def prefixEnd_3247017 : Nat := 4983230072969 + 3 ^ 40 * 3247017 * 2
def baseEnd_3247017 : Nat := 370506758737783947723277

theorem tailTrace_3247017 : CollatzResearch.WordTrace tailWord_3247017 prefixEnd_3247017 370506758737783947723277 := by
  unfold tailWord_3247017
  simp only [CollatzResearch.WordTrace]
  refine ⟨118428439277619430199019305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78952292851746286799346203 118428439277619430199019305)
  ·
    refine ⟨88821329458214572649264479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118428439277619430199019305 88821329458214572649264479)
    ·
      refine ⟨133231994187321858973896719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88821329458214572649264479 133231994187321858973896719)
      ·
        refine ⟨199847991280982788460845079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133231994187321858973896719 199847991280982788460845079)
        ·
          refine ⟨299771986921474182691267619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199847991280982788460845079 299771986921474182691267619)
          ·
            refine ⟨449657980382211274036901429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299771986921474182691267619 449657980382211274036901429)
            ·
              refine ⟨42155435660832306940959509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 449657980382211274036901429 42155435660832306940959509)
              ·
                refine ⟨1976036046601514387857477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42155435660832306940959509 1976036046601514387857477)
                ·
                  refine ⟨370506758737783947723277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1976036046601514387857477 370506758737783947723277)
                  ·
                    rfl

theorem cell22_3247017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 4].length) (baseStart_3247017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247017 prefixEnd_3247017 := by exact prefixLift 3247017
  have htrace : WordTrace (prefixWord ++ tailWord_3247017) baseStart_3247017 baseEnd_3247017 := by
    simpa [prefixWord, tailWord_3247017, baseEnd_3247017] using wordTrace_append hprefix tailTrace_3247017
  have hstable : (prefixWord ++ tailWord_3247017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247017).length < 2 ^ (prefixWord ++ tailWord_3247017).sum := by decide
  have hdescent : baseEnd_3247017 < baseStart_3247017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247032 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 1, 5]
def baseStart_3247032 : Nat := 118140960795 + 3247032 * 2 ^ 59
def prefixEnd_3247032 : Nat := 4983230072969 + 3 ^ 40 * 3247032 * 2
def baseEnd_3247032 : Nat := 1111525411019896804044785

theorem tailTrace_3247032 : CollatzResearch.WordTrace tailWord_3247032 prefixEnd_3247032 1111525411019896804044785 := by
  unfold tailWord_3247032
  simp only [CollatzResearch.WordTrace]
  refine ⟨59214493186282543880407675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78952657581710058507210233 59214493186282543880407675)
  ·
    refine ⟨88821739779423815820611513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59214493186282543880407675 88821739779423815820611513)
    ·
      refine ⟨66616304834567861865458635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88821739779423815820611513 66616304834567861865458635)
      ·
        refine ⟨99924457251851792798187953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66616304834567861865458635 99924457251851792798187953)
        ·
          refine ⟨74943342938888844598640965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99924457251851792798187953 74943342938888844598640965)
          ·
            refine ⟨14051876801041658362245181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74943342938888844598640965 14051876801041658362245181)
            ·
              refine ⟨5269453800390621885841943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14051876801041658362245181 5269453800390621885841943)
              ·
                refine ⟨7904180700585932828762915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5269453800390621885841943 7904180700585932828762915)
                ·
                  refine ⟨11856271050878899243144373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7904180700585932828762915 11856271050878899243144373)
                  ·
                    refine ⟨1111525411019896804044785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11856271050878899243144373 1111525411019896804044785)
                    ·
                      rfl

theorem cell22_3247032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_3247032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247032 prefixEnd_3247032 := by exact prefixLift 3247032
  have htrace : WordTrace (prefixWord ++ tailWord_3247032) baseStart_3247032 baseEnd_3247032 := by
    simpa [prefixWord, tailWord_3247032, baseEnd_3247032] using wordTrace_append hprefix tailTrace_3247032
  have hstable : (prefixWord ++ tailWord_3247032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247032).length < 2 ^ (prefixWord ++ tailWord_3247032).sum := by decide
  have hdescent : baseEnd_3247032 < baseStart_3247032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247111 : List Nat := [1, 1, 4, 3, 1, 1, 2, 5, 1, 3]
def baseStart_3247111 : Nat := 118140960795 + 3247111 * 2 ^ 59
def prefixEnd_3247111 : Nat := 4983230072969 + 3 ^ 40 * 3247111 * 2
def baseEnd_3247111 : Nat := 1111552454334366931319543

theorem tailTrace_3247111 : CollatzResearch.WordTrace tailWord_3247111 prefixEnd_3247111 1111552454334366931319543 := by
  unfold tailWord_3247111
  simp only [CollatzResearch.WordTrace]
  refine ⟨118431867739278884252941187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78954578492852589501960791 118431867739278884252941187)
  ·
    refine ⟨177647801608918326379411781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118431867739278884252941187 177647801608918326379411781)
    ·
      refine ⟨33308962801672186196139709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177647801608918326379411781 33308962801672186196139709)
      ·
        refine ⟨12490861050627069823552391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33308962801672186196139709 12490861050627069823552391)
        ·
          refine ⟨18736291575940604735328587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12490861050627069823552391 18736291575940604735328587)
          ·
            refine ⟨28104437363910907102992881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18736291575940604735328587 28104437363910907102992881)
            ·
              refine ⟨21078328022933180327244661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28104437363910907102992881 21078328022933180327244661)
              ·
                refine ⟨1976093252149985655679187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21078328022933180327244661 1976093252149985655679187)
                ·
                  refine ⟨2964139878224978483518781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976093252149985655679187 2964139878224978483518781)
                  ·
                    refine ⟨1111552454334366931319543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2964139878224978483518781 1111552454334366931319543)
                    ·
                      rfl

theorem cell22_3247111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_3247111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247111 prefixEnd_3247111 := by exact prefixLift 3247111
  have htrace : WordTrace (prefixWord ++ tailWord_3247111) baseStart_3247111 baseEnd_3247111 := by
    simpa [prefixWord, tailWord_3247111, baseEnd_3247111] using wordTrace_append hprefix tailTrace_3247111
  have hstable : (prefixWord ++ tailWord_3247111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247111).length < 2 ^ (prefixWord ++ tailWord_3247111).sum := by decide
  have hdescent : baseEnd_3247111 < baseStart_3247111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247128 : List Nat := [2, 1, 2, 3, 2, 2, 4, 2, 1, 3]
def baseStart_3247128 : Nat := 118140960795 + 3247128 * 2 ^ 59
def prefixEnd_3247128 : Nat := 4983230072969 + 3 ^ 40 * 3247128 * 2
def baseEnd_3247128 : Nat := 1111558273781784553644491

theorem tailTrace_3247128 : CollatzResearch.WordTrace tailWord_3247128 prefixEnd_3247128 1111558273781784553644491 := by
  unfold tailWord_3247128
  simp only [CollatzResearch.WordTrace]
  refine ⟨59216243890108648078155019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78954991853478197437540025 59216243890108648078155019)
  ·
    refine ⟨88824365835162972117232529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59216243890108648078155019 88824365835162972117232529)
    ·
      refine ⟨66618274376372229087924397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88824365835162972117232529 66618274376372229087924397)
      ·
        refine ⟨24981852891139585907971649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66618274376372229087924397 24981852891139585907971649)
        ·
          refine ⟨18736389668354689430978737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24981852891139585907971649 18736389668354689430978737)
          ·
            refine ⟨14052292251266017073234053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18736389668354689430978737 14052292251266017073234053)
            ·
              refine ⟨2634804797112378201231385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14052292251266017073234053 2634804797112378201231385)
              ·
                refine ⟨1976103597834283650923539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2634804797112378201231385 1976103597834283650923539)
                ·
                  refine ⟨2964155396751425476385309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976103597834283650923539 2964155396751425476385309)
                  ·
                    refine ⟨1111558273781784553644491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2964155396751425476385309 1111558273781784553644491)
                    ·
                      rfl

theorem cell22_3247128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_3247128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247128 prefixEnd_3247128 := by exact prefixLift 3247128
  have htrace : WordTrace (prefixWord ++ tailWord_3247128) baseStart_3247128 baseEnd_3247128 := by
    simpa [prefixWord, tailWord_3247128, baseEnd_3247128] using wordTrace_append hprefix tailTrace_3247128
  have hstable : (prefixWord ++ tailWord_3247128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247128).length < 2 ^ (prefixWord ++ tailWord_3247128).sum := by decide
  have hdescent : baseEnd_3247128 < baseStart_3247128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247152 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 6]
def baseStart_3247152 : Nat := 118140960795 + 3247152 * 2 ^ 59
def prefixEnd_3247152 : Nat := 4983230072969 + 3 ^ 40 * 3247152 * 2
def baseEnd_3247152 : Nat := 370522163157418830348139

theorem tailTrace_3247152 : CollatzResearch.WordTrace tailWord_3247152 prefixEnd_3247152 370522163157418830348139 := by
  unfold tailWord_3247152
  simp only [CollatzResearch.WordTrace]
  refine ⟨59216681566065174127591855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78955575421420232170122473 59216681566065174127591855)
  ·
    refine ⟨88825022349097761191387783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59216681566065174127591855 88825022349097761191387783)
    ·
      refine ⟨133237533523646641787081675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88825022349097761191387783 133237533523646641787081675)
      ·
        refine ⟨199856300285469962680622513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133237533523646641787081675 199856300285469962680622513)
        ·
          refine ⟨149892225214102472010466885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199856300285469962680622513 149892225214102472010466885)
          ·
            refine ⟨28104792227644213501962541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149892225214102472010466885 28104792227644213501962541)
            ·
              refine ⟨10539297085366580063235953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28104792227644213501962541 10539297085366580063235953)
              ·
                refine ⟨7904472814024935047426965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10539297085366580063235953 7904472814024935047426965)
                ·
                  refine ⟨370522163157418830348139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7904472814024935047426965 370522163157418830348139)
                  ·
                    rfl

theorem cell22_3247152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_3247152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247152 prefixEnd_3247152 := by exact prefixLift 3247152
  have htrace : WordTrace (prefixWord ++ tailWord_3247152) baseStart_3247152 baseEnd_3247152 := by
    simpa [prefixWord, tailWord_3247152, baseEnd_3247152] using wordTrace_append hprefix tailTrace_3247152
  have hstable : (prefixWord ++ tailWord_3247152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247152).length < 2 ^ (prefixWord ++ tailWord_3247152).sum := by decide
  have hdescent : baseEnd_3247152 < baseStart_3247152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247154 : List Nat := [3, 2, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_3247154 : Nat := 118140960795 + 3247154 * 2 ^ 59
def prefixEnd_3247154 : Nat := 4983230072969 + 3 ^ 40 * 3247154 * 2
def baseEnd_3247154 : Nat := 1111567174113129152494411

theorem tailTrace_3247154 : CollatzResearch.WordTrace tailWord_3247154 prefixEnd_3247154 1111567174113129152494411 := by
  unfold tailWord_3247154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29608359019530775649189129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78955624052082068397837677 29608359019530775649189129)
  ·
    refine ⟨22206269264648081736891847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29608359019530775649189129 22206269264648081736891847)
    ·
      refine ⟨33309403896972122605337771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22206269264648081736891847 33309403896972122605337771)
      ·
        refine ⟨49964105845458183908006657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33309403896972122605337771 49964105845458183908006657)
        ·
          refine ⟨37473079384093637931004993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49964105845458183908006657 37473079384093637931004993)
          ·
            refine ⟨28104809538070228448253745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37473079384093637931004993 28104809538070228448253745)
            ·
              refine ⟨21078607153552671336190309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28104809538070228448253745 21078607153552671336190309)
              ·
                refine ⟨3952238841291125875535683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21078607153552671336190309 3952238841291125875535683)
                ·
                  refine ⟨5928358261936688813303525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3952238841291125875535683 5928358261936688813303525)
                  ·
                    refine ⟨1111567174113129152494411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5928358261936688813303525 1111567174113129152494411)
                    ·
                      rfl

theorem cell22_3247154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_3247154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247154 prefixEnd_3247154 := by exact prefixLift 3247154
  have htrace : WordTrace (prefixWord ++ tailWord_3247154) baseStart_3247154 baseEnd_3247154 := by
    simpa [prefixWord, tailWord_3247154, baseEnd_3247154] using wordTrace_append hprefix tailTrace_3247154
  have hstable : (prefixWord ++ tailWord_3247154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247154).length < 2 ^ (prefixWord ++ tailWord_3247154).sum := by decide
  have hdescent : baseEnd_3247154 < baseStart_3247154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247186 : List Nat := [3, 2, 2, 1, 3, 1, 2, 4, 4]
def baseStart_3247186 : Nat := 118140960795 + 3247186 * 2 ^ 59
def prefixEnd_3247186 : Nat := 4983230072969 + 3 ^ 40 * 3247186 * 2
def baseEnd_3247186 : Nat := 370526042789030578564771

theorem tailTrace_3247186 : CollatzResearch.WordTrace tailWord_3247186 prefixEnd_3247186 370526042789030578564771 := by
  unfold tailWord_3247186
  simp only [CollatzResearch.WordTrace]
  refine ⟨29608650803501793015480353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78956402142671448041280941 29608650803501793015480353)
  ·
    refine ⟨22206488102626344761610265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29608650803501793015480353 22206488102626344761610265)
    ·
      refine ⟨16654866076969758571207699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22206488102626344761610265 16654866076969758571207699)
      ·
        refine ⟨24982299115454637856811549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16654866076969758571207699 24982299115454637856811549)
        ·
          refine ⟨9368362168295489196304331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24982299115454637856811549 9368362168295489196304331)
          ·
            refine ⟨14052543252443233794456497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9368362168295489196304331 14052543252443233794456497)
            ·
              refine ⟨10539407439332425345842373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14052543252443233794456497 10539407439332425345842373)
              ·
                refine ⟨1976138894874829752345445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10539407439332425345842373 1976138894874829752345445)
                ·
                  refine ⟨370526042789030578564771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1976138894874829752345445 370526042789030578564771)
                  ·
                    rfl

theorem cell22_3247186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_3247186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247186 prefixEnd_3247186 := by exact prefixLift 3247186
  have htrace : WordTrace (prefixWord ++ tailWord_3247186) baseStart_3247186 baseEnd_3247186 := by
    simpa [prefixWord, tailWord_3247186, baseEnd_3247186] using wordTrace_append hprefix tailTrace_3247186
  have hstable : (prefixWord ++ tailWord_3247186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247186).length < 2 ^ (prefixWord ++ tailWord_3247186).sum := by decide
  have hdescent : baseEnd_3247186 < baseStart_3247186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247212 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_3247212 : Nat := 118140960795 + 3247212 * 2 ^ 59
def prefixEnd_3247212 : Nat := 4983230072969 + 3 ^ 40 * 3247212 * 2
def baseEnd_3247212 : Nat := 1111587028698436334544233

theorem tailTrace_3247212 : CollatzResearch.WordTrace tailWord_3247212 prefixEnd_3247212 1111587028698436334544233 := by
  unfold tailWord_3247212
  simp only [CollatzResearch.WordTrace]
  refine ⟨59217775755956489251183945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78957034341275319001578593 59217775755956489251183945)
  ·
    refine ⟨44413331816967366938387959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59217775755956489251183945 44413331816967366938387959)
    ·
      refine ⟨66619997725451050407581939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44413331816967366938387959 66619997725451050407581939)
      ·
        refine ⟨99929996588176575611372909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66619997725451050407581939 99929996588176575611372909)
        ·
          refine ⟨37473748720566215854264841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99929996588176575611372909 37473748720566215854264841)
          ·
            refine ⟨28105311540424661890698631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37473748720566215854264841 28105311540424661890698631)
            ·
              refine ⟨42157967310636992836047947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28105311540424661890698631 42157967310636992836047947)
              ·
                refine ⟨63236950965955489254071921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42157967310636992836047947 63236950965955489254071921)
                ·
                  refine ⟨47427713224466616940553941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63236950965955489254071921 47427713224466616940553941)
                  ·
                    refine ⟨1111587028698436334544233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47427713224466616940553941 1111587028698436334544233)
                    ·
                      rfl

theorem cell22_3247212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_3247212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247212 prefixEnd_3247212 := by exact prefixLift 3247212
  have htrace : WordTrace (prefixWord ++ tailWord_3247212) baseStart_3247212 baseEnd_3247212 := by
    simpa [prefixWord, tailWord_3247212, baseEnd_3247212] using wordTrace_append hprefix tailTrace_3247212
  have hstable : (prefixWord ++ tailWord_3247212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247212).length < 2 ^ (prefixWord ++ tailWord_3247212).sum := by decide
  have hdescent : baseEnd_3247212 < baseStart_3247212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247214 : List Nat := [4, 1, 2, 2, 1, 3, 1, 8]
def baseStart_3247214 : Nat := 118140960795 + 3247214 * 2 ^ 59
def prefixEnd_3247214 : Nat := 4983230072969 + 3 ^ 40 * 3247214 * 2
def baseEnd_3247214 : Nat := 123509745926589888443803

theorem tailTrace_3247214 : CollatzResearch.WordTrace tailWord_3247214 prefixEnd_3247214 123509745926589888443803 := by
  unfold tailWord_3247214
  simp only [CollatzResearch.WordTrace]
  refine ⟨14804453057238216605492587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78957082971937155229293797 14804453057238216605492587)
  ·
    refine ⟨22206679585857324908238881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14804453057238216605492587 22206679585857324908238881)
    ·
      refine ⟨16655009689392993681179161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22206679585857324908238881 16655009689392993681179161)
      ·
        refine ⟨12491257267044745260884371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16655009689392993681179161 12491257267044745260884371)
        ·
          refine ⟨18736885900567117891326557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12491257267044745260884371 18736885900567117891326557)
          ·
            refine ⟨7026332212712669209247459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18736885900567117891326557 7026332212712669209247459)
            ·
              refine ⟨10539498319069003813871189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7026332212712669209247459 10539498319069003813871189)
              ·
                refine ⟨123509745926589888443803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10539498319069003813871189 123509745926589888443803)
                ·
                  rfl

theorem cell22_3247214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_3247214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247214 prefixEnd_3247214 := by exact prefixLift 3247214
  have htrace : WordTrace (prefixWord ++ tailWord_3247214) baseStart_3247214 baseEnd_3247214 := by
    simpa [prefixWord, tailWord_3247214, baseEnd_3247214] using wordTrace_append hprefix tailTrace_3247214
  have hstable : (prefixWord ++ tailWord_3247214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247214).length < 2 ^ (prefixWord ++ tailWord_3247214).sum := by decide
  have hdescent : baseEnd_3247214 < baseStart_3247214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247297 : List Nat := [1, 2, 6, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3247297 : Nat := 118140960795 + 3247297 * 2 ^ 59
def prefixEnd_3247297 : Nat := 4983230072969 + 3 ^ 40 * 3247297 * 2
def baseEnd_3247297 : Nat := 1111616125935524446168973

theorem tailTrace_3247297 : CollatzResearch.WordTrace tailWord_3247297 prefixEnd_3247297 1111616125935524446168973 := by
  unfold tailWord_3247297
  simp only [CollatzResearch.WordTrace]
  refine ⟨118438651716605038019212145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78959101144403358679474763 118438651716605038019212145)
  ·
    refine ⟨88828988787453778514409109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118438651716605038019212145 88828988787453778514409109)
    ·
      refine ⟨4163858849411895867862927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88828988787453778514409109 4163858849411895867862927)
      ·
        refine ⟨6245788274117843801794391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4163858849411895867862927 6245788274117843801794391)
        ·
          refine ⟨9368682411176765702691587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6245788274117843801794391 9368682411176765702691587)
          ·
            refine ⟨14053023616765148554037381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9368682411176765702691587 14053023616765148554037381)
            ·
              refine ⟨2634941928143465353882009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14053023616765148554037381 2634941928143465353882009)
              ·
                refine ⟨1976206446107599015411507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2634941928143465353882009 1976206446107599015411507)
                ·
                  refine ⟨2964309669161398523117261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976206446107599015411507 2964309669161398523117261)
                  ·
                    refine ⟨1111616125935524446168973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2964309669161398523117261 1111616125935524446168973)
                    ·
                      rfl

theorem cell22_3247297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3247297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247297 prefixEnd_3247297 := by exact prefixLift 3247297
  have htrace : WordTrace (prefixWord ++ tailWord_3247297) baseStart_3247297 baseEnd_3247297 := by
    simpa [prefixWord, tailWord_3247297, baseEnd_3247297] using wordTrace_append hprefix tailTrace_3247297
  have hstable : (prefixWord ++ tailWord_3247297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247297).length < 2 ^ (prefixWord ++ tailWord_3247297).sum := by decide
  have hdescent : baseEnd_3247297 < baseStart_3247297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247319 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 1, 5]
def baseStart_3247319 : Nat := 118140960795 + 3247319 * 2 ^ 59
def prefixEnd_3247319 : Nat := 4983230072969 + 3 ^ 40 * 3247319 * 2
def baseEnd_3247319 : Nat := 1111623656985123722118905

theorem tailTrace_3247319 : CollatzResearch.WordTrace tailWord_3247319 prefixEnd_3247319 1111623656985123722118905 := by
  unfold tailWord_3247319
  simp only [CollatzResearch.WordTrace]
  refine ⟨118439454122525335776513011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78959636081683557184342007 118439454122525335776513011)
  ·
    refine ⟨177659181183788003664769517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118439454122525335776513011 177659181183788003664769517)
    ·
      refine ⟨66622192943920501374288569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177659181183788003664769517 66622192943920501374288569)
      ·
        refine ⟨49966644707940376030716427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66622192943920501374288569 49966644707940376030716427)
        ·
          refine ⟨74949967061910564046074641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49966644707940376030716427 74949967061910564046074641)
          ·
            refine ⟨56212475296432923034555981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74949967061910564046074641 56212475296432923034555981)
            ·
              refine ⟨21079678236162346137958493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56212475296432923034555981 21079678236162346137958493)
              ·
                refine ⟨7904879338560879801734435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21079678236162346137958493 7904879338560879801734435)
                ·
                  refine ⟨11857319007841319702601653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7904879338560879801734435 11857319007841319702601653)
                  ·
                    refine ⟨1111623656985123722118905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11857319007841319702601653 1111623656985123722118905)
                    ·
                      rfl

theorem cell22_3247319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_3247319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247319 prefixEnd_3247319 := by exact prefixLift 3247319
  have htrace : WordTrace (prefixWord ++ tailWord_3247319) baseStart_3247319 baseEnd_3247319 := by
    simpa [prefixWord, tailWord_3247319, baseEnd_3247319] using wordTrace_append hprefix tailTrace_3247319
  have hstable : (prefixWord ++ tailWord_3247319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247319).length < 2 ^ (prefixWord ++ tailWord_3247319).sum := by decide
  have hdescent : baseEnd_3247319 < baseStart_3247319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247336 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 4, 3]
def baseStart_3247336 : Nat := 118140960795 + 3247336 * 2 ^ 59
def prefixEnd_3247336 : Nat := 4983230072969 + 3 ^ 40 * 3247336 * 2
def baseEnd_3247336 : Nat := 1111629476432541344443853

theorem tailTrace_3247336 : CollatzResearch.WordTrace tailWord_3247336 prefixEnd_3247336 1111629476432541344443853 := by
  unfold tailWord_3247336
  simp only [CollatzResearch.WordTrace]
  refine ⟨59220037081731873839940931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78960049442309165119921241 59220037081731873839940931)
  ·
    refine ⟨88830055622597810759911397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59220037081731873839940931 88830055622597810759911397)
    ·
      refine ⟨16655635429237089517483387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88830055622597810759911397 16655635429237089517483387)
      ·
        refine ⟨24983453143855634276225081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16655635429237089517483387 24983453143855634276225081)
        ·
          refine ⟨18737589857891725707168811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24983453143855634276225081 18737589857891725707168811)
          ·
            refine ⟨28106384786837588560753217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18737589857891725707168811 28106384786837588560753217)
            ·
              refine ⟨21079788590128191420564913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28106384786837588560753217 21079788590128191420564913)
              ·
                refine ⟨15809841442596143565423685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21079788590128191420564913 15809841442596143565423685)
                ·
                  refine ⟨2964345270486776918516941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15809841442596143565423685 2964345270486776918516941)
                  ·
                    refine ⟨1111629476432541344443853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2964345270486776918516941 1111629476432541344443853)
                    ·
                      rfl

theorem cell22_3247336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_3247336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247336 prefixEnd_3247336 := by exact prefixLift 3247336
  have htrace : WordTrace (prefixWord ++ tailWord_3247336) baseStart_3247336 baseEnd_3247336 := by
    simpa [prefixWord, tailWord_3247336, baseEnd_3247336] using wordTrace_append hprefix tailTrace_3247336
  have hstable : (prefixWord ++ tailWord_3247336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247336).length < 2 ^ (prefixWord ++ tailWord_3247336).sum := by decide
  have hdescent : baseEnd_3247336 < baseStart_3247336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247338 : List Nat := [3, 1, 3, 1, 1, 4, 2, 3, 4]
def baseStart_3247338 : Nat := 118140960795 + 3247338 * 2 ^ 59
def prefixEnd_3247338 : Nat := 4983230072969 + 3 ^ 40 * 3247338 * 2
def baseEnd_3247338 : Nat := 370543387024471335297949

theorem tailTrace_3247338 : CollatzResearch.WordTrace tailWord_3247338 prefixEnd_3247338 370543387024471335297949 := by
  unfold tailWord_3247338
  simp only [CollatzResearch.WordTrace]
  refine ⟨29610036777364125505363667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78960098072971001347636445 29610036777364125505363667)
  ·
    refine ⟨44415055166046188258045501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29610036777364125505363667 44415055166046188258045501)
    ·
      refine ⟨16655645687267320596767063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44415055166046188258045501 16655645687267320596767063)
      ·
        refine ⟨24983468530900980895150595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16655645687267320596767063 24983468530900980895150595)
        ·
          refine ⟨37475202796351471342725893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24983468530900980895150595 37475202796351471342725893)
          ·
            refine ⟨7026600524315900876761105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37475202796351471342725893 7026600524315900876761105)
            ·
              refine ⟨5269950393236925657570829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7026600524315900876761105 5269950393236925657570829)
              ·
                refine ⟨1976231397463847121589061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5269950393236925657570829 1976231397463847121589061)
                ·
                  refine ⟨370543387024471335297949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1976231397463847121589061 370543387024471335297949)
                  ·
                    rfl

theorem cell22_3247338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_3247338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247338 prefixEnd_3247338 := by exact prefixLift 3247338
  have htrace : WordTrace (prefixWord ++ tailWord_3247338) baseStart_3247338 baseEnd_3247338 := by
    simpa [prefixWord, tailWord_3247338, baseEnd_3247338] using wordTrace_append hprefix tailTrace_3247338
  have hstable : (prefixWord ++ tailWord_3247338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247338).length < 2 ^ (prefixWord ++ tailWord_3247338).sum := by decide
  have hdescent : baseEnd_3247338 < baseStart_3247338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247441 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 3, 4]
def baseStart_3247441 : Nat := 118140960795 + 3247441 * 2 ^ 59
def prefixEnd_3247441 : Nat := 4983230072969 + 3 ^ 40 * 3247441 * 2
def baseEnd_3247441 : Nat := 1111665420078356070568531

theorem tailTrace_3247441 : CollatzResearch.WordTrace tailWord_3247441 prefixEnd_3247441 1111665420078356070568531 := by
  unfold tailWord_3247441
  simp only [CollatzResearch.WordTrace]
  refine ⟨118443903828083350612454177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78962602552055567074969451 118443903828083350612454177)
  ·
    refine ⟨88832927871062512959340633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118443903828083350612454177 88832927871062512959340633)
    ·
      refine ⟨66624695903296884719505475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88832927871062512959340633 66624695903296884719505475)
      ·
        refine ⟨99937043854945327079258213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66624695903296884719505475 99937043854945327079258213)
        ·
          refine ⟨18738195722802248827360915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99937043854945327079258213 18738195722802248827360915)
          ·
            refine ⟨28107293584203373241041373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18738195722802248827360915 28107293584203373241041373)
            ·
              refine ⟨10540235094076264965390515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28107293584203373241041373 10540235094076264965390515)
              ·
                refine ⟨15810352641114397448085773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10540235094076264965390515 15810352641114397448085773)
                ·
                  refine ⟨5928882240417899043032165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15810352641114397448085773 5928882240417899043032165)
                  ·
                    refine ⟨1111665420078356070568531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5928882240417899043032165 1111665420078356070568531)
                    ·
                      rfl

theorem cell22_3247441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_3247441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247441 prefixEnd_3247441 := by exact prefixLift 3247441
  have htrace : WordTrace (prefixWord ++ tailWord_3247441) baseStart_3247441 baseEnd_3247441 := by
    simpa [prefixWord, tailWord_3247441, baseEnd_3247441] using wordTrace_append hprefix tailTrace_3247441
  have hstable : (prefixWord ++ tailWord_3247441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247441).length < 2 ^ (prefixWord ++ tailWord_3247441).sum := by decide
  have hdescent : baseEnd_3247441 < baseStart_3247441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247466 : List Nat := [3, 1, 3, 3, 3, 1, 2, 2, 1, 3]
def baseStart_3247466 : Nat := 118140960795 + 3247466 * 2 ^ 59
def prefixEnd_3247466 : Nat := 4983230072969 + 3 ^ 40 * 3247466 * 2
def baseEnd_3247466 : Nat := 1111673978089264338693455

theorem tailTrace_3247466 : CollatzResearch.WordTrace tailWord_3247466 prefixEnd_3247466 1111673978089264338693455 := by
  unfold tailWord_3247466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29611203913248194970528563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78963210435328519921409501 29611203913248194970528563)
  ·
    refine ⟨44416805869872292455792845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29611203913248194970528563 44416805869872292455792845)
    ·
      refine ⟨16656302201202109670922317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44416805869872292455792845 16656302201202109670922317)
      ·
        refine ⟨6246113325450791126595869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16656302201202109670922317 6246113325450791126595869)
        ·
          refine ⟨2342292497044046672473451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6246113325450791126595869 2342292497044046672473451)
          ·
            refine ⟨3513438745566070008710177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342292497044046672473451 3513438745566070008710177)
            ·
              refine ⟨2635079059174552506532633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3513438745566070008710177 2635079059174552506532633)
              ·
                refine ⟨1976309294380914379899475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2635079059174552506532633 1976309294380914379899475)
                ·
                  refine ⟨2964463941571371569849213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976309294380914379899475 2964463941571371569849213)
                  ·
                    refine ⟨1111673978089264338693455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2964463941571371569849213 1111673978089264338693455)
                    ·
                      rfl

theorem cell22_3247466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_3247466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247466 prefixEnd_3247466 := by exact prefixLift 3247466
  have htrace : WordTrace (prefixWord ++ tailWord_3247466) baseStart_3247466 baseEnd_3247466 := by
    simpa [prefixWord, tailWord_3247466, baseEnd_3247466] using wordTrace_append hprefix tailTrace_3247466
  have hstable : (prefixWord ++ tailWord_3247466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247466).length < 2 ^ (prefixWord ++ tailWord_3247466).sum := by decide
  have hdescent : baseEnd_3247466 < baseStart_3247466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247490 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 6]
def baseStart_3247490 : Nat := 118140960795 + 3247490 * 2 ^ 59
def prefixEnd_3247490 : Nat := 4983230072969 + 3 ^ 40 * 3247490 * 2
def baseEnd_3247490 : Nat := 370560731259912092031127

theorem tailTrace_3247490 : CollatzResearch.WordTrace tailWord_3247490 prefixEnd_3247490 370560731259912092031127 := by
  unfold tailWord_3247490
  simp only [CollatzResearch.WordTrace]
  refine ⟨29611422751226457995246981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78963794003270554653991949 29611422751226457995246981)
  ·
    refine ⟨5552141765854960874108809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29611422751226457995246981 5552141765854960874108809)
    ·
      refine ⟨4164106324391220655581607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5552141765854960874108809 4164106324391220655581607)
      ·
        refine ⟨6246159486586830983372411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4164106324391220655581607 6246159486586830983372411)
        ·
          refine ⟨9369239229880246475058617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6246159486586830983372411 9369239229880246475058617)
          ·
            refine ⟨7026929422410184856293963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9369239229880246475058617 7026929422410184856293963)
            ·
              refine ⟨10540394133615277284440945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7026929422410184856293963 10540394133615277284440945)
              ·
                refine ⟨7905295600211457963330709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10540394133615277284440945 7905295600211457963330709)
                ·
                  refine ⟨370560731259912092031127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7905295600211457963330709 370560731259912092031127)
                  ·
                    rfl

theorem cell22_3247490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_3247490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247490 prefixEnd_3247490 := by exact prefixLift 3247490
  have htrace : WordTrace (prefixWord ++ tailWord_3247490) baseStart_3247490 baseEnd_3247490 := by
    simpa [prefixWord, tailWord_3247490, baseEnd_3247490] using wordTrace_append hprefix tailTrace_3247490
  have hstable : (prefixWord ++ tailWord_3247490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247490).length < 2 ^ (prefixWord ++ tailWord_3247490).sum := by decide
  have hdescent : baseEnd_3247490 < baseStart_3247490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247522 : List Nat := [3, 3, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_3247522 : Nat := 118140960795 + 3247522 * 2 ^ 59
def prefixEnd_3247522 : Nat := 4983230072969 + 3 ^ 40 * 3247522 * 2
def baseEnd_3247522 : Nat := 1111693148033698859293283

theorem tailTrace_3247522 : CollatzResearch.WordTrace tailWord_3247522 prefixEnd_3247522 1111693148033698859293283 := by
  unfold tailWord_3247522
  simp only [CollatzResearch.WordTrace]
  refine ⟨29611714535197475361538205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78964572093859934297435213 29611714535197475361538205)
  ·
    refine ⟨11104392950699053260576827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29611714535197475361538205 11104392950699053260576827)
    ·
      refine ⟨16656589426048579890865241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11104392950699053260576827 16656589426048579890865241)
      ·
        refine ⟨12492442069536434918148931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16656589426048579890865241 12492442069536434918148931)
        ·
          refine ⟨18738663104304652377223397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12492442069536434918148931 18738663104304652377223397)
          ·
            refine ⟨3513499332057122320729387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18738663104304652377223397 3513499332057122320729387)
            ·
              refine ⟨5270248998085683481094081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3513499332057122320729387 5270248998085683481094081)
              ·
                refine ⟨3952686748564262610820561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5270248998085683481094081 3952686748564262610820561)
                ·
                  refine ⟨2964515061423196958115421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3952686748564262610820561 2964515061423196958115421)
                  ·
                    refine ⟨1111693148033698859293283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2964515061423196958115421 1111693148033698859293283)
                    ·
                      rfl

theorem cell22_3247522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_3247522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247522 prefixEnd_3247522 := by exact prefixLift 3247522
  have htrace : WordTrace (prefixWord ++ tailWord_3247522) baseStart_3247522 baseEnd_3247522 := by
    simpa [prefixWord, tailWord_3247522, baseEnd_3247522] using wordTrace_append hprefix tailTrace_3247522
  have hstable : (prefixWord ++ tailWord_3247522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247522).length < 2 ^ (prefixWord ++ tailWord_3247522).sum := by decide
  have hdescent : baseEnd_3247522 < baseStart_3247522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247623 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 3, 5]
def baseStart_3247623 : Nat := 118140960795 + 3247623 * 2 ^ 59
def prefixEnd_3247623 : Nat := 4983230072969 + 3 ^ 40 * 3247623 * 2
def baseEnd_3247623 : Nat := 1111727722397768262517973

theorem tailTrace_3247623 : CollatzResearch.WordTrace tailWord_3247623 prefixEnd_3247623 1111727722397768262517973 := by
  unfold tailWord_3247623
  simp only [CollatzResearch.WordTrace]
  refine ⟨118450541913423995695579523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78967027942282663797053015 118450541913423995695579523)
  ·
    refine ⟨177675812870135993543369285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118450541913423995695579523 177675812870135993543369285)
    ·
      refine ⟨33314214913150498789381741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177675812870135993543369285 33314214913150498789381741)
      ·
        refine ⟨12492830592431437046018153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33314214913150498789381741 12492830592431437046018153)
        ·
          refine ⟨9369622944323577784513615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12492830592431437046018153 9369622944323577784513615)
          ·
            refine ⟨14054434416485366676770423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9369622944323577784513615 14054434416485366676770423)
            ·
              refine ⟨21081651624728050015155635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14054434416485366676770423 21081651624728050015155635)
              ·
                refine ⟨31622477437092075022733453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21081651624728050015155635 31622477437092075022733453)
                ·
                  refine ⟨11858429038909528133525045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31622477437092075022733453 11858429038909528133525045)
                  ·
                    refine ⟨1111727722397768262517973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11858429038909528133525045 1111727722397768262517973)
                    ·
                      rfl

theorem cell22_3247623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_3247623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247623 prefixEnd_3247623 := by exact prefixLift 3247623
  have htrace : WordTrace (prefixWord ++ tailWord_3247623) baseStart_3247623 baseEnd_3247623 := by
    simpa [prefixWord, tailWord_3247623, baseEnd_3247623] using wordTrace_append hprefix tailTrace_3247623
  have hstable : (prefixWord ++ tailWord_3247623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247623).length < 2 ^ (prefixWord ++ tailWord_3247623).sum := by decide
  have hdescent : baseEnd_3247623 < baseStart_3247623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247627 : List Nat := [1, 1, 1, 1, 8, 1, 3, 1, 1, 4]
def baseStart_3247627 : Nat := 118140960795 + 3247627 * 2 ^ 59
def prefixEnd_3247627 : Nat := 4983230072969 + 3 ^ 40 * 3247627 * 2
def baseEnd_3247627 : Nat := 1111729091679513585417961

theorem tailTrace_3247627 : CollatzResearch.WordTrace tailWord_3247627 prefixEnd_3247627 1111729091679513585417961 := by
  unfold tailWord_3247627
  simp only [CollatzResearch.WordTrace]
  refine ⟨118450687805409504378725135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78967125203606336252483423 118450687805409504378725135)
  ·
    refine ⟨177676031708114256568087703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118450687805409504378725135 177676031708114256568087703)
    ·
      refine ⟨266514047562171384852131555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177676031708114256568087703 266514047562171384852131555)
      ·
        refine ⟨399771071343257077278197333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266514047562171384852131555 399771071343257077278197333)
        ·
          refine ⟨4684817242303793874353875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 399771071343257077278197333 4684817242303793874353875)
          ·
            refine ⟨7027225863455690811530813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4684817242303793874353875 7027225863455690811530813)
            ·
              refine ⟨2635209698795884054324055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7027225863455690811530813 2635209698795884054324055)
              ·
                refine ⟨3952814548193826081486083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2635209698795884054324055 3952814548193826081486083)
                ·
                  refine ⟨5929221822290739122229125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3952814548193826081486083 5929221822290739122229125)
                  ·
                    refine ⟨1111729091679513585417961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5929221822290739122229125 1111729091679513585417961)
                    ·
                      rfl

theorem cell22_3247627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 1, 4].length) (baseStart_3247627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247627 prefixEnd_3247627 := by exact prefixLift 3247627
  have htrace : WordTrace (prefixWord ++ tailWord_3247627) baseStart_3247627 baseEnd_3247627 := by
    simpa [prefixWord, tailWord_3247627, baseEnd_3247627] using wordTrace_append hprefix tailTrace_3247627
  have hstable : (prefixWord ++ tailWord_3247627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247627).length < 2 ^ (prefixWord ++ tailWord_3247627).sum := by decide
  have hdescent : baseEnd_3247627 < baseStart_3247627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247713 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3247713 : Nat := 118140960795 + 3247713 * 2 ^ 59
def prefixEnd_3247713 : Nat := 4983230072969 + 3 ^ 40 * 3247713 * 2
def baseEnd_3247713 : Nat := 1111758531237038027767697

theorem tailTrace_3247713 : CollatzResearch.WordTrace tailWord_3247713 prefixEnd_3247713 1111758531237038027767697 := by
  unfold tailWord_3247713
  simp only [CollatzResearch.WordTrace]
  refine ⟨118453824483097941066355793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78969216322065294044237195 118453824483097941066355793)
  ·
    refine ⟨88840368362323455799766845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118453824483097941066355793 88840368362323455799766845)
    ·
      refine ⟨33315138135871295924912567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88840368362323455799766845 33315138135871295924912567)
      ·
        refine ⟨49972707203806943887368851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33315138135871295924912567 49972707203806943887368851)
        ·
          refine ⟨74959060805710415831053277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49972707203806943887368851 74959060805710415831053277)
          ·
            refine ⟨28109647802141405936644979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74959060805710415831053277 28109647802141405936644979)
            ·
              refine ⟨42164471703212108904967469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28109647802141405936644979 42164471703212108904967469)
              ·
                refine ⟨15811676888704540839362801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42164471703212108904967469 15811676888704540839362801)
                ·
                  refine ⟨11858757666528405629522101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15811676888704540839362801 11858757666528405629522101)
                  ·
                    refine ⟨1111758531237038027767697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11858757666528405629522101 1111758531237038027767697)
                    ·
                      rfl

theorem cell22_3247713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3247713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247713 prefixEnd_3247713 := by exact prefixLift 3247713
  have htrace : WordTrace (prefixWord ++ tailWord_3247713) baseStart_3247713 baseEnd_3247713 := by
    simpa [prefixWord, tailWord_3247713, baseEnd_3247713] using wordTrace_append hprefix tailTrace_3247713
  have hstable : (prefixWord ++ tailWord_3247713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247713).length < 2 ^ (prefixWord ++ tailWord_3247713).sum := by decide
  have hdescent : baseEnd_3247713 < baseStart_3247713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247760 : List Nat := [2, 1, 1, 1, 1, 1, 3, 8, 4]
def baseStart_3247760 : Nat := 118140960795 + 3247760 * 2 ^ 59
def prefixEnd_3247760 : Nat := 4983230072969 + 3 ^ 40 * 3247760 * 2
def baseEnd_3247760 : Nat := 370591540099181857280851

theorem tailTrace_3247760 : CollatzResearch.WordTrace tailWord_3247760 prefixEnd_3247760 370591540099181857280851 := by
  unfold tailWord_3247760
  simp only [CollatzResearch.WordTrace]
  refine ⟨59227769356963834046658367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78970359142618445395544489 59227769356963834046658367)
  ·
    refine ⟨88841654035445751069987551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59227769356963834046658367 88841654035445751069987551)
    ·
      refine ⟨133262481053168626604981327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88841654035445751069987551 133262481053168626604981327)
      ·
        refine ⟨199893721579752939907471991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133262481053168626604981327 199893721579752939907471991)
        ·
          refine ⟨299840582369629409861207987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199893721579752939907471991 299840582369629409861207987)
          ·
            refine ⟨449760873554444114791811981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299840582369629409861207987 449760873554444114791811981)
            ·
              refine ⟨168660327582916543046929493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 449760873554444114791811981 168660327582916543046929493)
              ·
                refine ⟨1976488213862303238831205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 168660327582916543046929493 1976488213862303238831205)
                ·
                  refine ⟨370591540099181857280851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1976488213862303238831205 370591540099181857280851)
                  ·
                    rfl

theorem cell22_3247760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 4].length) (baseStart_3247760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247760 prefixEnd_3247760 := by exact prefixLift 3247760
  have htrace : WordTrace (prefixWord ++ tailWord_3247760) baseStart_3247760 baseEnd_3247760 := by
    simpa [prefixWord, tailWord_3247760, baseEnd_3247760] using wordTrace_append hprefix tailTrace_3247760
  have hstable : (prefixWord ++ tailWord_3247760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247760).length < 2 ^ (prefixWord ++ tailWord_3247760).sum := by decide
  have hdescent : baseEnd_3247760 < baseStart_3247760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247944 : List Nat := [2, 1, 3, 1, 1, 5, 1, 3, 2, 3]
def baseStart_3247944 : Nat := 118140960795 + 3247944 * 2 ^ 59
def prefixEnd_3247944 : Nat := 4983230072969 + 3 ^ 40 * 3247944 * 2
def baseEnd_3247944 : Nat := 1111837607257830425241989

theorem tailTrace_3247944 : CollatzResearch.WordTrace tailWord_3247944 prefixEnd_3247944 1111837607257830425241989 := by
  unfold tailWord_3247944
  simp only [CollatzResearch.WordTrace]
  refine ⟨59231124872630533759007443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78974833163507378345343257 59231124872630533759007443)
  ·
    refine ⟨88846687308945800638511165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59231124872630533759007443 88846687308945800638511165)
    ·
      refine ⟨33317507740854675239441687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88846687308945800638511165 33317507740854675239441687)
      ·
        refine ⟨49976261611282012859162531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33317507740854675239441687 49976261611282012859162531)
        ·
          refine ⟨74964392416923019288743797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49976261611282012859162531 74964392416923019288743797)
          ·
            refine ⟨7027911789086533058319731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74964392416923019288743797 7027911789086533058319731)
            ·
              refine ⟨10541867683629799587479597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7027911789086533058319731 10541867683629799587479597)
              ·
                refine ⟨3953200381361174845304849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10541867683629799587479597 3953200381361174845304849)
                ·
                  refine ⟨2964900286020881133978637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3953200381361174845304849 2964900286020881133978637)
                  ·
                    refine ⟨1111837607257830425241989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2964900286020881133978637 1111837607257830425241989)
                    ·
                      rfl

theorem cell22_3247944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_3247944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247944 prefixEnd_3247944 := by exact prefixLift 3247944
  have htrace : WordTrace (prefixWord ++ tailWord_3247944) baseStart_3247944 baseEnd_3247944 := by
    simpa [prefixWord, tailWord_3247944, baseEnd_3247944] using wordTrace_append hprefix tailTrace_3247944
  have hstable : (prefixWord ++ tailWord_3247944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247944).length < 2 ^ (prefixWord ++ tailWord_3247944).sum := by decide
  have hdescent : baseEnd_3247944 < baseStart_3247944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247959 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 2, 4]
def baseStart_3247959 : Nat := 118140960795 + 3247959 * 2 ^ 59
def prefixEnd_3247959 : Nat := 4983230072969 + 3 ^ 40 * 3247959 * 2
def baseEnd_3247959 : Nat := 1111842742064375386116943

theorem tailTrace_3247959 : CollatzResearch.WordTrace tailWord_3247959 prefixEnd_3247959 1111842742064375386116943 := by
  unfold tailWord_3247959
  simp only [CollatzResearch.WordTrace]
  refine ⟨118462796840206725079810931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78975197893471150053207287 118462796840206725079810931)
  ·
    refine ⟨177694195260310087619716397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118462796840206725079810931 177694195260310087619716397)
    ·
      refine ⟨66635323222616282857393649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177694195260310087619716397 66635323222616282857393649)
      ·
        refine ⟨49976492416962212143045237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66635323222616282857393649 49976492416962212143045237)
        ·
          refine ⟨4685296164090207388410491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49976492416962212143045237 4685296164090207388410491)
          ·
            refine ⟨7027944246135311082615737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4685296164090207388410491 7027944246135311082615737)
            ·
              refine ⟨5270958184601483311961803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7027944246135311082615737 5270958184601483311961803)
              ·
                refine ⟨7906437276902224967942705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5270958184601483311961803 7906437276902224967942705)
                ·
                  refine ⟨5929827957676668725957029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7906437276902224967942705 5929827957676668725957029)
                  ·
                    refine ⟨1111842742064375386116943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5929827957676668725957029 1111842742064375386116943)
                    ·
                      rfl

theorem cell22_3247959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_3247959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247959 prefixEnd_3247959 := by exact prefixLift 3247959
  have htrace : WordTrace (prefixWord ++ tailWord_3247959) baseStart_3247959 baseEnd_3247959 := by
    simpa [prefixWord, tailWord_3247959, baseEnd_3247959] using wordTrace_append hprefix tailTrace_3247959
  have hstable : (prefixWord ++ tailWord_3247959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247959).length < 2 ^ (prefixWord ++ tailWord_3247959).sum := by decide
  have hdescent : baseEnd_3247959 < baseStart_3247959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247978 : List Nat := [3, 1, 3, 4, 1, 1, 2, 2, 2, 3]
def baseStart_3247978 : Nat := 118140960795 + 3247978 * 2 ^ 59
def prefixEnd_3247978 : Nat := 4983230072969 + 3 ^ 40 * 3247978 * 2
def baseEnd_3247978 : Nat := 1111849246152665669891885

theorem tailTrace_3247978 : CollatzResearch.WordTrace tailWord_3247978 prefixEnd_3247978 1111849246152665669891885 := by
  unfold tailWord_3247978
  simp only [CollatzResearch.WordTrace]
  refine ⟨29615872456784472831188147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78975659884758594216501725 29615872456784472831188147)
  ·
    refine ⟨44423808685176709246782221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29615872456784472831188147 44423808685176709246782221)
    ·
      refine ⟨16658928256941265967543333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44423808685176709246782221 16658928256941265967543333)
      ·
        refine ⟨3123549048176487368914375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16658928256941265967543333 3123549048176487368914375)
        ·
          refine ⟨4685323572264731053371563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3123549048176487368914375 4685323572264731053371563)
          ·
            refine ⟨7027985358397096580057345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4685323572264731053371563 7027985358397096580057345)
            ·
              refine ⟨5270989018797822435043009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7027985358397096580057345 5270989018797822435043009)
              ·
                refine ⟨3953241764098366826282257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5270989018797822435043009 3953241764098366826282257)
                ·
                  refine ⟨2964931323073775119711693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3953241764098366826282257 2964931323073775119711693)
                  ·
                    refine ⟨1111849246152665669891885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2964931323073775119711693 1111849246152665669891885)
                    ·
                      rfl

theorem cell22_3247978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_3247978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247978 prefixEnd_3247978 := by exact prefixLift 3247978
  have htrace : WordTrace (prefixWord ++ tailWord_3247978) baseStart_3247978 baseEnd_3247978 := by
    simpa [prefixWord, tailWord_3247978, baseEnd_3247978] using wordTrace_append hprefix tailTrace_3247978
  have hstable : (prefixWord ++ tailWord_3247978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247978).length < 2 ^ (prefixWord ++ tailWord_3247978).sum := by decide
  have hdescent : baseEnd_3247978 < baseStart_3247978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247989 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 3, 3]
def baseStart_3247989 : Nat := 118140960795 + 3247989 * 2 ^ 59
def prefixEnd_3247989 : Nat := 4983230072969 + 3 ^ 40 * 3247989 * 2
def baseEnd_3247989 : Nat := 1111853011677465307866851

theorem tailTrace_3247989 : CollatzResearch.WordTrace tailWord_3247989 prefixEnd_3247989 1111853011677465307866851 := by
  unfold tailWord_3247989
  simp only [CollatzResearch.WordTrace]
  refine ⟨118463891030098040203403021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78975927353398693468935347 118463891030098040203403021)
  ·
    refine ⟨44423959136286765076276133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118463891030098040203403021 44423959136286765076276133)
    ·
      refine ⟨8329492338053768451801775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44423959136286765076276133 8329492338053768451801775)
      ·
        refine ⟨12494238507080652677702663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8329492338053768451801775 12494238507080652677702663)
        ·
          refine ⟨18741357760620979016553995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12494238507080652677702663 18741357760620979016553995)
          ·
            refine ⟨28112036640931468524830993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18741357760620979016553995 28112036640931468524830993)
            ·
              refine ⟨21084027480698601393623245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28112036640931468524830993 21084027480698601393623245)
              ·
                refine ⟨7906510305261975522608717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21084027480698601393623245 7906510305261975522608717)
                ·
                  refine ⟨2964941364473240820978269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7906510305261975522608717 2964941364473240820978269)
                  ·
                    refine ⟨1111853011677465307866851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2964941364473240820978269 1111853011677465307866851)
                    ·
                      rfl

theorem cell22_3247989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_3247989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3247989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3247989 prefixEnd_3247989 := by exact prefixLift 3247989
  have htrace : WordTrace (prefixWord ++ tailWord_3247989) baseStart_3247989 baseEnd_3247989 := by
    simpa [prefixWord, tailWord_3247989, baseEnd_3247989] using wordTrace_append hprefix tailTrace_3247989
  have hstable : (prefixWord ++ tailWord_3247989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247989).length < 2 ^ (prefixWord ++ tailWord_3247989).sum := by decide
  have hdescent : baseEnd_3247989 < baseStart_3247989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248047 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 6]
def baseStart_3248047 : Nat := 118140960795 + 3248047 * 2 ^ 59
def prefixEnd_3248047 : Nat := 4983230072969 + 3 ^ 40 * 3248047 * 2
def baseEnd_3248047 : Nat := 370624288754257496638891

theorem tailTrace_3248047 : CollatzResearch.WordTrace tailWord_3248047 prefixEnd_3248047 370624288754257496638891 := by
  unfold tailWord_3248047
  simp only [CollatzResearch.WordTrace]
  refine ⟨118466006463887916109014395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78977337642591944072676263 118466006463887916109014395)
  ·
    refine ⟨177699009695831874163521593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118466006463887916109014395 177699009695831874163521593)
    ·
      refine ⟨133274257271873905622641195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177699009695831874163521593 133274257271873905622641195)
      ·
        refine ⟨199911385907810858433961793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133274257271873905622641195 199911385907810858433961793)
        ·
          refine ⟨149933539430858143825471345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199911385907810858433961793 149933539430858143825471345)
          ·
            refine ⟨112450154573143607869103509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149933539430858143825471345 112450154573143607869103509)
            ·
              refine ⟨5271100995616106618864227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112450154573143607869103509 5271100995616106618864227)
              ·
                refine ⟨7906651493424159928296341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271100995616106618864227 7906651493424159928296341)
                ·
                  refine ⟨370624288754257496638891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7906651493424159928296341 370624288754257496638891)
                  ·
                    rfl

theorem cell22_3248047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 6].length) (baseStart_3248047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248047 prefixEnd_3248047 := by exact prefixLift 3248047
  have htrace : WordTrace (prefixWord ++ tailWord_3248047) baseStart_3248047 baseEnd_3248047 := by
    simpa [prefixWord, tailWord_3248047, baseEnd_3248047] using wordTrace_append hprefix tailTrace_3248047
  have hstable : (prefixWord ++ tailWord_3248047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248047).length < 2 ^ (prefixWord ++ tailWord_3248047).sum := by decide
  have hdescent : baseEnd_3248047 < baseStart_3248047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248098 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 6]
def baseStart_3248098 : Nat := 118140960795 + 3248098 * 2 ^ 59
def prefixEnd_3248098 : Nat := 4983230072969 + 3 ^ 40 * 3248098 * 2
def baseEnd_3248098 : Nat := 370630108201675118963839

theorem tailTrace_3248098 : CollatzResearch.WordTrace tailWord_3248098 prefixEnd_3248098 370630108201675118963839 := by
  unfold tailWord_3248098
  simp only [CollatzResearch.WordTrace]
  refine ⟨29616966646675787954780237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78978577724468767879413965 29616966646675787954780237)
  ·
    refine ⟨11106362492503420483042589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29616966646675787954780237 11106362492503420483042589)
    ·
      refine ⟨4164885934688782681140971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11106362492503420483042589 4164885934688782681140971)
      ·
        refine ⟨6247328902033174021711457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4164885934688782681140971 6247328902033174021711457)
        ·
          refine ⟨4685496676524880516283593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6247328902033174021711457 4685496676524880516283593)
          ·
            refine ⟨3514122507393660387212695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4685496676524880516283593 3514122507393660387212695)
            ·
              refine ⟨5271183761090490580819043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514122507393660387212695 5271183761090490580819043)
              ·
                refine ⟨7906775641635735871228565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271183761090490580819043 7906775641635735871228565)
                ·
                  refine ⟨370630108201675118963839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7906775641635735871228565 370630108201675118963839)
                  ·
                    rfl

theorem cell22_3248098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_3248098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248098 prefixEnd_3248098 := by exact prefixLift 3248098
  have htrace : WordTrace (prefixWord ++ tailWord_3248098) baseStart_3248098 baseEnd_3248098 := by
    simpa [prefixWord, tailWord_3248098, baseEnd_3248098] using wordTrace_append hprefix tailTrace_3248098
  have hstable : (prefixWord ++ tailWord_3248098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248098).length < 2 ^ (prefixWord ++ tailWord_3248098).sum := by decide
  have hdescent : baseEnd_3248098 < baseStart_3248098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248124 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 5, 3]
def baseStart_3248124 : Nat := 118140960795 + 3248124 * 2 ^ 59
def prefixEnd_3248124 : Nat := 4983230072969 + 3 ^ 40 * 3248124 * 2
def baseEnd_3248124 : Nat := 1111899224936369955741437

theorem tailTrace_3248124 : CollatzResearch.WordTrace tailWord_3248124 prefixEnd_3248124 1111899224936369955741437 := by
  unfold tailWord_3248124
  simp only [CollatzResearch.WordTrace]
  refine ⟨59234407442304479129783713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78979209923072638839711617 59234407442304479129783713)
  ·
    refine ⟨44425805581728359347337785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59234407442304479129783713 44425805581728359347337785)
    ·
      refine ⟨33319354186296269510503339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44425805581728359347337785 33319354186296269510503339)
      ·
        refine ⟨49979031279444404265755009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33319354186296269510503339 49979031279444404265755009)
        ·
          refine ⟨37484273459583303199316257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49979031279444404265755009 37484273459583303199316257)
          ·
            refine ⟨28113205094687477399487193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37484273459583303199316257 28113205094687477399487193)
            ·
              refine ⟨21084903821015608049615395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28113205094687477399487193 21084903821015608049615395)
              ·
                refine ⟨31627355731523412074423093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21084903821015608049615395 31627355731523412074423093)
                ·
                  refine ⟨2965064599830319881977165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31627355731523412074423093 2965064599830319881977165)
                  ·
                    refine ⟨1111899224936369955741437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2965064599830319881977165 1111899224936369955741437)
                    ·
                      rfl

theorem cell22_3248124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_3248124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248124 prefixEnd_3248124 := by exact prefixLift 3248124
  have htrace : WordTrace (prefixWord ++ tailWord_3248124) baseStart_3248124 baseEnd_3248124 := by
    simpa [prefixWord, tailWord_3248124, baseEnd_3248124] using wordTrace_append hprefix tailTrace_3248124
  have hstable : (prefixWord ++ tailWord_3248124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248124).length < 2 ^ (prefixWord ++ tailWord_3248124).sum := by decide
  have hdescent : baseEnd_3248124 < baseStart_3248124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248134 : List Nat := [6, 2, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3248134 : Nat := 118140960795 + 3248134 * 2 ^ 59
def prefixEnd_3248134 : Nat := 4983230072969 + 3 ^ 40 * 3248134 * 2
def baseEnd_3248134 : Nat := 1111902648140733262991407

theorem tailTrace_3248134 : CollatzResearch.WordTrace tailWord_3248134 prefixEnd_3248134 1111902648140733262991407 := by
  unfold tailWord_3248134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3702161862955397811482233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78979453076381819978287637 3702161862955397811482233)
  ·
    refine ⟨2776621397216548358611675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3702161862955397811482233 2776621397216548358611675)
    ·
      refine ⟨4164932095824822537917513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2776621397216548358611675 4164932095824822537917513)
      ·
        refine ⟨3123699071868616903438135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4164932095824822537917513 3123699071868616903438135)
        ·
          refine ⟨4685548607802925355157203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3123699071868616903438135 4685548607802925355157203)
          ·
            refine ⟨7028322911704388032735805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4685548607802925355157203 7028322911704388032735805)
            ·
              refine ⟨2635621091889145512275927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7028322911704388032735805 2635621091889145512275927)
              ·
                refine ⟨3953431637833718268413891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2635621091889145512275927 3953431637833718268413891)
                ·
                  refine ⟨5930147456750577402620837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3953431637833718268413891 5930147456750577402620837)
                  ·
                    refine ⟨1111902648140733262991407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5930147456750577402620837 1111902648140733262991407)
                    ·
                      rfl

theorem cell22_3248134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3248134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248134 prefixEnd_3248134 := by exact prefixLift 3248134
  have htrace : WordTrace (prefixWord ++ tailWord_3248134) baseStart_3248134 baseEnd_3248134 := by
    simpa [prefixWord, tailWord_3248134, baseEnd_3248134] using wordTrace_append hprefix tailTrace_3248134
  have hstable : (prefixWord ++ tailWord_3248134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248134).length < 2 ^ (prefixWord ++ tailWord_3248134).sum := by decide
  have hdescent : baseEnd_3248134 < baseStart_3248134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248154 : List Nat := [3, 1, 1, 3, 1, 3, 1, 4, 5]
def baseStart_3248154 : Nat := 118140960795 + 3248154 * 2 ^ 59
def prefixEnd_3248154 : Nat := 4983230072969 + 3 ^ 40 * 3248154 * 2
def baseEnd_3248154 : Nat := 370636498183153292497115

theorem tailTrace_3248154 : CollatzResearch.WordTrace tailWord_3248154 prefixEnd_3248154 370636498183153292497115 := by
  unfold tailWord_3248154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29617477268625068345789879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78979939383000182255439677 29617477268625068345789879)
  ·
    refine ⟨44426215902937602518684819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29617477268625068345789879 44426215902937602518684819)
    ·
      refine ⟨66639323854406403778027229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44426215902937602518684819 66639323854406403778027229)
      ·
        refine ⟨24989746445402401416760211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66639323854406403778027229 24989746445402401416760211)
        ·
          refine ⟨37484619668103602125140317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24989746445402401416760211 37484619668103602125140317)
          ·
            refine ⟨14056732375538850796927619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37484619668103602125140317 14056732375538850796927619)
            ·
              refine ⟨21085098563308276195391429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14056732375538850796927619 21085098563308276195391429)
              ·
                refine ⟨3953455980620301786635893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21085098563308276195391429 3953455980620301786635893)
                ·
                  refine ⟨370636498183153292497115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3953455980620301786635893 370636498183153292497115)
                  ·
                    rfl

theorem cell22_3248154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_3248154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248154 prefixEnd_3248154 := by exact prefixLift 3248154
  have htrace : WordTrace (prefixWord ++ tailWord_3248154) baseStart_3248154 baseEnd_3248154 := by
    simpa [prefixWord, tailWord_3248154, baseEnd_3248154] using wordTrace_append hprefix tailTrace_3248154
  have hstable : (prefixWord ++ tailWord_3248154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248154).length < 2 ^ (prefixWord ++ tailWord_3248154).sum := by decide
  have hdescent : baseEnd_3248154 < baseStart_3248154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248216 : List Nat := [2, 1, 2, 2, 1, 4, 2, 4, 4]
def baseStart_3248216 : Nat := 118140960795 + 3248216 * 2 ^ 59
def prefixEnd_3248216 : Nat := 4983230072969 + 3 ^ 40 * 3248216 * 2
def baseEnd_3248216 : Nat := 370643572805504127480385

theorem tailTrace_3248216 : CollatzResearch.WordTrace tailWord_3248216 prefixEnd_3248216 370643572805504127480385 := by
  unfold tailWord_3248216
  simp only [CollatzResearch.WordTrace]
  refine ⟨59236085200137828985958251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78981446933517105314611001 59236085200137828985958251)
  ·
    refine ⟨88854127800206743478937377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59236085200137828985958251 88854127800206743478937377)
    ·
      refine ⟨66640595850155057609203033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88854127800206743478937377 66640595850155057609203033)
      ·
        refine ⟨49980446887616293206902275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66640595850155057609203033 49980446887616293206902275)
        ·
          refine ⟨74970670331424439810353413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49980446887616293206902275 74970670331424439810353413)
          ·
            refine ⟨14057000687142082464441265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74970670331424439810353413 14057000687142082464441265)
            ·
              refine ⟨10542750515356561848330949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14057000687142082464441265 10542750515356561848330949)
              ·
                refine ⟨1976765721629355346562053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10542750515356561848330949 1976765721629355346562053)
                ·
                  refine ⟨370643572805504127480385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1976765721629355346562053 370643572805504127480385)
                  ·
                    rfl

theorem cell22_3248216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 4].length) (baseStart_3248216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248216 prefixEnd_3248216 := by exact prefixLift 3248216
  have htrace : WordTrace (prefixWord ++ tailWord_3248216) baseStart_3248216 baseEnd_3248216 := by
    simpa [prefixWord, tailWord_3248216, baseEnd_3248216] using wordTrace_append hprefix tailTrace_3248216
  have hstable : (prefixWord ++ tailWord_3248216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248216).length < 2 ^ (prefixWord ++ tailWord_3248216).sum := by decide
  have hdescent : baseEnd_3248216 < baseStart_3248216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248222 : List Nat := [4, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_3248222 : Nat := 118140960795 + 3248222 * 2 ^ 59
def prefixEnd_3248222 : Nat := 4983230072969 + 3 ^ 40 * 3248222 * 2
def baseEnd_3248222 : Nat := 370644257446376788930379

theorem tailTrace_3248222 : CollatzResearch.WordTrace tailWord_3248222 prefixEnd_3248222 370644257446376788930379 := by
  unfold tailWord_3248222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14809048654781740124579365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78981592825502613997756613 14809048654781740124579365)
  ·
    refine ⟨2776696622771576273358631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14809048654781740124579365 2776696622771576273358631)
    ·
      refine ⟨4165044934157364410037947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2776696622771576273358631 4165044934157364410037947)
      ·
        refine ⟨6247567401236046615056921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4165044934157364410037947 6247567401236046615056921)
        ·
          refine ⟨4685675550927034961292691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6247567401236046615056921 4685675550927034961292691)
          ·
            refine ⟨7028513326390552441939037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4685675550927034961292691 7028513326390552441939037)
            ·
              refine ⟨2635692497396457165727139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7028513326390552441939037 2635692497396457165727139)
              ·
                refine ⟨3953538746094685748590709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2635692497396457165727139 3953538746094685748590709)
                ·
                  refine ⟨370644257446376788930379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3953538746094685748590709 370644257446376788930379)
                  ·
                    rfl

theorem cell22_3248222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_3248222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248222 prefixEnd_3248222 := by exact prefixLift 3248222
  have htrace : WordTrace (prefixWord ++ tailWord_3248222) baseStart_3248222 baseEnd_3248222 := by
    simpa [prefixWord, tailWord_3248222, baseEnd_3248222] using wordTrace_append hprefix tailTrace_3248222
  have hstable : (prefixWord ++ tailWord_3248222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248222).length < 2 ^ (prefixWord ++ tailWord_3248222).sum := by decide
  have hdescent : baseEnd_3248222 < baseStart_3248222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248229 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_3248229 : Nat := 118140960795 + 3248229 * 2 ^ 59
def prefixEnd_3248229 : Nat := 4983230072969 + 3 ^ 40 * 3248229 * 2
def baseEnd_3248229 : Nat := 1111935168582184681866115

theorem tailTrace_3248229 : CollatzResearch.WordTrace tailWord_3248229 prefixEnd_3248229 1111935168582184681866115 := by
  unfold tailWord_3248229
  simp only [CollatzResearch.WordTrace]
  refine ⟨118472644549228561192139741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78981763032819040794759827 118472644549228561192139741)
  ·
    refine ⟨44427241705960710447052403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118472644549228561192139741 44427241705960710447052403)
    ·
      refine ⟨66640862558941065670578605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44427241705960710447052403 66640862558941065670578605)
      ·
        refine ⟨24990323459602899626466977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66640862558941065670578605 24990323459602899626466977)
        ·
          refine ⟨18742742594702174719850233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24990323459602899626466977 18742742594702174719850233)
          ·
            refine ⟨14057056946026631039887675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18742742594702174719850233 14057056946026631039887675)
            ·
              refine ⟨21085585419039946559831513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14057056946026631039887675 21085585419039946559831513)
              ·
                refine ⟨15814189064279959919873635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21085585419039946559831513 15814189064279959919873635)
                ·
                  refine ⟨23721283596419939879810453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15814189064279959919873635 23721283596419939879810453)
                  ·
                    refine ⟨1111935168582184681866115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23721283596419939879810453 1111935168582184681866115)
                    ·
                      rfl

theorem cell22_3248229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_3248229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248229 prefixEnd_3248229 := by exact prefixLift 3248229
  have htrace : WordTrace (prefixWord ++ tailWord_3248229) baseStart_3248229 baseEnd_3248229 := by
    simpa [prefixWord, tailWord_3248229, baseEnd_3248229] using wordTrace_append hprefix tailTrace_3248229
  have hstable : (prefixWord ++ tailWord_3248229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248229).length < 2 ^ (prefixWord ++ tailWord_3248229).sum := by decide
  have hdescent : baseEnd_3248229 < baseStart_3248229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248246 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_3248246 : Nat := 118140960795 + 3248246 * 2 ^ 59
def prefixEnd_3248246 : Nat := 4983230072969 + 3 ^ 40 * 3248246 * 2
def baseEnd_3248246 : Nat := 1111940988029602304191063

theorem tailTrace_3248246 : CollatzResearch.WordTrace tailWord_3248246 prefixEnd_3248246 1111940988029602304191063 := by
  unfold tailWord_3248246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7404579036885435818469287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78982176393444648730339061 7404579036885435818469287)
  ·
    refine ⟨11106868555328153727703931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7404579036885435818469287 11106868555328153727703931)
    ·
      refine ⟨16660302832992230591555897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11106868555328153727703931 16660302832992230591555897)
      ·
        refine ⟨12495227124744172943666923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16660302832992230591555897 12495227124744172943666923)
        ·
          refine ⟨18742840687116259415500385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12495227124744172943666923 18742840687116259415500385)
          ·
            refine ⟨14057130515337194561625289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18742840687116259415500385 14057130515337194561625289)
            ·
              refine ⟨10542847886502895921218967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14057130515337194561625289 10542847886502895921218967)
              ·
                refine ⟨15814271829754343881828451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10542847886502895921218967 15814271829754343881828451)
                ·
                  refine ⟨23721407744631515822742677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15814271829754343881828451 23721407744631515822742677)
                  ·
                    refine ⟨1111940988029602304191063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23721407744631515822742677 1111940988029602304191063)
                    ·
                      rfl

theorem cell22_3248246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_3248246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248246 prefixEnd_3248246 := by exact prefixLift 3248246
  have htrace : WordTrace (prefixWord ++ tailWord_3248246) baseStart_3248246 baseEnd_3248246 := by
    simpa [prefixWord, tailWord_3248246, baseEnd_3248246] using wordTrace_append hprefix tailTrace_3248246
  have hstable : (prefixWord ++ tailWord_3248246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248246).length < 2 ^ (prefixWord ++ tailWord_3248246).sum := by decide
  have hdescent : baseEnd_3248246 < baseStart_3248246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248282 : List Nat := [3, 1, 1, 5, 2, 2, 2, 1, 2, 3]
def baseStart_3248282 : Nat := 118140960795 + 3248282 * 2 ^ 59
def prefixEnd_3248282 : Nat := 4983230072969 + 3 ^ 40 * 3248282 * 2
def baseEnd_3248282 : Nat := 1111953311565310210290953

theorem tailTrace_3248282 : CollatzResearch.WordTrace tailWord_3248282 prefixEnd_3248282 1111953311565310210290953 := by
  unfold tailWord_3248282
  simp only [CollatzResearch.WordTrace]
  refine ⟨29618644404509137810954775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78983051745357700829212733 29618644404509137810954775)
  ·
    refine ⟨44427966606763706716432163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29618644404509137810954775 44427966606763706716432163)
    ·
      refine ⟨66641949910145560074648245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44427966606763706716432163 66641949910145560074648245)
      ·
        refine ⟨6247682804076146256998273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66641949910145560074648245 6247682804076146256998273)
        ·
          refine ⟨4685762103057109692748705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6247682804076146256998273 4685762103057109692748705)
          ·
            refine ⟨3514321577292832269561529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4685762103057109692748705 3514321577292832269561529)
            ·
              refine ⟨2635741182969624202171147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3514321577292832269561529 2635741182969624202171147)
              ·
                refine ⟨3953611774454436303256721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2635741182969624202171147 3953611774454436303256721)
                ·
                  refine ⟨2965208830840827227442541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3953611774454436303256721 2965208830840827227442541)
                  ·
                    refine ⟨1111953311565310210290953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2965208830840827227442541 1111953311565310210290953)
                    ·
                      rfl

theorem cell22_3248282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_3248282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248282 prefixEnd_3248282 := by exact prefixLift 3248282
  have htrace : WordTrace (prefixWord ++ tailWord_3248282) baseStart_3248282 baseEnd_3248282 := by
    simpa [prefixWord, tailWord_3248282, baseEnd_3248282] using wordTrace_append hprefix tailTrace_3248282
  have hstable : (prefixWord ++ tailWord_3248282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248282).length < 2 ^ (prefixWord ++ tailWord_3248282).sum := by decide
  have hdescent : baseEnd_3248282 < baseStart_3248282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248370 : List Nat := [3, 2, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_3248370 : Nat := 118140960795 + 3248370 * 2 ^ 59
def prefixEnd_3248370 : Nat := 4983230072969 + 3 ^ 40 * 3248370 * 2
def baseEnd_3248370 : Nat := 1111983435763707314090683

theorem tailTrace_3248370 : CollatzResearch.WordTrace tailWord_3248370 prefixEnd_3248370 1111983435763707314090683 := by
  unfold tailWord_3248370
  simp only [CollatzResearch.WordTrace]
  refine ⟨29619446810429435568255641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78985191494478494848681709 29619446810429435568255641)
  ·
    refine ⟨22214585107822076676191731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29619446810429435568255641 22214585107822076676191731)
    ·
      refine ⟨33321877661733115014287597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22214585107822076676191731 33321877661733115014287597)
      ·
        refine ⟨12495704123149918130357849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33321877661733115014287597 12495704123149918130357849)
        ·
          refine ⟨9371778092362438597768387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12495704123149918130357849 9371778092362438597768387)
          ·
            refine ⟨14057667138543657896652581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9371778092362438597768387 14057667138543657896652581)
            ·
              refine ⟨2635812588476935855622359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14057667138543657896652581 2635812588476935855622359)
              ·
                refine ⟨3953718882715403783433539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2635812588476935855622359 3953718882715403783433539)
                ·
                  refine ⟨5930578324073105675150309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3953718882715403783433539 5930578324073105675150309)
                  ·
                    refine ⟨1111983435763707314090683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5930578324073105675150309 1111983435763707314090683)
                    ·
                      rfl

theorem cell22_3248370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_3248370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248370 prefixEnd_3248370 := by exact prefixLift 3248370
  have htrace : WordTrace (prefixWord ++ tailWord_3248370) baseStart_3248370 baseEnd_3248370 := by
    simpa [prefixWord, tailWord_3248370, baseEnd_3248370] using wordTrace_append hprefix tailTrace_3248370
  have hstable : (prefixWord ++ tailWord_3248370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248370).length < 2 ^ (prefixWord ++ tailWord_3248370).sum := by decide
  have hdescent : baseEnd_3248370 < baseStart_3248370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248381 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_3248381 : Nat := 118140960795 + 3248381 * 2 ^ 59
def prefixEnd_3248381 : Nat := 4983230072969 + 3 ^ 40 * 3248381 * 2
def baseEnd_3248381 : Nat := 1111987201288506952065649

theorem tailTrace_3248381 : CollatzResearch.WordTrace tailWord_3248381 prefixEnd_3248381 1111987201288506952065649 := by
  unfold tailWord_3248381
  simp only [CollatzResearch.WordTrace]
  refine ⟨118478188444677891151672997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78985458963118594101115331 118478188444677891151672997)
  ·
    refine ⟨22214660333377104590938687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118478188444677891151672997 22214660333377104590938687)
    ·
      refine ⟨33321990500065656886408031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22214660333377104590938687 33321990500065656886408031)
      ·
        refine ⟨49982985750098485329612047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33321990500065656886408031 49982985750098485329612047)
        ·
          refine ⟨74974478625147727994418071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49982985750098485329612047 74974478625147727994418071)
          ·
            refine ⟨112461717937721591991627107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74974478625147727994418071 112461717937721591991627107)
            ·
              refine ⟨168692576906582387987440661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112461717937721591991627107 168692576906582387987440661)
              ·
                refine ⟨7907464542496049436911281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 168692576906582387987440661 7907464542496049436911281)
                ·
                  refine ⟨5930598406872037077683461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7907464542496049436911281 5930598406872037077683461)
                  ·
                    refine ⟨1111987201288506952065649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5930598406872037077683461 1111987201288506952065649)
                    ·
                      rfl

theorem cell22_3248381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_3248381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248381 prefixEnd_3248381 := by exact prefixLift 3248381
  have htrace : WordTrace (prefixWord ++ tailWord_3248381) baseStart_3248381 baseEnd_3248381 := by
    simpa [prefixWord, tailWord_3248381, baseEnd_3248381] using wordTrace_append hprefix tailTrace_3248381
  have hstable : (prefixWord ++ tailWord_3248381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248381).length < 2 ^ (prefixWord ++ tailWord_3248381).sum := by decide
  have hdescent : baseEnd_3248381 < baseStart_3248381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248413 : List Nat := [1, 4, 2, 3, 2, 1, 1, 8]
def baseStart_3248413 : Nat := 118140960795 + 3248413 * 2 ^ 59
def prefixEnd_3248413 : Nat := 4983230072969 + 3 ^ 40 * 3248413 * 2
def baseEnd_3248413 : Nat := 123555350615829948362839

theorem tailTrace_3248413 : CollatzResearch.WordTrace tailWord_3248413 prefixEnd_3248413 123555350615829948362839 := by
  unfold tailWord_3248413
  simp only [CollatzResearch.WordTrace]
  refine ⟨118479355580561960616837893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78986237053707973744558595 118479355580561960616837893)
  ·
    refine ⟨22214879171355367615657105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118479355580561960616837893 22214879171355367615657105)
    ·
      refine ⟨16661159378516525711742829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22214879171355367615657105 16661159378516525711742829)
      ·
        refine ⟨6247934766943697141903561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16661159378516525711742829 6247934766943697141903561)
        ·
          refine ⟨4685951075207772856427671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6247934766943697141903561 4685951075207772856427671)
          ·
            refine ⟨7028926612811659284641507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4685951075207772856427671 7028926612811659284641507)
            ·
              refine ⟨10543389919217488926962261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7028926612811659284641507 10543389919217488926962261)
              ·
                refine ⟨123555350615829948362839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10543389919217488926962261 123555350615829948362839)
                ·
                  rfl

theorem cell22_3248413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 8].length) (baseStart_3248413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248413 prefixEnd_3248413 := by exact prefixLift 3248413
  have htrace : WordTrace (prefixWord ++ tailWord_3248413) baseStart_3248413 baseEnd_3248413 := by
    simpa [prefixWord, tailWord_3248413, baseEnd_3248413] using wordTrace_append hprefix tailTrace_3248413
  have hstable : (prefixWord ++ tailWord_3248413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248413).length < 2 ^ (prefixWord ++ tailWord_3248413).sum := by decide
  have hdescent : baseEnd_3248413 < baseStart_3248413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248430 : List Nat := [4, 1, 3, 3, 1, 2, 8]
def baseStart_3248430 : Nat := 118140960795 + 3248430 * 2 ^ 59
def prefixEnd_3248430 : Nat := 4983230072969 + 3 ^ 40 * 3248430 * 2
def baseEnd_3248430 : Nat := 41185332407032857688537

theorem tailTrace_3248430 : CollatzResearch.WordTrace tailWord_3248430 prefixEnd_3248430 41185332407032857688537 := by
  unfold tailWord_3248430
  simp only [CollatzResearch.WordTrace]
  refine ⟨14809996952687546565025843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78986650414333581680137829 14809996952687546565025843)
  ·
    refine ⟨22214995429031319847538765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14809996952687546565025843 22214995429031319847538765)
    ·
      refine ⟨8330623285886744942827037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22214995429031319847538765 8330623285886744942827037)
      ·
        refine ⟨3123983732207529353560139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8330623285886744942827037 3123983732207529353560139)
        ·
          refine ⟨4685975598311294030340209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3123983732207529353560139 4685975598311294030340209)
          ·
            refine ⟨3514481698733470522755157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4685975598311294030340209 3514481698733470522755157)
            ·
              refine ⟨41185332407032857688537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3514481698733470522755157 41185332407032857688537)
              ·
                rfl

theorem cell22_3248430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 8].length) (baseStart_3248430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248430 prefixEnd_3248430 := by exact prefixLift 3248430
  have htrace : WordTrace (prefixWord ++ tailWord_3248430) baseStart_3248430 baseEnd_3248430 := by
    simpa [prefixWord, tailWord_3248430, baseEnd_3248430] using wordTrace_append hprefix tailTrace_3248430
  have hstable : (prefixWord ++ tailWord_3248430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248430).length < 2 ^ (prefixWord ++ tailWord_3248430).sum := by decide
  have hdescent : baseEnd_3248430 < baseStart_3248430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248456 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 2, 5]
def baseStart_3248456 : Nat := 118140960795 + 3248456 * 2 ^ 59
def prefixEnd_3248456 : Nat := 4983230072969 + 3 ^ 40 * 3248456 * 2
def baseEnd_3248456 : Nat := 1112012875321231756440419

theorem tailTrace_3248456 : CollatzResearch.WordTrace tailWord_3248456 prefixEnd_3248456 1112012875321231756440419 := by
  unfold tailWord_3248456
  simp only [CollatzResearch.WordTrace]
  refine ⟨59240461959703089480326611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78987282612937452640435481 59240461959703089480326611)
  ·
    refine ⟨88860692939554634220489917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59240461959703089480326611 88860692939554634220489917)
    ·
      refine ⟨33322759852332987832683719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88860692939554634220489917 33322759852332987832683719)
      ·
        refine ⟨49984139778499481749025579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33322759852332987832683719 49984139778499481749025579)
        ·
          refine ⟨74976209667749222623538369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49984139778499481749025579 74976209667749222623538369)
          ·
            refine ⟨56232157250811916967653777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74976209667749222623538369 56232157250811916967653777)
            ·
              refine ⟨42174117938108937725740333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56232157250811916967653777 42174117938108937725740333)
              ·
                refine ⟨15815294226790851647152625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42174117938108937725740333 15815294226790851647152625)
                ·
                  refine ⟨11861470670093138735364469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15815294226790851647152625 11861470670093138735364469)
                  ·
                    refine ⟨1112012875321231756440419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11861470670093138735364469 1112012875321231756440419)
                    ·
                      rfl

theorem cell22_3248456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_3248456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248456 prefixEnd_3248456 := by exact prefixLift 3248456
  have htrace : WordTrace (prefixWord ++ tailWord_3248456) baseStart_3248456 baseEnd_3248456 := by
    simpa [prefixWord, tailWord_3248456, baseEnd_3248456] using wordTrace_append hprefix tailTrace_3248456
  have hstable : (prefixWord ++ tailWord_3248456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248456).length < 2 ^ (prefixWord ++ tailWord_3248456).sum := by decide
  have hdescent : baseEnd_3248456 < baseStart_3248456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248552 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3248552 : Nat := 118140960795 + 3248552 * 2 ^ 59
def prefixEnd_3248552 : Nat := 4983230072969 + 3 ^ 40 * 3248552 * 2
def baseEnd_3248552 : Nat := 1112045738083119506040125

theorem tailTrace_3248552 : CollatzResearch.WordTrace tailWord_3248552 prefixEnd_3248552 1112045738083119506040125 := by
  unfold tailWord_3248552
  simp only [CollatzResearch.WordTrace]
  refine ⟨59242212663529193678073955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78989616884705591570765273 59242212663529193678073955)
  ·
    refine ⟨88863318995293790517110933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59242212663529193678073955 88863318995293790517110933)
    ·
      refine ⟨4165468077904396430489575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88863318995293790517110933 4165468077904396430489575)
      ·
        refine ⟨6248202116856594645734363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4165468077904396430489575 6248202116856594645734363)
        ·
          refine ⟨9372303175284891968601545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6248202116856594645734363 9372303175284891968601545)
          ·
            refine ⟨7029227381463668976451159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9372303175284891968601545 7029227381463668976451159)
            ·
              refine ⟨10543841072195503464676739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7029227381463668976451159 10543841072195503464676739)
              ·
                refine ⟨15815761608293255197015109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10543841072195503464676739 15815761608293255197015109)
                ·
                  refine ⟨2965455301554985349440333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15815761608293255197015109 2965455301554985349440333)
                  ·
                    refine ⟨1112045738083119506040125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2965455301554985349440333 1112045738083119506040125)
                    ·
                      rfl

theorem cell22_3248552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3248552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248552 prefixEnd_3248552 := by exact prefixLift 3248552
  have htrace : WordTrace (prefixWord ++ tailWord_3248552) baseStart_3248552 baseEnd_3248552 := by
    simpa [prefixWord, tailWord_3248552, baseEnd_3248552] using wordTrace_append hprefix tailTrace_3248552
  have hstable : (prefixWord ++ tailWord_3248552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248552).length < 2 ^ (prefixWord ++ tailWord_3248552).sum := by decide
  have hdescent : baseEnd_3248552 < baseStart_3248552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248554 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 6]
def baseStart_3248554 : Nat := 118140960795 + 3248554 * 2 ^ 59
def prefixEnd_3248554 : Nat := 4983230072969 + 3 ^ 40 * 3248554 * 2
def baseEnd_3248554 : Nat := 370682140907997389163373

theorem tailTrace_3248554 : CollatzResearch.WordTrace tailWord_3248554 prefixEnd_3248554 370682140907997389163373 := by
  unfold tailWord_3248554
  simp only [CollatzResearch.WordTrace]
  refine ⟨29621124568262785424430179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78989665515367427798480477 29621124568262785424430179)
  ·
    refine ⟨44431686852394178136645269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29621124568262785424430179 44431686852394178136645269)
    ·
      refine ⟨2082735321205977100155247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44431686852394178136645269 2082735321205977100155247)
      ·
        refine ⟨3124102981808965650232871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2082735321205977100155247 3124102981808965650232871)
        ·
          refine ⟨4686154472713448475349307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3124102981808965650232871 4686154472713448475349307)
          ·
            refine ⟨7029231709070172713023961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4686154472713448475349307 7029231709070172713023961)
            ·
              refine ⟨5271923781802629534767971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7029231709070172713023961 5271923781802629534767971)
              ·
                refine ⟨7907885672703944302151957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271923781802629534767971 7907885672703944302151957)
                ·
                  refine ⟨370682140907997389163373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7907885672703944302151957 370682140907997389163373)
                  ·
                    rfl

theorem cell22_3248554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_3248554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248554 prefixEnd_3248554 := by exact prefixLift 3248554
  have htrace : WordTrace (prefixWord ++ tailWord_3248554) baseStart_3248554 baseEnd_3248554 := by
    simpa [prefixWord, tailWord_3248554, baseEnd_3248554] using wordTrace_append hprefix tailTrace_3248554
  have hstable : (prefixWord ++ tailWord_3248554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248554).length < 2 ^ (prefixWord ++ tailWord_3248554).sum := by decide
  have hdescent : baseEnd_3248554 < baseStart_3248554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248623 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 3, 4]
def baseStart_3248623 : Nat := 118140960795 + 3248623 * 2 ^ 59
def prefixEnd_3248623 : Nat := 4983230072969 + 3 ^ 40 * 3248623 * 2
def baseEnd_3248623 : Nat := 1112070042834098987514907

theorem tailTrace_3248623 : CollatzResearch.WordTrace tailWord_3248623 prefixEnd_3248623 1112070042834098987514907 := by
  unfold tailWord_3248623
  simp only [CollatzResearch.WordTrace]
  refine ⟨118487014909801166481982523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78991343273200777654655015 118487014909801166481982523)
  ·
    refine ⟨177730522364701749722973785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118487014909801166481982523 177730522364701749722973785)
    ·
      refine ⟨133297891773526312292230339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177730522364701749722973785 133297891773526312292230339)
      ·
        refine ⟨199946837660289468438345509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133297891773526312292230339 199946837660289468438345509)
        ·
          refine ⟨37490032061304275332189783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199946837660289468438345509 37490032061304275332189783)
          ·
            refine ⟨56235048091956412998284675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37490032061304275332189783 56235048091956412998284675)
            ·
              refine ⟨84352572137934619497427013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56235048091956412998284675 84352572137934619497427013)
              ·
                refine ⟨15816107275862741155767565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84352572137934619497427013 15816107275862741155767565)
                ·
                  refine ⟨5931040228448527933412837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15816107275862741155767565 5931040228448527933412837)
                  ·
                    refine ⟨1112070042834098987514907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5931040228448527933412837 1112070042834098987514907)
                    ·
                      rfl

theorem cell22_3248623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_3248623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248623 prefixEnd_3248623 := by exact prefixLift 3248623
  have htrace : WordTrace (prefixWord ++ tailWord_3248623) baseStart_3248623 baseEnd_3248623 := by
    simpa [prefixWord, tailWord_3248623, baseEnd_3248623] using wordTrace_append hprefix tailTrace_3248623
  have hstable : (prefixWord ++ tailWord_3248623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248623).length < 2 ^ (prefixWord ++ tailWord_3248623).sum := by decide
  have hdescent : baseEnd_3248623 < baseStart_3248623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248738 : List Nat := [3, 3, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3248738 : Nat := 118140960795 + 3248738 * 2 ^ 59
def prefixEnd_3248738 : Nat := 4983230072969 + 3 ^ 40 * 3248738 * 2
def baseEnd_3248738 : Nat := 1112109409684277020889555

theorem tailTrace_3248738 : CollatzResearch.WordTrace tailWord_3248738 prefixEnd_3248738 1112109409684277020889555 := by
  unfold tailWord_3248738
  simp only [CollatzResearch.WordTrace]
  refine ⟨29622802326096135280604717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78994139536256360748279245 29622802326096135280604717)
  ·
    refine ⟨11108550872286050730226769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29622802326096135280604717 11108550872286050730226769)
    ·
      refine ⟨8331413154214538047670077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11108550872286050730226769 8331413154214538047670077)
      ·
        refine ⟨3124279932830451767876279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8331413154214538047670077 3124279932830451767876279)
        ·
          refine ⟨4686419899245677651814419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3124279932830451767876279 4686419899245677651814419)
          ·
            refine ⟨7029629848868516477721629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4686419899245677651814419 7029629848868516477721629)
            ·
              refine ⟨2636111193325693679145611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7029629848868516477721629 2636111193325693679145611)
              ·
                refine ⟨3954166789988540518718417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636111193325693679145611 3954166789988540518718417)
                ·
                  refine ⟨2965625092491405389038813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3954166789988540518718417 2965625092491405389038813)
                  ·
                    refine ⟨1112109409684277020889555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2965625092491405389038813 1112109409684277020889555)
                    ·
                      rfl

theorem cell22_3248738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3248738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248738 prefixEnd_3248738 := by exact prefixLift 3248738
  have htrace : WordTrace (prefixWord ++ tailWord_3248738) baseStart_3248738 baseEnd_3248738 := by
    simpa [prefixWord, tailWord_3248738, baseEnd_3248738] using wordTrace_append hprefix tailTrace_3248738
  have hstable : (prefixWord ++ tailWord_3248738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248738).length < 2 ^ (prefixWord ++ tailWord_3248738).sum := by decide
  have hdescent : baseEnd_3248738 < baseStart_3248738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248805 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_3248805 : Nat := 118140960795 + 3248805 * 2 ^ 59
def prefixEnd_3248805 : Nat := 4983230072969 + 3 ^ 40 * 3248805 * 2
def baseEnd_3248805 : Nat := 1112132345153511179464349

theorem tailTrace_3248805 : CollatzResearch.WordTrace tailWord_3248805 prefixEnd_3248805 1112132345153511179464349 := by
  unfold tailWord_3248805
  simp only [CollatzResearch.WordTrace]
  refine ⟨118493652995141811565107869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78995768663427874376738579 118493652995141811565107869)
  ·
    refine ⟨44435119873178179336915451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118493652995141811565107869 44435119873178179336915451)
    ·
      refine ⟨66652679809767269005373177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44435119873178179336915451 66652679809767269005373177)
      ·
        refine ⟨49989509857325451754029883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66652679809767269005373177 49989509857325451754029883)
        ·
          refine ⟨74984264785988177631044825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49989509857325451754029883 74984264785988177631044825)
          ·
            refine ⟨56238198589491133223283619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74984264785988177631044825 56238198589491133223283619)
            ·
              refine ⟨84357297884236699834925429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56238198589491133223283619 84357297884236699834925429)
              ·
                refine ⟨7908496676647190609524259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84357297884236699834925429 7908496676647190609524259)
                ·
                  refine ⟨11862745014970785914286389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7908496676647190609524259 11862745014970785914286389)
                  ·
                    refine ⟨1112132345153511179464349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11862745014970785914286389 1112132345153511179464349)
                    ·
                      rfl

theorem cell22_3248805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_3248805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248805 prefixEnd_3248805 := by exact prefixLift 3248805
  have htrace : WordTrace (prefixWord ++ tailWord_3248805) baseStart_3248805 baseEnd_3248805 := by
    simpa [prefixWord, tailWord_3248805, baseEnd_3248805] using wordTrace_append hprefix tailTrace_3248805
  have hstable : (prefixWord ++ tailWord_3248805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248805).length < 2 ^ (prefixWord ++ tailWord_3248805).sum := by decide
  have hdescent : baseEnd_3248805 < baseStart_3248805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248880 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 7]
def baseStart_3248880 : Nat := 118140960795 + 3248880 * 2 ^ 59
def prefixEnd_3248880 : Nat := 4983230072969 + 3 ^ 40 * 3248880 * 2
def baseEnd_3248880 : Nat := 370719339728745327946373

theorem tailTrace_3248880 : CollatzResearch.WordTrace tailWord_3248880 prefixEnd_3248880 370719339728745327946373 := by
  unfold tailWord_3248880
  simp only [CollatzResearch.WordTrace]
  refine ⟨59248194234935049687044047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78997592313246732916058729 59248194234935049687044047)
  ·
    refine ⟨88872291352402574530566071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59248194234935049687044047 88872291352402574530566071)
    ·
      refine ⟨133308437028603861795849107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88872291352402574530566071 133308437028603861795849107)
      ·
        refine ⟨199962655542905792693773661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133308437028603861795849107 199962655542905792693773661)
        ·
          refine ⟨74985995828589672260165123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199962655542905792693773661 74985995828589672260165123)
          ·
            refine ⟨112478993742884508390247685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74985995828589672260165123 112478993742884508390247685)
            ·
              refine ⟨21089811326790845323171441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112478993742884508390247685 21089811326790845323171441)
              ·
                refine ⟨15817358495093133992378581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21089811326790845323171441 15817358495093133992378581)
                ·
                  refine ⟨370719339728745327946373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15817358495093133992378581 370719339728745327946373)
                  ·
                    rfl

theorem cell22_3248880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_3248880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248880 prefixEnd_3248880 := by exact prefixLift 3248880
  have htrace : WordTrace (prefixWord ++ tailWord_3248880) baseStart_3248880 baseEnd_3248880 := by
    simpa [prefixWord, tailWord_3248880, baseEnd_3248880] using wordTrace_append hprefix tailTrace_3248880
  have hstable : (prefixWord ++ tailWord_3248880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248880).length < 2 ^ (prefixWord ++ tailWord_3248880).sum := by decide
  have hdescent : baseEnd_3248880 < baseStart_3248880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248955 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 1, 12]
def baseStart_3248955 : Nat := 118140960795 + 3248955 * 2 ^ 59
def prefixEnd_3248955 : Nat := 4983230072969 + 3 ^ 40 * 3248955 * 2
def baseEnd_3248955 : Nat := 1112183693218960788213889

theorem tailTrace_3248955 : CollatzResearch.WordTrace tailWord_3248955 prefixEnd_3248955 1112183693218960788213889 := by
  unfold tailWord_3248955
  simp only [CollatzResearch.WordTrace]
  refine ⟨118499123944598387183068319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78999415963065591455378879 118499123944598387183068319)
  ·
    refine ⟨177748685916897580774602479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118499123944598387183068319 177748685916897580774602479)
    ·
      refine ⟨266623028875346371161903719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177748685916897580774602479 266623028875346371161903719)
      ·
        refine ⟨399934543313019556742855579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266623028875346371161903719 399934543313019556742855579)
        ·
          refine ⟨599901814969529335114283369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399934543313019556742855579 599901814969529335114283369)
          ·
            refine ⟨449926361227147001335712527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599901814969529335114283369 449926361227147001335712527)
            ·
              refine ⟨674889541840720502003568791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449926361227147001335712527 674889541840720502003568791)
              ·
                refine ⟨1012334312761080753005353187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674889541840720502003568791 1012334312761080753005353187)
                ·
                  refine ⟨1518501469141621129508029781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012334312761080753005353187 1518501469141621129508029781)
                  ·
                    refine ⟨1112183693218960788213889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1518501469141621129508029781 1112183693218960788213889)
                    ·
                      rfl

theorem cell22_3248955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_3248955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248955 prefixEnd_3248955 := by exact prefixLift 3248955
  have htrace : WordTrace (prefixWord ++ tailWord_3248955) baseStart_3248955 baseEnd_3248955 := by
    simpa [prefixWord, tailWord_3248955, baseEnd_3248955] using wordTrace_append hprefix tailTrace_3248955
  have hstable : (prefixWord ++ tailWord_3248955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248955).length < 2 ^ (prefixWord ++ tailWord_3248955).sum := by decide
  have hdescent : baseEnd_3248955 < baseStart_3248955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248959 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 6]
def baseStart_3248959 : Nat := 118140960795 + 3248959 * 2 ^ 59
def prefixEnd_3248959 : Nat := 4983230072969 + 3 ^ 40 * 3248959 * 2
def baseEnd_3248959 : Nat := 370728354166902037037959

theorem tailTrace_3248959 : CollatzResearch.WordTrace tailWord_3248959 prefixEnd_3248959 370728354166902037037959 := by
  unfold tailWord_3248959
  simp only [CollatzResearch.WordTrace]
  refine ⟨118499269836583895866213931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78999513224389263910809287 118499269836583895866213931)
  ·
    refine ⟨177748904754875843799320897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118499269836583895866213931 177748904754875843799320897)
    ·
      refine ⟨133311678566156882849490673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177748904754875843799320897 133311678566156882849490673)
      ·
        refine ⟨99983758924617662137118005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133311678566156882849490673 99983758924617662137118005)
        ·
          refine ⟨9373477399182905825354813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99983758924617662137118005 9373477399182905825354813)
          ·
            refine ⟨3515054024693589684508055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9373477399182905825354813 3515054024693589684508055)
            ·
              refine ⟨5272581037040384526762083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3515054024693589684508055 5272581037040384526762083)
              ·
                refine ⟨7908871555560576790143125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5272581037040384526762083 7908871555560576790143125)
                ·
                  refine ⟨370728354166902037037959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7908871555560576790143125 370728354166902037037959)
                  ·
                    rfl

theorem cell22_3248959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 6].length) (baseStart_3248959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3248959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3248959 prefixEnd_3248959 := by exact prefixLift 3248959
  have htrace : WordTrace (prefixWord ++ tailWord_3248959) baseStart_3248959 baseEnd_3248959 := by
    simpa [prefixWord, tailWord_3248959, baseEnd_3248959] using wordTrace_append hprefix tailTrace_3248959
  have hstable : (prefixWord ++ tailWord_3248959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248959).length < 2 ^ (prefixWord ++ tailWord_3248959).sum := by decide
  have hdescent : baseEnd_3248959 < baseStart_3248959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249017 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 2, 6]
def baseStart_3249017 : Nat := 118140960795 + 3249017 * 2 ^ 59
def prefixEnd_3249017 : Nat := 4983230072969 + 3 ^ 40 * 3249017 * 2
def baseEnd_3249017 : Nat := 1112204917086013293163699

theorem tailTrace_3249017 : CollatzResearch.WordTrace tailWord_3249017 prefixEnd_3249017 1112204917086013293163699 := by
  unfold tailWord_3249017
  simp only [CollatzResearch.WordTrace]
  refine ⟨118501385270373771771825305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79000923513582514514550203 118501385270373771771825305)
  ·
    refine ⟨88876038952780328828868979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118501385270373771771825305 88876038952780328828868979)
    ·
      refine ⟨133314058429170493243303469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88876038952780328828868979 133314058429170493243303469)
      ·
        refine ⟨49992771910938934966238801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133314058429170493243303469 49992771910938934966238801)
        ·
          refine ⟨37494578933204201224679101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49992771910938934966238801 37494578933204201224679101)
          ·
            refine ⟨14060467099951575459254663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37494578933204201224679101 14060467099951575459254663)
            ·
              refine ⟨21090700649927363188881995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14060467099951575459254663 21090700649927363188881995)
              ·
                refine ⟨31636050974891044783322993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21090700649927363188881995 31636050974891044783322993)
                ·
                  refine ⟨23727038231168283587492245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31636050974891044783322993 23727038231168283587492245)
                  ·
                    refine ⟨1112204917086013293163699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23727038231168283587492245 1112204917086013293163699)
                    ·
                      rfl

theorem cell22_3249017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_3249017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249017 prefixEnd_3249017 := by exact prefixLift 3249017
  have htrace : WordTrace (prefixWord ++ tailWord_3249017) baseStart_3249017 baseEnd_3249017 := by
    simpa [prefixWord, tailWord_3249017, baseEnd_3249017] using wordTrace_append hprefix tailTrace_3249017
  have hstable : (prefixWord ++ tailWord_3249017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249017).length < 2 ^ (prefixWord ++ tailWord_3249017).sum := by decide
  have hdescent : baseEnd_3249017 < baseStart_3249017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249047 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 1, 7]
def baseStart_3249047 : Nat := 118140960795 + 3249047 * 2 ^ 59
def prefixEnd_3249047 : Nat := 4983230072969 + 3 ^ 40 * 3249047 * 2
def baseEnd_3249047 : Nat := 1112215186699103214913607

theorem tailTrace_3249047 : CollatzResearch.WordTrace tailWord_3249047 prefixEnd_3249047 1112215186699103214913607 := by
  unfold tailWord_3249047
  simp only [CollatzResearch.WordTrace]
  refine ⟨118502479460265086895417395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79001652973510057930278263 118502479460265086895417395)
  ·
    refine ⟨177753719190397630343126093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118502479460265086895417395 177753719190397630343126093)
    ·
      refine ⟨66657644696399111378672285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177753719190397630343126093 66657644696399111378672285)
      ·
        refine ⟨24996616761149666767002107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66657644696399111378672285 24996616761149666767002107)
        ·
          refine ⟨37494925141724500150503161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24996616761149666767002107 37494925141724500150503161)
          ·
            refine ⟨28121193856293375112877371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37494925141724500150503161 28121193856293375112877371)
            ·
              refine ⟨42181790784440062669316057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28121193856293375112877371 42181790784440062669316057)
              ·
                refine ⟨31636343088330047001987043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42181790784440062669316057 31636343088330047001987043)
                ·
                  refine ⟨47454514632495070502980565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31636343088330047001987043 47454514632495070502980565)
                  ·
                    refine ⟨1112215186699103214913607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47454514632495070502980565 1112215186699103214913607)
                    ·
                      rfl

theorem cell22_3249047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_3249047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249047 prefixEnd_3249047 := by exact prefixLift 3249047
  have htrace : WordTrace (prefixWord ++ tailWord_3249047) baseStart_3249047 baseEnd_3249047 := by
    simpa [prefixWord, tailWord_3249047, baseEnd_3249047] using wordTrace_append hprefix tailTrace_3249047
  have hstable : (prefixWord ++ tailWord_3249047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249047).length < 2 ^ (prefixWord ++ tailWord_3249047).sum := by decide
  have hdescent : baseEnd_3249047 < baseStart_3249047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249053 : List Nat := [1, 4, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_3249053 : Nat := 118140960795 + 3249053 * 2 ^ 59
def prefixEnd_3249053 : Nat := 4983230072969 + 3 ^ 40 * 3249053 * 2
def baseEnd_3249053 : Nat := 1112217240621721199263589

theorem tailTrace_3249053 : CollatzResearch.WordTrace tailWord_3249053 prefixEnd_3249053 1112217240621721199263589 := by
  unfold tailWord_3249053
  simp only [CollatzResearch.WordTrace]
  refine ⟨118502698298243349920135813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79001798865495566613423875 118502698298243349920135813)
  ·
    refine ⟨22219255930920628110025465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118502698298243349920135813 22219255930920628110025465)
    ·
      refine ⟨16664441948190471082519099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22219255930920628110025465 16664441948190471082519099)
      ·
        refine ⟨24996662922285706623778649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16664441948190471082519099 24996662922285706623778649)
        ·
          refine ⟨18747497191714279967833987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24996662922285706623778649 18747497191714279967833987)
          ·
            refine ⟨28121245787571419951750981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18747497191714279967833987 28121245787571419951750981)
            ·
              refine ⟨5272733585169641240953309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28121245787571419951750981 5272733585169641240953309)
              ·
                refine ⟨1977275094438615465357491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5272733585169641240953309 1977275094438615465357491)
                ·
                  refine ⟨2965912641657923198036237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977275094438615465357491 2965912641657923198036237)
                  ·
                    refine ⟨1112217240621721199263589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2965912641657923198036237 1112217240621721199263589)
                    ·
                      rfl

theorem cell22_3249053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_3249053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249053 prefixEnd_3249053 := by exact prefixLift 3249053
  have htrace : WordTrace (prefixWord ++ tailWord_3249053) baseStart_3249053 baseEnd_3249053 := by
    simpa [prefixWord, tailWord_3249053, baseEnd_3249053] using wordTrace_append hprefix tailTrace_3249053
  have hstable : (prefixWord ++ tailWord_3249053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249053).length < 2 ^ (prefixWord ++ tailWord_3249053).sum := by decide
  have hdescent : baseEnd_3249053 < baseStart_3249053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249222 : List Nat := [6, 1, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_3249222 : Nat := 118140960795 + 3249222 * 2 ^ 59
def prefixEnd_3249222 : Nat := 4983230072969 + 3 ^ 40 * 3249222 * 2
def baseEnd_3249222 : Nat := 1112275092775461091788071

theorem tailTrace_3249222 : CollatzResearch.WordTrace tailWord_3249222 prefixEnd_3249222 1112275092775461091788071 := by
  unfold tailWord_3249222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703401944832221618219935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79005908156420727855358613 3703401944832221618219935)
  ·
    refine ⟨5555102917248332427329903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3703401944832221618219935 5555102917248332427329903)
    ·
      refine ⟨8332654375872498640994855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5555102917248332427329903 8332654375872498640994855)
      ·
        refine ⟨12498981563808747961492283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8332654375872498640994855 12498981563808747961492283)
        ·
          refine ⟨18748472345713121942238425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12498981563808747961492283 18748472345713121942238425)
          ·
            refine ⟨14061354259284841456678819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18748472345713121942238425 14061354259284841456678819)
            ·
              refine ⟨21092031388927262185018229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14061354259284841456678819 21092031388927262185018229)
              ·
                refine ⟨1977377942711930829845459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21092031388927262185018229 1977377942711930829845459)
                ·
                  refine ⟨2966066914067896244768189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977377942711930829845459 2966066914067896244768189)
                  ·
                    refine ⟨1112275092775461091788071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2966066914067896244768189 1112275092775461091788071)
                    ·
                      rfl

theorem cell22_3249222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_3249222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249222 prefixEnd_3249222 := by exact prefixLift 3249222
  have htrace : WordTrace (prefixWord ++ tailWord_3249222) baseStart_3249222 baseEnd_3249222 := by
    simpa [prefixWord, tailWord_3249222, baseEnd_3249222] using wordTrace_append hprefix tailTrace_3249222
  have hstable : (prefixWord ++ tailWord_3249222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249222).length < 2 ^ (prefixWord ++ tailWord_3249222).sum := by decide
  have hdescent : baseEnd_3249222 < baseStart_3249222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249276 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_3249276 : Nat := 118140960795 + 3249276 * 2 ^ 59
def prefixEnd_3249276 : Nat := 4983230072969 + 3 ^ 40 * 3249276 * 2
def baseEnd_3249276 : Nat := 1112293578079022950937905

theorem tailTrace_3249276 : CollatzResearch.WordTrace tailWord_3249276 prefixEnd_3249276 1112293578079022950937905 := by
  unfold tailWord_3249276
  simp only [CollatzResearch.WordTrace]
  refine ⟨59255415888217729502751841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79007221184290306003669121 59255415888217729502751841)
  ·
    refine ⟨44441561916163297127063881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59255415888217729502751841 44441561916163297127063881)
    ·
      refine ⟨33331171437122472845297911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44441561916163297127063881 33331171437122472845297911)
      ·
        refine ⟨49996757155683709267946867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33331171437122472845297911 49996757155683709267946867)
        ·
          refine ⟨74995135733525563901920301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49996757155683709267946867 74995135733525563901920301)
          ·
            refine ⟨28123175900072086463220113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74995135733525563901920301 28123175900072086463220113)
            ·
              refine ⟨21092381925054064847415085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28123175900072086463220113 21092381925054064847415085)
              ·
                refine ⟨7909643221895274317780657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21092381925054064847415085 7909643221895274317780657)
                ·
                  refine ⟨5932232416421455738335493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7909643221895274317780657 5932232416421455738335493)
                  ·
                    refine ⟨1112293578079022950937905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5932232416421455738335493 1112293578079022950937905)
                    ·
                      rfl

theorem cell22_3249276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_3249276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249276 prefixEnd_3249276 := by exact prefixLift 3249276
  have htrace : WordTrace (prefixWord ++ tailWord_3249276) baseStart_3249276 baseEnd_3249276 := by
    simpa [prefixWord, tailWord_3249276, baseEnd_3249276] using wordTrace_append hprefix tailTrace_3249276
  have hstable : (prefixWord ++ tailWord_3249276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249276).length < 2 ^ (prefixWord ++ tailWord_3249276).sum := by decide
  have hdescent : baseEnd_3249276 < baseStart_3249276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249368 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 2, 5]
def baseStart_3249368 : Nat := 118140960795 + 3249368 * 2 ^ 59
def prefixEnd_3249368 : Nat := 4983230072969 + 3 ^ 40 * 3249368 * 2
def baseEnd_3249368 : Nat := 1112325071559165377637623

theorem tailTrace_3249368 : CollatzResearch.WordTrace tailWord_3249368 prefixEnd_3249368 1112325071559165377637623 := by
  unfold tailWord_3249368
  simp only [CollatzResearch.WordTrace]
  refine ⟨59257093646051079358926379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79009458194734772478568505 59257093646051079358926379)
  ·
    refine ⟨88885640469076619038389569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59257093646051079358926379 88885640469076619038389569)
    ·
      refine ⟨66664230351807464278792177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88885640469076619038389569 66664230351807464278792177)
      ·
        refine ⟨49998172763855598209094133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66664230351807464278792177 49998172763855598209094133)
        ·
          refine ⟨4687328696611462332102575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49998172763855598209094133 4687328696611462332102575)
          ·
            refine ⟨7030993044917193498153863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4687328696611462332102575 7030993044917193498153863)
            ·
              refine ⟨10546489567375790247230795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030993044917193498153863 10546489567375790247230795)
              ·
                refine ⟨15819734351063685370846193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10546489567375790247230795 15819734351063685370846193)
                ·
                  refine ⟨11864800763297764028134645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15819734351063685370846193 11864800763297764028134645)
                  ·
                    refine ⟨1112325071559165377637623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11864800763297764028134645 1112325071559165377637623)
                    ·
                      rfl

theorem cell22_3249368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_3249368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249368 prefixEnd_3249368 := by exact prefixLift 3249368
  have htrace : WordTrace (prefixWord ++ tailWord_3249368) baseStart_3249368 baseEnd_3249368 := by
    simpa [prefixWord, tailWord_3249368, baseEnd_3249368] using wordTrace_append hprefix tailTrace_3249368
  have hstable : (prefixWord ++ tailWord_3249368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249368).length < 2 ^ (prefixWord ++ tailWord_3249368).sum := by decide
  have hdescent : baseEnd_3249368 < baseStart_3249368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249413 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 4, 3]
def baseStart_3249413 : Nat := 118140960795 + 3249413 * 2 ^ 59
def prefixEnd_3249413 : Nat := 4983230072969 + 3 ^ 40 * 3249413 * 2
def baseEnd_3249413 : Nat := 1112340475978800260262485

theorem tailTrace_3249413 : CollatzResearch.WordTrace tailWord_3249413 prefixEnd_3249413 1112340475978800260262485 := by
  unfold tailWord_3249413
  simp only [CollatzResearch.WordTrace]
  refine ⟨118515828576939131403240893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79010552384626087602160595 118515828576939131403240893)
  ·
    refine ⟨44443435716352174276215335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118515828576939131403240893 44443435716352174276215335)
    ·
      refine ⟨66665153574528261414323003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44443435716352174276215335 66665153574528261414323003)
      ·
        refine ⟨99997730361792392121484505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66665153574528261414323003 99997730361792392121484505)
        ·
          refine ⟨74998297771344294091113379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99997730361792392121484505 74998297771344294091113379)
          ·
            refine ⟨112497446657016441136670069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74998297771344294091113379 112497446657016441136670069)
            ·
              refine ⟨10546635624095291356562819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112497446657016441136670069 10546635624095291356562819)
              ·
                refine ⟨15819953436142937034844229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10546635624095291356562819 15819953436142937034844229)
                ·
                  refine ⟨2966241269276800694033293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15819953436142937034844229 2966241269276800694033293)
                  ·
                    refine ⟨1112340475978800260262485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2966241269276800694033293 1112340475978800260262485)
                    ·
                      rfl

theorem cell22_3249413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_3249413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249413 prefixEnd_3249413 := by exact prefixLift 3249413
  have htrace : WordTrace (prefixWord ++ tailWord_3249413) baseStart_3249413 baseEnd_3249413 := by
    simpa [prefixWord, tailWord_3249413, baseEnd_3249413] using wordTrace_append hprefix tailTrace_3249413
  have hstable : (prefixWord ++ tailWord_3249413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249413).length < 2 ^ (prefixWord ++ tailWord_3249413).sum := by decide
  have hdescent : baseEnd_3249413 < baseStart_3249413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249441 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3249441 : Nat := 118140960795 + 3249441 * 2 ^ 59
def prefixEnd_3249441 : Nat := 4983230072969 + 3 ^ 40 * 3249441 * 2
def baseEnd_3249441 : Nat := 1112350060951017520562399

theorem tailTrace_3249441 : CollatzResearch.WordTrace tailWord_3249441 prefixEnd_3249441 1112350060951017520562399 := by
  unfold tailWord_3249441
  simp only [CollatzResearch.WordTrace]
  refine ⟨118516849820837692185260177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79011233213891794790173451 118516849820837692185260177)
  ·
    refine ⟨88887637365628269138945133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118516849820837692185260177 88887637365628269138945133)
    ·
      refine ⟨33332864012110600927104425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88887637365628269138945133 33332864012110600927104425)
      ·
        refine ⟨24999648009082950695328319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33332864012110600927104425 24999648009082950695328319)
        ·
          refine ⟨37499472013624426042992479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24999648009082950695328319 37499472013624426042992479)
          ·
            refine ⟨56249208020436639064488719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37499472013624426042992479 56249208020436639064488719)
            ·
              refine ⟨84373812030654958596733079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56249208020436639064488719 84373812030654958596733079)
              ·
                refine ⟨126560718045982437895099619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84373812030654958596733079 126560718045982437895099619)
                ·
                  refine ⟨189841077068973656842649429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126560718045982437895099619 189841077068973656842649429)
                  ·
                    refine ⟨1112350060951017520562399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 189841077068973656842649429 1112350060951017520562399)
                    ·
                      rfl

theorem cell22_3249441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3249441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249441 prefixEnd_3249441 := by exact prefixLift 3249441
  have htrace : WordTrace (prefixWord ++ tailWord_3249441) baseStart_3249441 baseEnd_3249441 := by
    simpa [prefixWord, tailWord_3249441, baseEnd_3249441] using wordTrace_append hprefix tailTrace_3249441
  have hstable : (prefixWord ++ tailWord_3249441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249441).length < 2 ^ (prefixWord ++ tailWord_3249441).sum := by decide
  have hdescent : baseEnd_3249441 < baseStart_3249441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249443 : List Nat := [1, 1, 1, 4, 2, 3, 4, 6]
def baseStart_3249443 : Nat := 118140960795 + 3249443 * 2 ^ 59
def prefixEnd_3249443 : Nat := 4983230072969 + 3 ^ 40 * 3249443 * 2
def baseEnd_3249443 : Nat := 123594527287987798001377

theorem tailTrace_3249443 : CollatzResearch.WordTrace tailWord_3249443 prefixEnd_3249443 123594527287987798001377 := by
  unfold tailWord_3249443
  simp only [CollatzResearch.WordTrace]
  refine ⟨118516922766830446526832983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79011281844553631017888655 118516922766830446526832983)
  ·
    refine ⟨177775384150245669790249475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118516922766830446526832983 177775384150245669790249475)
    ·
      refine ⟨266663076225368504685374213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177775384150245669790249475 266663076225368504685374213)
      ·
        refine ⟨49999326792256594628507665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266663076225368504685374213 49999326792256594628507665)
        ·
          refine ⟨37499495094192445971380749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49999326792256594628507665 37499495094192445971380749)
          ·
            refine ⟨14062310660322167239267781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37499495094192445971380749 14062310660322167239267781)
            ·
              refine ⟨2636683248810406357362709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14062310660322167239267781 2636683248810406357362709)
              ·
                refine ⟨123594527287987798001377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2636683248810406357362709 123594527287987798001377)
                ·
                  rfl

theorem cell22_3249443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 6].length) (baseStart_3249443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249443 prefixEnd_3249443 := by exact prefixLift 3249443
  have htrace : WordTrace (prefixWord ++ tailWord_3249443) baseStart_3249443 baseEnd_3249443 := by
    simpa [prefixWord, tailWord_3249443, baseEnd_3249443] using wordTrace_append hprefix tailTrace_3249443
  have hstable : (prefixWord ++ tailWord_3249443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249443).length < 2 ^ (prefixWord ++ tailWord_3249443).sum := by decide
  have hdescent : baseEnd_3249443 < baseStart_3249443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249488 : List Nat := [2, 1, 1, 1, 1, 5, 3, 3, 5]
def baseStart_3249488 : Nat := 118140960795 + 3249488 * 2 ^ 59
def prefixEnd_3249488 : Nat := 4983230072969 + 3 ^ 40 * 3249488 * 2
def baseEnd_3249488 : Nat := 370788716670508354879085

theorem tailTrace_3249488 : CollatzResearch.WordTrace tailWord_3249488 prefixEnd_3249488 370788716670508354879085 := by
  unfold tailWord_3249488
  simp only [CollatzResearch.WordTrace]
  refine ⟨59259282025833709606110559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79012376034444946141480745 59259282025833709606110559)
  ·
    refine ⟨88888923038750564409165839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59259282025833709606110559 88888923038750564409165839)
    ·
      refine ⟨133333384558125846613748759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88888923038750564409165839 133333384558125846613748759)
      ·
        refine ⟨200000076837188769920623139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133333384558125846613748759 200000076837188769920623139)
        ·
          refine ⟨300000115255783154880934709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200000076837188769920623139 300000115255783154880934709)
          ·
            refine ⟨28125010805229670770087629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 300000115255783154880934709 28125010805229670770087629)
            ·
              refine ⟨10546879051961126538782861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28125010805229670770087629 10546879051961126538782861)
              ·
                refine ⟨3955079644485422452043573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10546879051961126538782861 3955079644485422452043573)
                ·
                  refine ⟨370788716670508354879085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3955079644485422452043573 370788716670508354879085)
                  ·
                    rfl

theorem cell22_3249488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_3249488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249488 prefixEnd_3249488 := by exact prefixLift 3249488
  have htrace : WordTrace (prefixWord ++ tailWord_3249488) baseStart_3249488 baseEnd_3249488 := by
    simpa [prefixWord, tailWord_3249488, baseEnd_3249488] using wordTrace_append hprefix tailTrace_3249488
  have hstable : (prefixWord ++ tailWord_3249488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249488).length < 2 ^ (prefixWord ++ tailWord_3249488).sum := by decide
  have hdescent : baseEnd_3249488 < baseStart_3249488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249533 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 6]
def baseStart_3249533 : Nat := 118140960795 + 3249533 * 2 ^ 59
def prefixEnd_3249533 : Nat := 4983230072969 + 3 ^ 40 * 3249533 * 2
def baseEnd_3249533 : Nat := 370793851477053315754039

theorem tailTrace_3249533 : CollatzResearch.WordTrace tailWord_3249533 prefixEnd_3249533 370793851477053315754039 := by
  unfold tailWord_3249533
  simp only [CollatzResearch.WordTrace]
  refine ⟨118520205336504391897609253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79013470224336261265072835 118520205336504391897609253)
  ·
    refine ⟨22222538500594573480801735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118520205336504391897609253 22222538500594573480801735)
    ·
      refine ⟨33333807750891860221202603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22222538500594573480801735 33333807750891860221202603)
      ·
        refine ⟨50000711626337790331803905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33333807750891860221202603 50000711626337790331803905)
        ·
          refine ⟨37500533719753342748852929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50000711626337790331803905 37500533719753342748852929)
          ·
            refine ⟨28125400289815007061639697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37500533719753342748852929 28125400289815007061639697)
            ·
              refine ⟨21094050217361255296229773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28125400289815007061639697 21094050217361255296229773)
              ·
                refine ⟨7910268831510470736086165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21094050217361255296229773 7910268831510470736086165)
                ·
                  refine ⟨370793851477053315754039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7910268831510470736086165 370793851477053315754039)
                  ·
                    rfl

theorem cell22_3249533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_3249533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249533 prefixEnd_3249533 := by exact prefixLift 3249533
  have htrace : WordTrace (prefixWord ++ tailWord_3249533) baseStart_3249533 baseEnd_3249533 := by
    simpa [prefixWord, tailWord_3249533, baseEnd_3249533] using wordTrace_append hprefix tailTrace_3249533
  have hstable : (prefixWord ++ tailWord_3249533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249533).length < 2 ^ (prefixWord ++ tailWord_3249533).sum := by decide
  have hdescent : baseEnd_3249533 < baseStart_3249533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249565 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_3249565 : Nat := 118140960795 + 3249565 * 2 ^ 59
def prefixEnd_3249565 : Nat := 4983230072969 + 3 ^ 40 * 3249565 * 2
def baseEnd_3249565 : Nat := 1112392508685122530462019

theorem tailTrace_3249565 : CollatzResearch.WordTrace tailWord_3249565 prefixEnd_3249565 1112392508685122530462019 := by
  unfold tailWord_3249565
  simp only [CollatzResearch.WordTrace]
  refine ⟨118521372472388461362774149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79014248314925640908516099 118521372472388461362774149)
  ·
    refine ⟨22222757338572836505520153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118521372472388461362774149 22222757338572836505520153)
    ·
      refine ⟨16667068003929627379140115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22222757338572836505520153 16667068003929627379140115)
      ·
        refine ⟨25000602005894441068710173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16667068003929627379140115 25000602005894441068710173)
        ·
          refine ⟨9375225752210415400766315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25000602005894441068710173 9375225752210415400766315)
          ·
            refine ⟨14062838628315623101149473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9375225752210415400766315 14062838628315623101149473)
            ·
              refine ⟨10547128971236717325862105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14062838628315623101149473 10547128971236717325862105)
              ·
                refine ⟨7910346728427537994396579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10547128971236717325862105 7910346728427537994396579)
                ·
                  refine ⟨11865520092641306991594869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7910346728427537994396579 11865520092641306991594869)
                  ·
                    refine ⟨1112392508685122530462019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11865520092641306991594869 1112392508685122530462019)
                    ·
                      rfl

theorem cell22_3249565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_3249565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249565 prefixEnd_3249565 := by exact prefixLift 3249565
  have htrace : WordTrace (prefixWord ++ tailWord_3249565) baseStart_3249565 baseEnd_3249565 := by
    simpa [prefixWord, tailWord_3249565, baseEnd_3249565] using wordTrace_append hprefix tailTrace_3249565
  have hstable : (prefixWord ++ tailWord_3249565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249565).length < 2 ^ (prefixWord ++ tailWord_3249565).sum := by decide
  have hdescent : baseEnd_3249565 < baseStart_3249565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249567 : List Nat := [1, 1, 2, 5, 1, 3, 2, 3, 4]
def baseStart_3249567 : Nat := 118140960795 + 3249567 * 2 ^ 59
def prefixEnd_3249567 : Nat := 4983230072969 + 3 ^ 40 * 3249567 * 2
def baseEnd_3249567 : Nat := 370797731108665063970671

theorem tailTrace_3249567 : CollatzResearch.WordTrace tailWord_3249567 prefixEnd_3249567 370797731108665063970671 := by
  unfold tailWord_3249567
  simp only [CollatzResearch.WordTrace]
  refine ⟨118521445418381215704346955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79014296945587477136231303 118521445418381215704346955)
  ·
    refine ⟨177782168127571823556520433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118521445418381215704346955 177782168127571823556520433)
    ·
      refine ⟨133336626095678867667390325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177782168127571823556520433 133336626095678867667390325)
      ·
        refine ⟨12500308696469893843817843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133336626095678867667390325 12500308696469893843817843)
        ·
          refine ⟨18750463044704840765726765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12500308696469893843817843 18750463044704840765726765)
          ·
            refine ⟨7031423641764315287147537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18750463044704840765726765 7031423641764315287147537)
            ·
              refine ⟨5273567731323236465360653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7031423641764315287147537 5273567731323236465360653)
              ·
                refine ⟨1977587899246213674510245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5273567731323236465360653 1977587899246213674510245)
                ·
                  refine ⟨370797731108665063970671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1977587899246213674510245 370797731108665063970671)
                  ·
                    rfl

theorem cell22_3249567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 4].length) (baseStart_3249567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249567 prefixEnd_3249567 := by exact prefixLift 3249567
  have htrace : WordTrace (prefixWord ++ tailWord_3249567) baseStart_3249567 baseEnd_3249567 := by
    simpa [prefixWord, tailWord_3249567, baseEnd_3249567] using wordTrace_append hprefix tailTrace_3249567
  have hstable : (prefixWord ++ tailWord_3249567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249567).length < 2 ^ (prefixWord ++ tailWord_3249567).sum := by decide
  have hdescent : baseEnd_3249567 < baseStart_3249567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249612 : List Nat := [2, 2, 1, 4, 2, 3, 2, 6]
def baseStart_3249612 : Nat := 118140960795 + 3249612 * 2 ^ 59
def prefixEnd_3249612 : Nat := 4983230072969 + 3 ^ 40 * 3249612 * 2
def baseEnd_3249612 : Nat := 123600955305070008281875

theorem tailTrace_3249612 : CollatzResearch.WordTrace tailWord_3249612 prefixEnd_3249612 123600955305070008281875 := by
  unfold tailWord_3249612
  simp only [CollatzResearch.WordTrace]
  refine ⟨59261543351609094194867545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79015391135478792259823393 59261543351609094194867545)
  ·
    refine ⟨44446157513706820646150659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59261543351609094194867545 44446157513706820646150659)
    ·
      refine ⟨66669236270560230969225989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44446157513706820646150659 66669236270560230969225989)
      ·
        refine ⟨12500481800730043306729873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66669236270560230969225989 12500481800730043306729873)
        ·
          refine ⟨9375361350547532480047405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12500481800730043306729873 9375361350547532480047405)
          ·
            refine ⟨3515760506455324680017777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9375361350547532480047405 3515760506455324680017777)
            ·
              refine ⟨2636820379841493510013333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3515760506455324680017777 2636820379841493510013333)
              ·
                refine ⟨123600955305070008281875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2636820379841493510013333 123600955305070008281875)
                ·
                  rfl

theorem cell22_3249612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 6].length) (baseStart_3249612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249612 prefixEnd_3249612 := by exact prefixLift 3249612
  have htrace : WordTrace (prefixWord ++ tailWord_3249612) baseStart_3249612 baseEnd_3249612 := by
    simpa [prefixWord, tailWord_3249612, baseEnd_3249612] using wordTrace_append hprefix tailTrace_3249612
  have hstable : (prefixWord ++ tailWord_3249612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249612).length < 2 ^ (prefixWord ++ tailWord_3249612).sum := by decide
  have hdescent : baseEnd_3249612 < baseStart_3249612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249640 : List Nat := [2, 1, 4, 1, 1, 2, 2, 4, 5]
def baseStart_3249640 : Nat := 118140960795 + 3249640 * 2 ^ 59
def prefixEnd_3249640 : Nat := 4983230072969 + 3 ^ 40 * 3249640 * 2
def baseEnd_3249640 : Nat := 370806060905949111612263

theorem tailTrace_3249640 : CollatzResearch.WordTrace tailWord_3249640 prefixEnd_3249640 370806060905949111612263 := by
  unfold tailWord_3249640
  simp only [CollatzResearch.WordTrace]
  refine ⟨59262053973558374585877187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79016071964744499447836249 59262053973558374585877187)
  ·
    refine ⟨88893080960337561878815781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59262053973558374585877187 88893080960337561878815781)
    ·
      refine ⟨16667452680063292852277959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88893080960337561878815781 16667452680063292852277959)
      ·
        refine ⟨25001179020094939278416939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16667452680063292852277959 25001179020094939278416939)
        ·
          refine ⟨37501768530142408917625409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25001179020094939278416939 37501768530142408917625409)
          ·
            refine ⟨28126326397606806688219057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37501768530142408917625409 28126326397606806688219057)
            ·
              refine ⟨21094744798205105016164293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28126326397606806688219057 21094744798205105016164293)
              ·
                refine ⟨3955264649663457190530805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21094744798205105016164293 3955264649663457190530805)
                ·
                  refine ⟨370806060905949111612263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3955264649663457190530805 370806060905949111612263)
                  ·
                    rfl

theorem cell22_3249640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_3249640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249640 prefixEnd_3249640 := by exact prefixLift 3249640
  have htrace : WordTrace (prefixWord ++ tailWord_3249640) baseStart_3249640 baseEnd_3249640 := by
    simpa [prefixWord, tailWord_3249640, baseEnd_3249640] using wordTrace_append hprefix tailTrace_3249640
  have hstable : (prefixWord ++ tailWord_3249640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249640).length < 2 ^ (prefixWord ++ tailWord_3249640).sum := by decide
  have hdescent : baseEnd_3249640 < baseStart_3249640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249717 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_3249717 : Nat := 118140960795 + 3249717 * 2 ^ 59
def prefixEnd_3249717 : Nat := 4983230072969 + 3 ^ 40 * 3249717 * 2
def baseEnd_3249717 : Nat := 1112444541391444800661553

theorem tailTrace_3249717 : CollatzResearch.WordTrace tailWord_3249717 prefixEnd_3249717 1112444541391444800661553 := by
  unfold tailWord_3249717
  simp only [CollatzResearch.WordTrace]
  refine ⟨118526916367837791322307405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79017944245225194214871603 118526916367837791322307405)
  ·
    refine ⟨44447593637939171745865277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118526916367837791322307405 44447593637939171745865277)
    ·
      refine ⟨16667847614227189404699479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44447593637939171745865277 16667847614227189404699479)
      ·
        refine ⟨25001771421340784107049219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16667847614227189404699479 25001771421340784107049219)
        ·
          refine ⟨37502657132011176160573829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25001771421340784107049219 37502657132011176160573829)
          ·
            refine ⟨7031748212252095530107593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37502657132011176160573829 7031748212252095530107593)
            ·
              refine ⟨5273811159189071647580695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7031748212252095530107593 5273811159189071647580695)
              ·
                refine ⟨7910716738783607471371043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5273811159189071647580695 7910716738783607471371043)
                ·
                  refine ⟨11866075108175411207056565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7910716738783607471371043 11866075108175411207056565)
                  ·
                    refine ⟨1112444541391444800661553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11866075108175411207056565 1112444541391444800661553)
                    ·
                      rfl

theorem cell22_3249717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_3249717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249717 prefixEnd_3249717 := by exact prefixLift 3249717
  have htrace : WordTrace (prefixWord ++ tailWord_3249717) baseStart_3249717 baseEnd_3249717 := by
    simpa [prefixWord, tailWord_3249717, baseEnd_3249717] using wordTrace_append hprefix tailTrace_3249717
  have hstable : (prefixWord ++ tailWord_3249717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249717).length < 2 ^ (prefixWord ++ tailWord_3249717).sum := by decide
  have hdescent : baseEnd_3249717 < baseStart_3249717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249826 : List Nat := [3, 3, 1, 4, 1, 1, 1, 3, 5]
def baseStart_3249826 : Nat := 118140960795 + 3249826 * 2 ^ 59
def prefixEnd_3249826 : Nat := 4983230072969 + 3 ^ 40 * 3249826 * 2
def baseEnd_3249826 : Nat := 370827284773001616562073

theorem tailTrace_3249826 : CollatzResearch.WordTrace tailWord_3249826 prefixEnd_3249826 370827284773001616562073 := by
  unfold tailWord_3249826
  simp only [CollatzResearch.WordTrace]
  refine ⟨29632722981110725734506333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79020594616295268625350221 29632722981110725734506333)
  ·
    refine ⟨11112271117916522150439875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29632722981110725734506333 11112271117916522150439875)
    ·
      refine ⟨16668406676874783225659813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11112271117916522150439875 16668406676874783225659813)
      ·
        refine ⟨3125326251914021854811215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16668406676874783225659813 3125326251914021854811215)
        ·
          refine ⟨4687989377871032782216823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125326251914021854811215 4687989377871032782216823)
          ·
            refine ⟨7031984066806549173325235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4687989377871032782216823 7031984066806549173325235)
            ·
              refine ⟨10547976100209823759987853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7031984066806549173325235 10547976100209823759987853)
              ·
                refine ⟨3955491037578683909995445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10547976100209823759987853 3955491037578683909995445)
                ·
                  refine ⟨370827284773001616562073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3955491037578683909995445 370827284773001616562073)
                  ·
                    rfl

theorem cell22_3249826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_3249826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249826 prefixEnd_3249826 := by exact prefixLift 3249826
  have htrace : WordTrace (prefixWord ++ tailWord_3249826) baseStart_3249826 baseEnd_3249826 := by
    simpa [prefixWord, tailWord_3249826, baseEnd_3249826] using wordTrace_append hprefix tailTrace_3249826
  have hstable : (prefixWord ++ tailWord_3249826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249826).length < 2 ^ (prefixWord ++ tailWord_3249826).sum := by decide
  have hdescent : baseEnd_3249826 < baseStart_3249826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249837 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3249837 : Nat := 118140960795 + 3249837 * 2 ^ 59
def prefixEnd_3249837 : Nat := 4983230072969 + 3 ^ 40 * 3249837 * 2
def baseEnd_3249837 : Nat := 370828539947934829220395

theorem tailTrace_3249837 : CollatzResearch.WordTrace tailWord_3249837 prefixEnd_3249837 370828539947934829220395 := by
  unfold tailWord_3249837
  simp only [CollatzResearch.WordTrace]
  refine ⟨118531293127403051816675765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79020862084935367877783843 118531293127403051816675765)
  ·
    refine ⟨11112308730694036107813353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118531293127403051816675765 11112308730694036107813353)
    ·
      refine ⟨8334231548020527080860015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11112308730694036107813353 8334231548020527080860015)
      ·
        refine ⟨12501347322030790621290023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8334231548020527080860015 12501347322030790621290023)
        ·
          refine ⟨18752020983046185931935035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12501347322030790621290023 18752020983046185931935035)
          ·
            refine ⟨28128031474569278897902553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18752020983046185931935035 28128031474569278897902553)
            ·
              refine ⟨21096023605926959173426915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28128031474569278897902553 21096023605926959173426915)
              ·
                refine ⟨31644035408890438760140373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21096023605926959173426915 31644035408890438760140373)
                ·
                  refine ⟨370828539947934829220395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31644035408890438760140373 370828539947934829220395)
                  ·
                    rfl

theorem cell22_3249837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3249837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249837 prefixEnd_3249837 := by exact prefixLift 3249837
  have htrace : WordTrace (prefixWord ++ tailWord_3249837) baseStart_3249837 baseEnd_3249837 := by
    simpa [prefixWord, tailWord_3249837, baseEnd_3249837] using wordTrace_append hprefix tailTrace_3249837
  have hstable : (prefixWord ++ tailWord_3249837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249837).length < 2 ^ (prefixWord ++ tailWord_3249837).sum := by decide
  have hdescent : baseEnd_3249837 < baseStart_3249837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249852 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_3249852 : Nat := 118140960795 + 3249852 * 2 ^ 59
def prefixEnd_3249852 : Nat := 4983230072969 + 3 ^ 40 * 3249852 * 2
def baseEnd_3249852 : Nat := 1112490754650349448536139

theorem tailTrace_3249852 : CollatzResearch.WordTrace tailWord_3249852 prefixEnd_3249852 1112490754650349448536139 := by
  unfold tailWord_3249852
  simp only [CollatzResearch.WordTrace]
  refine ⟨59265920111174354689235905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79021226814899139585647873 59265920111174354689235905)
  ·
    refine ⟨44449440083380766016926929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59265920111174354689235905 44449440083380766016926929)
    ·
      refine ⟨33337080062535574512695197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44449440083380766016926929 33337080062535574512695197)
      ·
        refine ⟨12501405023450840442260699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33337080062535574512695197 12501405023450840442260699)
        ·
          refine ⟨18752107535176260663391049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12501405023450840442260699 18752107535176260663391049)
          ·
            refine ⟨14064080651382195497543287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18752107535176260663391049 14064080651382195497543287)
            ·
              refine ⟨21096120977073293246314931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14064080651382195497543287 21096120977073293246314931)
              ·
                refine ⟨31644181465609939869472397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21096120977073293246314931 31644181465609939869472397)
                ·
                  refine ⟨11866568049603727451052149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31644181465609939869472397 11866568049603727451052149)
                  ·
                    refine ⟨1112490754650349448536139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11866568049603727451052149 1112490754650349448536139)
                    ·
                      rfl

theorem cell22_3249852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_3249852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249852 prefixEnd_3249852 := by exact prefixLift 3249852
  have htrace : WordTrace (prefixWord ++ tailWord_3249852) baseStart_3249852 baseEnd_3249852 := by
    simpa [prefixWord, tailWord_3249852, baseEnd_3249852] using wordTrace_append hprefix tailTrace_3249852
  have hstable : (prefixWord ++ tailWord_3249852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249852).length < 2 ^ (prefixWord ++ tailWord_3249852).sum := by decide
  have hdescent : baseEnd_3249852 < baseStart_3249852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249882 : List Nat := [3, 1, 1, 2, 2, 3, 3, 7]
def baseStart_3249882 : Nat := 118140960795 + 3249882 * 2 ^ 59
def prefixEnd_3249882 : Nat := 4983230072969 + 3 ^ 40 * 3249882 * 2
def baseEnd_3249882 : Nat := 123611224918159930031783

theorem tailTrace_3249882 : CollatzResearch.WordTrace tailWord_3249882 prefixEnd_3249882 123611224918159930031783 := by
  unfold tailWord_3249882
  simp only [CollatzResearch.WordTrace]
  refine ⟨29633233603060006125515975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79021956274826683001375933 29633233603060006125515975)
  ·
    refine ⟨44449850404590009188273963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29633233603060006125515975 44449850404590009188273963)
    ·
      refine ⟨66674775606885013782410945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44449850404590009188273963 66674775606885013782410945)
      ·
        refine ⟨50006081705163760336808209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66674775606885013782410945 50006081705163760336808209)
        ·
          refine ⟨37504561278872820252606157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50006081705163760336808209 37504561278872820252606157)
          ·
            refine ⟨14064210479577307594727309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37504561278872820252606157 14064210479577307594727309)
            ·
              refine ⟨5274078929841490348022741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14064210479577307594727309 5274078929841490348022741)
              ·
                refine ⟨123611224918159930031783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5274078929841490348022741 123611224918159930031783)
                ·
                  rfl

theorem cell22_3249882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_3249882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249882 prefixEnd_3249882 := by exact prefixLift 3249882
  have htrace : WordTrace (prefixWord ++ tailWord_3249882) baseStart_3249882 baseEnd_3249882 := by
    simpa [prefixWord, tailWord_3249882, baseEnd_3249882] using wordTrace_append hprefix tailTrace_3249882
  have hstable : (prefixWord ++ tailWord_3249882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249882).length < 2 ^ (prefixWord ++ tailWord_3249882).sum := by decide
  have hdescent : baseEnd_3249882 < baseStart_3249882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249901 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_3249901 : Nat := 118140960795 + 3249901 * 2 ^ 59
def prefixEnd_3249901 : Nat := 4983230072969 + 3 ^ 40 * 3249901 * 2
def baseEnd_3249901 : Nat := 1112507528351729654060989

theorem tailTrace_3249901 : CollatzResearch.WordTrace tailWord_3249901 prefixEnd_3249901 1112507528351729654060989 := by
  unfold tailWord_3249901
  simp only [CollatzResearch.WordTrace]
  refine ⟨118533627399171190747005557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79022418266114127164670371 118533627399171190747005557)
  ·
    refine ⟨11112527568672299132531771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118533627399171190747005557 11112527568672299132531771)
    ·
      refine ⟨16668791353008448698797657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11112527568672299132531771 16668791353008448698797657)
      ·
        refine ⟨12501593514756336524098243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16668791353008448698797657 12501593514756336524098243)
        ·
          refine ⟨18752390272134504786147365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12501593514756336524098243 18752390272134504786147365)
          ·
            refine ⟨3516073176025219647402631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18752390272134504786147365 3516073176025219647402631)
            ·
              refine ⟨5274109764037829471103947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3516073176025219647402631 5274109764037829471103947)
              ·
                refine ⟨7911164646056744206655921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5274109764037829471103947 7911164646056744206655921)
                ·
                  refine ⟨5933373484542558154991941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7911164646056744206655921 5933373484542558154991941)
                  ·
                    refine ⟨1112507528351729654060989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5933373484542558154991941 1112507528351729654060989)
                    ·
                      rfl

theorem cell22_3249901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_3249901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249901 prefixEnd_3249901 := by exact prefixLift 3249901
  have htrace : WordTrace (prefixWord ++ tailWord_3249901) baseStart_3249901 baseEnd_3249901 := by
    simpa [prefixWord, tailWord_3249901, baseEnd_3249901] using wordTrace_append hprefix tailTrace_3249901
  have hstable : (prefixWord ++ tailWord_3249901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249901).length < 2 ^ (prefixWord ++ tailWord_3249901).sum := by decide
  have hdescent : baseEnd_3249901 < baseStart_3249901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249931 : List Nat := [1, 1, 1, 1, 5, 1, 4, 4, 1, 3]
def baseStart_3249931 : Nat := 118140960795 + 3249931 * 2 ^ 59
def prefixEnd_3249931 : Nat := 4983230072969 + 3 ^ 40 * 3249931 * 2
def baseEnd_3249931 : Nat := 1112517797964819575810897

theorem tailTrace_3249931 : CollatzResearch.WordTrace tailWord_3249931 prefixEnd_3249931 1112517797964819575810897 := by
  unfold tailWord_3249931
  simp only [CollatzResearch.WordTrace]
  refine ⟨118534721589062505870597647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79023147726041670580398431 118534721589062505870597647)
  ·
    refine ⟨177802082383593758805896471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118534721589062505870597647 177802082383593758805896471)
    ·
      refine ⟨266703123575390638208844707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177802082383593758805896471 266703123575390638208844707)
      ·
        refine ⟨400054685363085957313267061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266703123575390638208844707 400054685363085957313267061)
        ·
          refine ⟨37505126752789308498118787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 400054685363085957313267061 37505126752789308498118787)
          ·
            refine ⟨56257690129183962747178181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37505126752789308498118787 56257690129183962747178181)
            ·
              refine ⟨10548316899221993015095909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56257690129183962747178181 10548316899221993015095909)
              ·
                refine ⟨1977809418604123690330483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10548316899221993015095909 1977809418604123690330483)
                ·
                  refine ⟨2966714127906185535495725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977809418604123690330483 2966714127906185535495725)
                  ·
                    refine ⟨1112517797964819575810897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2966714127906185535495725 1112517797964819575810897)
                    ·
                      rfl

theorem cell22_3249931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 1, 3].length) (baseStart_3249931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249931 prefixEnd_3249931 := by exact prefixLift 3249931
  have htrace : WordTrace (prefixWord ++ tailWord_3249931) baseStart_3249931 baseEnd_3249931 := by
    simpa [prefixWord, tailWord_3249931, baseEnd_3249931] using wordTrace_append hprefix tailTrace_3249931
  have hstable : (prefixWord ++ tailWord_3249931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249931).length < 2 ^ (prefixWord ++ tailWord_3249931).sum := by decide
  have hdescent : baseEnd_3249931 < baseStart_3249931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249950 : List Nat := [4, 3, 2, 2, 1, 2, 2, 6]
def baseStart_3249950 : Nat := 118140960795 + 3249950 * 2 ^ 59
def prefixEnd_3249950 : Nat := 4983230072969 + 3 ^ 40 * 3249950 * 2
def baseEnd_3249950 : Nat := 123613811339234428842871

theorem tailTrace_3249950 : CollatzResearch.WordTrace tailWord_3249950 prefixEnd_3249950 123613811339234428842871 := by
  unfold tailWord_3249950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14816926821999209014442413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79023609717329114743692869 14816926821999209014442413)
  ·
    refine ⟨5556347558249703380415905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14816926821999209014442413 5556347558249703380415905)
    ·
      refine ⟨4167260668687277535311929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5556347558249703380415905 4167260668687277535311929)
      ·
        refine ⟨3125445501515458151483947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4167260668687277535311929 3125445501515458151483947)
        ·
          refine ⟨4688168252273187227225921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125445501515458151483947 4688168252273187227225921)
          ·
            refine ⟨3516126189204890420419441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4688168252273187227225921 3516126189204890420419441)
            ·
              refine ⟨2637094641903667815314581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3516126189204890420419441 2637094641903667815314581)
              ·
                refine ⟨123613811339234428842871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2637094641903667815314581 123613811339234428842871)
                ·
                  rfl

theorem cell22_3249950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_3249950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3249950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3249950 prefixEnd_3249950 := by exact prefixLift 3249950
  have htrace : WordTrace (prefixWord ++ tailWord_3249950) baseStart_3249950 baseEnd_3249950 := by
    simpa [prefixWord, tailWord_3249950, baseEnd_3249950] using wordTrace_append hprefix tailTrace_3249950
  have hstable : (prefixWord ++ tailWord_3249950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249950).length < 2 ^ (prefixWord ++ tailWord_3249950).sum := by decide
  have hdescent : baseEnd_3249950 < baseStart_3249950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250017 : List Nat := [1, 2, 3, 1, 1, 1, 3, 10]
def baseStart_3250017 : Nat := 118140960795 + 3250017 * 2 ^ 59
def prefixEnd_3250017 : Nat := 4983230072969 + 3 ^ 40 * 3250017 * 2
def baseEnd_3250017 : Nat := 123616359724704890906737

theorem tailTrace_3250017 : CollatzResearch.WordTrace tailWord_3250017 prefixEnd_3250017 123616359724704890906737 := by
  unfold tailWord_3250017
  simp only [CollatzResearch.WordTrace]
  refine ⟨118537858266750942558228305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79025238844500628372152203 118537858266750942558228305)
  ·
    refine ⟨88903393700063206918671229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118537858266750942558228305 88903393700063206918671229)
    ·
      refine ⟨33338772637523702594501711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88903393700063206918671229 33338772637523702594501711)
      ·
        refine ⟨50008158956285553891752567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33338772637523702594501711 50008158956285553891752567)
        ·
          refine ⟨75012238434428330837628851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50008158956285553891752567 75012238434428330837628851)
          ·
            refine ⟨112518357651642496256443277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75012238434428330837628851 112518357651642496256443277)
            ·
              refine ⟨42194384119365936096166229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112518357651642496256443277 42194384119365936096166229)
              ·
                refine ⟨123616359724704890906737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42194384119365936096166229 123616359724704890906737)
                ·
                  rfl

theorem cell22_3250017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 10].length) (baseStart_3250017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250017 prefixEnd_3250017 := by exact prefixLift 3250017
  have htrace : WordTrace (prefixWord ++ tailWord_3250017) baseStart_3250017 baseEnd_3250017 := by
    simpa [prefixWord, tailWord_3250017, baseEnd_3250017] using wordTrace_append hprefix tailTrace_3250017
  have hstable : (prefixWord ++ tailWord_3250017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250017).length < 2 ^ (prefixWord ++ tailWord_3250017).sum := by decide
  have hdescent : baseEnd_3250017 < baseStart_3250017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250070 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3250070 : Nat := 118140960795 + 3250070 * 2 ^ 59
def prefixEnd_3250070 : Nat := 4983230072969 + 3 ^ 40 * 3250070 * 2
def baseEnd_3250070 : Nat := 1112565380505469546585471

theorem tailTrace_3250070 : CollatzResearch.WordTrace tailWord_3250070 prefixEnd_3250070 1112565380505469546585471 := by
  unfold tailWord_3250070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7408736958472433288119229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79026527557039288406605109 7408736958472433288119229)
  ·
    refine ⟨2778276359427162483044711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7408736958472433288119229 2778276359427162483044711)
    ·
      refine ⟨4167414539140743724567067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2778276359427162483044711 4167414539140743724567067)
      ·
        refine ⟨6251121808711115586850601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4167414539140743724567067 6251121808711115586850601)
        ·
          refine ⟨4688341356533336690137951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6251121808711115586850601 4688341356533336690137951)
          ·
            refine ⟨7032512034800005035206927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4688341356533336690137951 7032512034800005035206927)
            ·
              refine ⟨10548768052200007552810391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7032512034800005035206927 10548768052200007552810391)
              ·
                refine ⟨15823152078300011329215587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10548768052200007552810391 15823152078300011329215587)
                ·
                  refine ⟨23734728117450016993823381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15823152078300011329215587 23734728117450016993823381)
                  ·
                    refine ⟨1112565380505469546585471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23734728117450016993823381 1112565380505469546585471)
                    ·
                      rfl

theorem cell22_3250070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3250070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250070 prefixEnd_3250070 := by exact prefixLift 3250070
  have htrace : WordTrace (prefixWord ++ tailWord_3250070) baseStart_3250070 baseEnd_3250070 := by
    simpa [prefixWord, tailWord_3250070, baseEnd_3250070] using wordTrace_append hprefix tailTrace_3250070
  have hstable : (prefixWord ++ tailWord_3250070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250070).length < 2 ^ (prefixWord ++ tailWord_3250070).sum := by decide
  have hdescent : baseEnd_3250070 < baseStart_3250070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250134 : List Nat := [5, 2, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3250134 : Nat := 118140960795 + 3250134 * 2 ^ 59
def prefixEnd_3250134 : Nat := 4983230072969 + 3 ^ 40 * 3250134 * 2
def baseEnd_3250134 : Nat := 1112587289013394712985275

theorem tailTrace_3250134 : CollatzResearch.WordTrace tailWord_3250134 prefixEnd_3250134 1112587289013394712985275 := by
  unfold tailWord_3250134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7408882850457941971264841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79028083738218047693491637 7408882850457941971264841)
  ·
    refine ⟨5556662137843456478448631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7408882850457941971264841 5556662137843456478448631)
    ·
      refine ⟨8334993206765184717672947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5556662137843456478448631 8334993206765184717672947)
      ·
        refine ⟨12502489810147777076509421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8334993206765184717672947 12502489810147777076509421)
        ·
          refine ⟨4688433678805416403691033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12502489810147777076509421 4688433678805416403691033)
          ·
            refine ⟨3516325259104062302768275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4688433678805416403691033 3516325259104062302768275)
            ·
              refine ⟨5274487888656093454152413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3516325259104062302768275 5274487888656093454152413)
              ·
                refine ⟨1977932958246035045307155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5274487888656093454152413 1977932958246035045307155)
                ·
                  refine ⟨2966899437369052567960733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977932958246035045307155 2966899437369052567960733)
                  ·
                    refine ⟨1112587289013394712985275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2966899437369052567960733 1112587289013394712985275)
                    ·
                      rfl

theorem cell22_3250134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3250134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250134 prefixEnd_3250134 := by exact prefixLift 3250134
  have htrace : WordTrace (prefixWord ++ tailWord_3250134) baseStart_3250134 baseEnd_3250134 := by
    simpa [prefixWord, tailWord_3250134, baseEnd_3250134] using wordTrace_append hprefix tailTrace_3250134
  have hstable : (prefixWord ++ tailWord_3250134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250134).length < 2 ^ (prefixWord ++ tailWord_3250134).sum := by decide
  have hdescent : baseEnd_3250134 < baseStart_3250134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250158 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_3250158 : Nat := 118140960795 + 3250158 * 2 ^ 59
def prefixEnd_3250158 : Nat := 4983230072969 + 3 ^ 40 * 3250158 * 2
def baseEnd_3250158 : Nat := 370865168234622216795067

theorem tailTrace_3250158 : CollatzResearch.WordTrace tailWord_3250158 prefixEnd_3250158 370865168234622216795067 := by
  unfold tailWord_3250158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14817875119905015454888891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79028667306160082426074085 14817875119905015454888891)
  ·
    refine ⟨22226812679857523182333337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14817875119905015454888891 22226812679857523182333337)
    ·
      refine ⟨16670109509893142386750003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22226812679857523182333337 16670109509893142386750003)
      ·
        refine ⟨25005164264839713580125005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16670109509893142386750003 25005164264839713580125005)
        ·
          refine ⟨9376936599314892592546877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25005164264839713580125005 9376936599314892592546877)
          ·
            refine ⟨3516351224743084722205079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9376936599314892592546877 3516351224743084722205079)
            ·
              refine ⟨5274526837114627083307619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3516351224743084722205079 5274526837114627083307619)
              ·
                refine ⟨7911790255671940624961429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5274526837114627083307619 7911790255671940624961429)
                ·
                  refine ⟨370865168234622216795067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7911790255671940624961429 370865168234622216795067)
                  ·
                    rfl

theorem cell22_3250158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_3250158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250158 prefixEnd_3250158 := by exact prefixLift 3250158
  have htrace : WordTrace (prefixWord ++ tailWord_3250158) baseStart_3250158 baseEnd_3250158 := by
    simpa [prefixWord, tailWord_3250158, baseEnd_3250158] using wordTrace_append hprefix tailTrace_3250158
  have hstable : (prefixWord ++ tailWord_3250158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250158).length < 2 ^ (prefixWord ++ tailWord_3250158).sum := by decide
  have hdescent : baseEnd_3250158 < baseStart_3250158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250169 : List Nat := [1, 2, 1, 3, 1, 4, 1, 9]
def baseStart_3250169 : Nat := 118140960795 + 3250169 * 2 ^ 59
def prefixEnd_3250169 : Nat := 4983230072969 + 3 ^ 40 * 3250169 * 2
def baseEnd_3250169 : Nat := 123622141136518476484463

theorem tailTrace_3250169 : CollatzResearch.WordTrace tailWord_3250169 prefixEnd_3250169 123622141136518476484463 := by
  unfold tailWord_3250169
  simp only [CollatzResearch.WordTrace]
  refine ⟨118543402162200272517761561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79028934774800181678507707 118543402162200272517761561)
  ·
    refine ⟨88907551621650204388321171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118543402162200272517761561 88907551621650204388321171)
    ·
      refine ⟨133361327432475306582481757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88907551621650204388321171 133361327432475306582481757)
      ·
        refine ⟨50010497787178239968430659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133361327432475306582481757 50010497787178239968430659)
        ·
          refine ⟨75015746680767359952645989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50010497787178239968430659 75015746680767359952645989)
          ·
            refine ⟨14065452502643879991121123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75015746680767359952645989 14065452502643879991121123)
            ·
              refine ⟨21098178753965819986681685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14065452502643879991121123 21098178753965819986681685)
              ·
                refine ⟨123622141136518476484463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21098178753965819986681685 123622141136518476484463)
                ·
                  rfl

theorem cell22_3250169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 9].length) (baseStart_3250169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250169 prefixEnd_3250169 := by exact prefixLift 3250169
  have htrace : WordTrace (prefixWord ++ tailWord_3250169) baseStart_3250169 baseEnd_3250169 := by
    simpa [prefixWord, tailWord_3250169, baseEnd_3250169] using wordTrace_append hprefix tailTrace_3250169
  have hstable : (prefixWord ++ tailWord_3250169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250169).length < 2 ^ (prefixWord ++ tailWord_3250169).sum := by decide
  have hdescent : baseEnd_3250169 < baseStart_3250169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250231 : List Nat := [1, 1, 3, 1, 2, 2, 4, 3, 5]
def baseStart_3250231 : Nat := 118140960795 + 3250231 * 2 ^ 59
def prefixEnd_3250231 : Nat := 4983230072969 + 3 ^ 40 * 3250231 * 2
def baseEnd_3250231 : Nat := 370873498031906264436659

theorem tailTrace_3250231 : CollatzResearch.WordTrace tailWord_3250231 prefixEnd_3250231 370873498031906264436659 := by
  unfold tailWord_3250231
  simp only [CollatzResearch.WordTrace]
  refine ⟨118545663487975657106518547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79030442325317104737679031 118545663487975657106518547)
  ·
    refine ⟨177818495231963485659777821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118545663487975657106518547 177818495231963485659777821)
    ·
      refine ⟨66681935711986307122416683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177818495231963485659777821 66681935711986307122416683)
      ·
        refine ⟨100022903567979460683625025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66681935711986307122416683 100022903567979460683625025)
        ·
          refine ⟨75017177675984595512718769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100022903567979460683625025 75017177675984595512718769)
          ·
            refine ⟨56262883256988446634539077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75017177675984595512718769 56262883256988446634539077)
            ·
              refine ⟨10549290610685333743976077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56262883256988446634539077 10549290610685333743976077)
              ·
                refine ⟨3955983979007000153991029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10549290610685333743976077 3955983979007000153991029)
                ·
                  refine ⟨370873498031906264436659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3955983979007000153991029 370873498031906264436659)
                  ·
                    rfl

theorem cell22_3250231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 5].length) (baseStart_3250231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250231 prefixEnd_3250231 := by exact prefixLift 3250231
  have htrace : WordTrace (prefixWord ++ tailWord_3250231) baseStart_3250231 baseEnd_3250231 := by
    simpa [prefixWord, tailWord_3250231, baseEnd_3250231] using wordTrace_append hprefix tailTrace_3250231
  have hstable : (prefixWord ++ tailWord_3250231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250231).length < 2 ^ (prefixWord ++ tailWord_3250231).sum := by decide
  have hdescent : baseEnd_3250231 < baseStart_3250231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250276 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 6]
def baseStart_3250276 : Nat := 118140960795 + 3250276 * 2 ^ 59
def prefixEnd_3250276 : Nat := 4983230072969 + 3 ^ 40 * 3250276 * 2
def baseEnd_3250276 : Nat := 370878632838451225311613

theorem tailTrace_3250276 : CollatzResearch.WordTrace tailWord_3250276 prefixEnd_3250276 370878632838451225311613 := by
  unfold tailWord_3250276
  simp only [CollatzResearch.WordTrace]
  refine ⟨59273652386406314895953341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79031536515208419861271121 59273652386406314895953341)
  ·
    refine ⟨22227619644902368085982503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59273652386406314895953341 22227619644902368085982503)
    ·
      refine ⟨33341429467353552128973755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22227619644902368085982503 33341429467353552128973755)
      ·
        refine ⟨50012144201030328193460633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33341429467353552128973755 50012144201030328193460633)
        ·
          refine ⟨37509108150772746145095475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50012144201030328193460633 37509108150772746145095475)
          ·
            refine ⟨56263662226159119217643213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37509108150772746145095475 56263662226159119217643213)
            ·
              refine ⟨21098873334809669706616205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56263662226159119217643213 21098873334809669706616205)
              ·
                refine ⟨7912077500553626139981077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21098873334809669706616205 7912077500553626139981077)
                ·
                  refine ⟨370878632838451225311613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7912077500553626139981077 370878632838451225311613)
                  ·
                    rfl

theorem cell22_3250276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_3250276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250276 prefixEnd_3250276 := by exact prefixLift 3250276
  have htrace : WordTrace (prefixWord ++ tailWord_3250276) baseStart_3250276 baseEnd_3250276 := by
    simpa [prefixWord, tailWord_3250276, baseEnd_3250276] using wordTrace_append hprefix tailTrace_3250276
  have hstable : (prefixWord ++ tailWord_3250276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250276).length < 2 ^ (prefixWord ++ tailWord_3250276).sum := by decide
  have hdescent : baseEnd_3250276 < baseStart_3250276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250308 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_3250308 : Nat := 118140960795 + 3250308 * 2 ^ 59
def prefixEnd_3250308 : Nat := 4983230072969 + 3 ^ 40 * 3250308 * 2
def baseEnd_3250308 : Nat := 1112646852769316259134741

theorem tailTrace_3250308 : CollatzResearch.WordTrace tailWord_3250308 prefixEnd_3250308 1112646852769316259134741 := by
  unfold tailWord_3250308
  simp only [CollatzResearch.WordTrace]
  refine ⟨59274235954348349628535789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79032314605797799504714385 59274235954348349628535789)
  ·
    refine ⟨22227838482880631110700921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59274235954348349628535789 22227838482880631110700921)
    ·
      refine ⟨16670878862160473333025691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22227838482880631110700921 16670878862160473333025691)
      ·
        refine ⟨25006318293240709999538537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16670878862160473333025691 25006318293240709999538537)
        ·
          refine ⟨18754738719930532499653903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25006318293240709999538537 18754738719930532499653903)
          ·
            refine ⟨28132108079895798749480855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18754738719930532499653903 28132108079895798749480855)
            ·
              refine ⟨42198162119843698124221283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28132108079895798749480855 42198162119843698124221283)
              ·
                refine ⟨63297243179765547186331925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42198162119843698124221283 63297243179765547186331925)
                ·
                  refine ⟨2967058274051510024359309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63297243179765547186331925 2967058274051510024359309)
                  ·
                    refine ⟨1112646852769316259134741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2967058274051510024359309 1112646852769316259134741)
                    ·
                      rfl

theorem cell22_3250308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_3250308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250308 prefixEnd_3250308 := by exact prefixLift 3250308
  have htrace : WordTrace (prefixWord ++ tailWord_3250308) baseStart_3250308 baseEnd_3250308 := by
    simpa [prefixWord, tailWord_3250308, baseEnd_3250308] using wordTrace_append hprefix tailTrace_3250308
  have hstable : (prefixWord ++ tailWord_3250308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250308).length < 2 ^ (prefixWord ++ tailWord_3250308).sum := by decide
  have hdescent : baseEnd_3250308 < baseStart_3250308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250327 : List Nat := [1, 1, 3, 3, 4, 1, 3, 2, 4]
def baseStart_3250327 : Nat := 118140960795 + 3250327 * 2 ^ 59
def prefixEnd_3250327 : Nat := 4983230072969 + 3 ^ 40 * 3250327 * 2
def baseEnd_3250327 : Nat := 370884452285868847636561

theorem tailTrace_3250327 : CollatzResearch.WordTrace tailWord_3250327 prefixEnd_3250327 370884452285868847636561 := by
  unfold tailWord_3250327
  simp only [CollatzResearch.WordTrace]
  refine ⟨118549164895627865502013235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79032776597085243668008823 118549164895627865502013235)
  ·
    refine ⟨177823747343441798253019853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118549164895627865502013235 177823747343441798253019853)
    ·
      refine ⟨66683905253790674344882445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177823747343441798253019853 66683905253790674344882445)
      ·
        refine ⟨25006464470171502879330917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66683905253790674344882445 25006464470171502879330917)
        ·
          refine ⟨4688712088157156789874547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25006464470171502879330917 4688712088157156789874547)
          ·
            refine ⟨7033068132235735184811821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4688712088157156789874547 7033068132235735184811821)
            ·
              refine ⟨2637400549588400694304433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7033068132235735184811821 2637400549588400694304433)
              ·
                refine ⟨1978050412191300520728325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2637400549588400694304433 1978050412191300520728325)
                ·
                  refine ⟨370884452285868847636561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978050412191300520728325 370884452285868847636561)
                  ·
                    rfl

theorem cell22_3250327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 4].length) (baseStart_3250327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250327 prefixEnd_3250327 := by exact prefixLift 3250327
  have htrace : WordTrace (prefixWord ++ tailWord_3250327) baseStart_3250327 baseEnd_3250327 := by
    simpa [prefixWord, tailWord_3250327, baseEnd_3250327] using wordTrace_append hprefix tailTrace_3250327
  have hstable : (prefixWord ++ tailWord_3250327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250327).length < 2 ^ (prefixWord ++ tailWord_3250327).sum := by decide
  have hdescent : baseEnd_3250327 < baseStart_3250327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250338 : List Nat := [3, 3, 1, 3, 1, 1, 1, 9]
def baseStart_3250338 : Nat := 118140960795 + 3250338 * 2 ^ 59
def prefixEnd_3250338 : Nat := 4983230072969 + 3 ^ 40 * 3250338 * 2
def baseEnd_3250338 : Nat := 123628569153600686764961

theorem tailTrace_3250338 : CollatzResearch.WordTrace tailWord_3250338 prefixEnd_3250338 123628569153600686764961 := by
  unfold tailWord_3250338
  simp only [CollatzResearch.WordTrace]
  refine ⟨29637391524647003595165917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79033044065725342920442445 29637391524647003595165917)
  ·
    refine ⟨11114021821742626348187219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29637391524647003595165917 11114021821742626348187219)
    ·
      refine ⟨16671032732613939522280829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11114021821742626348187219 16671032732613939522280829)
      ·
        refine ⟨6251637274730227320855311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16671032732613939522280829 6251637274730227320855311)
        ·
          refine ⟨9377455912095340981282967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6251637274730227320855311 9377455912095340981282967)
          ·
            refine ⟨14066183868143011471924451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9377455912095340981282967 14066183868143011471924451)
            ·
              refine ⟨21099275802214517207886677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14066183868143011471924451 21099275802214517207886677)
              ·
                refine ⟨123628569153600686764961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21099275802214517207886677 123628569153600686764961)
                ·
                  rfl

theorem cell22_3250338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_3250338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250338 prefixEnd_3250338 := by exact prefixLift 3250338
  have htrace : WordTrace (prefixWord ++ tailWord_3250338) baseStart_3250338 baseEnd_3250338 := by
    simpa [prefixWord, tailWord_3250338, baseEnd_3250338] using wordTrace_append hprefix tailTrace_3250338
  have hstable : (prefixWord ++ tailWord_3250338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250338).length < 2 ^ (prefixWord ++ tailWord_3250338).sum := by decide
  have hdescent : baseEnd_3250338 < baseStart_3250338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250357 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 2, 4]
def baseStart_3250357 : Nat := 118140960795 + 3250357 * 2 ^ 59
def prefixEnd_3250357 : Nat := 4983230072969 + 3 ^ 40 * 3250357 * 2
def baseEnd_3250357 : Nat := 1112663626470696464659591

theorem tailTrace_3250357 : CollatzResearch.WordTrace tailWord_3250357 prefixEnd_3250357 1112663626470696464659591 := by
  unfold tailWord_3250357
  simp only [CollatzResearch.WordTrace]
  refine ⟨118550259085519180625605325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79033506057012787083736883 118550259085519180625605325)
  ·
    refine ⟨44456347157069692734601997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118550259085519180625605325 44456347157069692734601997)
    ·
      refine ⟨16671130183901134775475749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44456347157069692734601997 16671130183901134775475749)
      ·
        refine ⟨3125836909481462770401703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16671130183901134775475749 3125836909481462770401703)
        ·
          refine ⟨4688755364222194155602555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125836909481462770401703 4688755364222194155602555)
          ·
            refine ⟨7033133046333291233403833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4688755364222194155602555 7033133046333291233403833)
            ·
              refine ⟨5274849784749968425052875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7033133046333291233403833 5274849784749968425052875)
              ·
                refine ⟨7912274677124952637579313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5274849784749968425052875 7912274677124952637579313)
                ·
                  refine ⟨5934206007843714478184485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7912274677124952637579313 5934206007843714478184485)
                  ·
                    refine ⟨1112663626470696464659591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5934206007843714478184485 1112663626470696464659591)
                    ·
                      rfl

theorem cell22_3250357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_3250357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250357 prefixEnd_3250357 := by exact prefixLift 3250357
  have htrace : WordTrace (prefixWord ++ tailWord_3250357) baseStart_3250357 baseEnd_3250357 := by
    simpa [prefixWord, tailWord_3250357, baseEnd_3250357] using wordTrace_append hprefix tailTrace_3250357
  have hstable : (prefixWord ++ tailWord_3250357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250357).length < 2 ^ (prefixWord ++ tailWord_3250357).sum := by decide
  have hdescent : baseEnd_3250357 < baseStart_3250357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250383 : List Nat := [1, 1, 2, 1, 1, 3, 6, 2, 5]
def baseStart_3250383 : Nat := 118140960795 + 3250383 * 2 ^ 59
def prefixEnd_3250383 : Nat := 4983230072969 + 3 ^ 40 * 3250383 * 2
def baseEnd_3250383 : Nat := 370890842267347021169837

theorem tailTrace_3250383 : CollatzResearch.WordTrace tailWord_3250383 prefixEnd_3250383 370890842267347021169837 := by
  unfold tailWord_3250383
  simp only [CollatzResearch.WordTrace]
  refine ⟨118551207383424987066051803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79034138255616658044034535 118551207383424987066051803)
  ·
    refine ⟨177826811075137480599077705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118551207383424987066051803 177826811075137480599077705)
    ·
      refine ⟨133370108306353110449308279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177826811075137480599077705 133370108306353110449308279)
      ·
        refine ⟨200055162459529665673962419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133370108306353110449308279 200055162459529665673962419)
        ·
          refine ⟨300082743689294498510943629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200055162459529665673962419 300082743689294498510943629)
          ·
            refine ⟨112531028883485436941603861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300082743689294498510943629 112531028883485436941603861)
            ·
              refine ⟨5274891978913379856637681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112531028883485436941603861 5274891978913379856637681)
              ·
                refine ⟨3956168984185034892478261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5274891978913379856637681 3956168984185034892478261)
                ·
                  refine ⟨370890842267347021169837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3956168984185034892478261 370890842267347021169837)
                  ·
                    rfl

theorem cell22_3250383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 5].length) (baseStart_3250383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250383 prefixEnd_3250383 := by exact prefixLift 3250383
  have htrace : WordTrace (prefixWord ++ tailWord_3250383) baseStart_3250383 baseEnd_3250383 := by
    simpa [prefixWord, tailWord_3250383, baseEnd_3250383] using wordTrace_append hprefix tailTrace_3250383
  have hstable : (prefixWord ++ tailWord_3250383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250383).length < 2 ^ (prefixWord ++ tailWord_3250383).sum := by decide
  have hdescent : baseEnd_3250383 < baseStart_3250383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250462 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3250462 : Nat := 118140960795 + 3250462 * 2 ^ 59
def prefixEnd_3250462 : Nat := 4983230072969 + 3 ^ 40 * 3250462 * 2
def baseEnd_3250462 : Nat := 370899856705503730261423

theorem tailTrace_3250462 : CollatzResearch.WordTrace tailWord_3250462 prefixEnd_3250462 370899856705503730261423 := by
  unfold tailWord_3250462
  simp only [CollatzResearch.WordTrace]
  refine ⟨14819261093767347944772205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79036059166759189038785093 14819261093767347944772205)
  ·
    refine ⟨5557222910162755479289577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14819261093767347944772205 5557222910162755479289577)
    ·
      refine ⟨4167917182622066609467183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5557222910162755479289577 4167917182622066609467183)
      ·
        refine ⟨6251875773933099914200775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4167917182622066609467183 6251875773933099914200775)
        ·
          refine ⟨9377813660899649871301163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6251875773933099914200775 9377813660899649871301163)
          ·
            refine ⟨14066720491349474806951745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9377813660899649871301163 14066720491349474806951745)
            ·
              refine ⟨10550040368512106105213809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14066720491349474806951745 10550040368512106105213809)
              ·
                refine ⟨7912530276384079578910357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10550040368512106105213809 7912530276384079578910357)
                ·
                  refine ⟨370899856705503730261423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7912530276384079578910357 370899856705503730261423)
                  ·
                    rfl

theorem cell22_3250462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3250462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250462 prefixEnd_3250462 := by exact prefixLift 3250462
  have htrace : WordTrace (prefixWord ++ tailWord_3250462) baseStart_3250462 baseEnd_3250462 := by
    simpa [prefixWord, tailWord_3250462, baseEnd_3250462] using wordTrace_append hprefix tailTrace_3250462
  have hstable : (prefixWord ++ tailWord_3250462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250462).length < 2 ^ (prefixWord ++ tailWord_3250462).sum := by decide
  have hdescent : baseEnd_3250462 < baseStart_3250462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250503 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 2, 6]
def baseStart_3250503 : Nat := 118140960795 + 3250503 * 2 ^ 59
def prefixEnd_3250503 : Nat := 4983230072969 + 3 ^ 40 * 3250503 * 2
def baseEnd_3250503 : Nat := 1112713605254400750509143

theorem tailTrace_3250503 : CollatzResearch.WordTrace tailWord_3250503 prefixEnd_3250503 1112713605254400750509143 := by
  unfold tailWord_3250503
  simp only [CollatzResearch.WordTrace]
  refine ⟨118555584142990247560420163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79037056095326831706946775 118555584142990247560420163)
  ·
    refine ⟨177833376214485371340630245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118555584142990247560420163 177833376214485371340630245)
    ·
      refine ⟨33343758040216007126368171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177833376214485371340630245 33343758040216007126368171)
      ·
        refine ⟨50015637060324010689552257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33343758040216007126368171 50015637060324010689552257)
        ·
          refine ⟨37511727795243008017164193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50015637060324010689552257 37511727795243008017164193)
          ·
            refine ⟨28133795846432256012873145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37511727795243008017164193 28133795846432256012873145)
            ·
              refine ⟨21100346884824192009654859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28133795846432256012873145 21100346884824192009654859)
              ·
                refine ⟨31650520327236288014482289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21100346884824192009654859 31650520327236288014482289)
                ·
                  refine ⟨23737890245427216010861717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31650520327236288014482289 23737890245427216010861717)
                  ·
                    refine ⟨1112713605254400750509143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23737890245427216010861717 1112713605254400750509143)
                    ·
                      rfl

theorem cell22_3250503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_3250503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250503 prefixEnd_3250503 := by exact prefixLift 3250503
  have htrace : WordTrace (prefixWord ++ tailWord_3250503) baseStart_3250503 baseEnd_3250503 := by
    simpa [prefixWord, tailWord_3250503, baseEnd_3250503] using wordTrace_append hprefix tailTrace_3250503
  have hstable : (prefixWord ++ tailWord_3250503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250503).length < 2 ^ (prefixWord ++ tailWord_3250503).sum := by decide
  have hdescent : baseEnd_3250503 < baseStart_3250503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250595 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 1, 5]
def baseStart_3250595 : Nat := 118140960795 + 3250595 * 2 ^ 59
def prefixEnd_3250595 : Nat := 4983230072969 + 3 ^ 40 * 3250595 * 2
def baseEnd_3250595 : Nat := 1112745098734543177208861

theorem tailTrace_3250595 : CollatzResearch.WordTrace tailWord_3250595 prefixEnd_3250595 1112745098734543177208861 := by
  unfold tailWord_3250595
  simp only [CollatzResearch.WordTrace]
  refine ⟨118558939658656947272769239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79039293105771298181846159 118558939658656947272769239)
  ·
    refine ⟨177838409487985420909153859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118558939658656947272769239 177838409487985420909153859)
    ·
      refine ⟨266757614231978131363730789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177838409487985420909153859 266757614231978131363730789)
      ·
        refine ⟨50017052668495899630699523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266757614231978131363730789 50017052668495899630699523)
        ·
          refine ⟨75025579002743849446049285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50017052668495899630699523 75025579002743849446049285)
          ·
            refine ⟨14067296063014471771134241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75025579002743849446049285 14067296063014471771134241)
            ·
              refine ⟨10550472047260853828350681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14067296063014471771134241 10550472047260853828350681)
              ·
                refine ⟨7912854035445640371263011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10550472047260853828350681 7912854035445640371263011)
                ·
                  refine ⟨11869281053168460556894517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7912854035445640371263011 11869281053168460556894517)
                  ·
                    refine ⟨1112745098734543177208861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11869281053168460556894517 1112745098734543177208861)
                    ·
                      rfl

theorem cell22_3250595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 5].length) (baseStart_3250595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250595 prefixEnd_3250595 := by exact prefixLift 3250595
  have htrace : WordTrace (prefixWord ++ tailWord_3250595) baseStart_3250595 baseEnd_3250595 := by
    simpa [prefixWord, tailWord_3250595, baseEnd_3250595] using wordTrace_append hprefix tailTrace_3250595
  have hstable : (prefixWord ++ tailWord_3250595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250595).length < 2 ^ (prefixWord ++ tailWord_3250595).sum := by decide
  have hdescent : baseEnd_3250595 < baseStart_3250595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250597 : List Nat := [1, 3, 1, 2, 1, 1, 6, 3, 4]
def baseStart_3250597 : Nat := 118140960795 + 3250597 * 2 ^ 59
def prefixEnd_3250597 : Nat := 4983230072969 + 3 ^ 40 * 3250597 * 2
def baseEnd_3250597 : Nat := 370915261125138612886285

theorem tailTrace_3250597 : CollatzResearch.WordTrace tailWord_3250597 prefixEnd_3250597 370915261125138612886285 := by
  unfold tailWord_3250597
  simp only [CollatzResearch.WordTrace]
  refine ⟨118559012604649701614342045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79039341736433134409561363 118559012604649701614342045)
  ·
    refine ⟨44459629726743638105378267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118559012604649701614342045 44459629726743638105378267)
    ·
      refine ⟨66689444590115457158067401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44459629726743638105378267 66689444590115457158067401)
      ·
        refine ⟨50017083442586592868550551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66689444590115457158067401 50017083442586592868550551)
        ·
          refine ⟨75025625163879889302825827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50017083442586592868550551 75025625163879889302825827)
          ·
            refine ⟨112538437745819833954238741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75025625163879889302825827 112538437745819833954238741)
            ·
              refine ⟨5275239269335304716604941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112538437745819833954238741 5275239269335304716604941)
              ·
                refine ⟨1978214726000739268726853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5275239269335304716604941 1978214726000739268726853)
                ·
                  refine ⟨370915261125138612886285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978214726000739268726853 370915261125138612886285)
                  ·
                    rfl

theorem cell22_3250597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_3250597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250597 prefixEnd_3250597 := by exact prefixLift 3250597
  have htrace : WordTrace (prefixWord ++ tailWord_3250597) baseStart_3250597 baseEnd_3250597 := by
    simpa [prefixWord, tailWord_3250597, baseEnd_3250597] using wordTrace_append hprefix tailTrace_3250597
  have hstable : (prefixWord ++ tailWord_3250597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250597).length < 2 ^ (prefixWord ++ tailWord_3250597).sum := by decide
  have hdescent : baseEnd_3250597 < baseStart_3250597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250599 : List Nat := [1, 1, 6, 1, 1, 2, 4, 1, 1, 4]
def baseStart_3250599 : Nat := 118140960795 + 3250599 * 2 ^ 59
def prefixEnd_3250599 : Nat := 4983230072969 + 3 ^ 40 * 3250599 * 2
def baseEnd_3250599 : Nat := 1112746468016288500108849

theorem tailTrace_3250599 : CollatzResearch.WordTrace tailWord_3250599 prefixEnd_3250599 1112746468016288500108849 := by
  unfold tailWord_3250599
  simp only [CollatzResearch.WordTrace]
  refine ⟨118559085550642455955914851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79039390367094970637276567 118559085550642455955914851)
  ·
    refine ⟨177838628325963683933872277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118559085550642455955914851 177838628325963683933872277)
    ·
      refine ⟨8336185702779547684400263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 177838628325963683933872277 8336185702779547684400263)
      ·
        refine ⟨12504278554169321526600395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8336185702779547684400263 12504278554169321526600395)
        ·
          refine ⟨18756417831253982289900593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12504278554169321526600395 18756417831253982289900593)
          ·
            refine ⟨14067313373440486717425445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18756417831253982289900593 14067313373440486717425445)
            ·
              refine ⟨2637621257520091259517271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14067313373440486717425445 2637621257520091259517271)
              ·
                refine ⟨3956431886280136889275907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637621257520091259517271 3956431886280136889275907)
                ·
                  refine ⟨5934647829420205333913861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3956431886280136889275907 5934647829420205333913861)
                  ·
                    refine ⟨1112746468016288500108849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5934647829420205333913861 1112746468016288500108849)
                    ·
                      rfl

theorem cell22_3250599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_3250599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250599 prefixEnd_3250599 := by exact prefixLift 3250599
  have htrace : WordTrace (prefixWord ++ tailWord_3250599) baseStart_3250599 baseEnd_3250599 := by
    simpa [prefixWord, tailWord_3250599, baseEnd_3250599] using wordTrace_append hprefix tailTrace_3250599
  have hstable : (prefixWord ++ tailWord_3250599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250599).length < 2 ^ (prefixWord ++ tailWord_3250599).sum := by decide
  have hdescent : baseEnd_3250599 < baseStart_3250599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250610 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_3250610 : Nat := 118140960795 + 3250610 * 2 ^ 59
def prefixEnd_3250610 : Nat := 4983230072969 + 3 ^ 40 * 3250610 * 2
def baseEnd_3250610 : Nat := 1112750233541088138083815

theorem tailTrace_3250610 : CollatzResearch.WordTrace tailWord_3250610 prefixEnd_3250610 1112750233541088138083815 := by
  unfold tailWord_3250610
  simp only [CollatzResearch.WordTrace]
  refine ⟨29639871688400651208641321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79039657835735069889710189 29639871688400651208641321)
  ·
    refine ⟨22229903766300488406480991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29639871688400651208641321 22229903766300488406480991)
    ·
      refine ⟨33344855649450732609721487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22229903766300488406480991 33344855649450732609721487)
      ·
        refine ⟨50017283474176098914582231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33344855649450732609721487 50017283474176098914582231)
        ·
          refine ⟨75025925211264148371873347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50017283474176098914582231 75025925211264148371873347)
          ·
            refine ⟨112538887816896222557810021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75025925211264148371873347 112538887816896222557810021)
            ·
              refine ⟨21101041465668041729589379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112538887816896222557810021 21101041465668041729589379)
              ·
                refine ⟨31651562198502062594384069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21101041465668041729589379 31651562198502062594384069)
                ·
                  refine ⟨5934667912219136736447013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31651562198502062594384069 5934667912219136736447013)
                  ·
                    refine ⟨1112750233541088138083815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5934667912219136736447013 1112750233541088138083815)
                    ·
                      rfl

theorem cell22_3250610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_3250610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250610 prefixEnd_3250610 := by exact prefixLift 3250610
  have htrace : WordTrace (prefixWord ++ tailWord_3250610) baseStart_3250610 baseEnd_3250610 := by
    simpa [prefixWord, tailWord_3250610, baseEnd_3250610] using wordTrace_append hprefix tailTrace_3250610
  have hstable : (prefixWord ++ tailWord_3250610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250610).length < 2 ^ (prefixWord ++ tailWord_3250610).sum := by decide
  have hdescent : baseEnd_3250610 < baseStart_3250610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250685 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_3250685 : Nat := 118140960795 + 3250685 * 2 ^ 59
def prefixEnd_3250685 : Nat := 4983230072969 + 3 ^ 40 * 3250685 * 2
def baseEnd_3250685 : Nat := 1112775907573812942458585

theorem tailTrace_3250685 : CollatzResearch.WordTrace tailWord_3250685 prefixEnd_3250685 1112775907573812942458585 := by
  unfold tailWord_3250685
  simp only [CollatzResearch.WordTrace]
  refine ⟨118562222228330892643545509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79041481485553928429030339 118562222228330892643545509)
  ·
    refine ⟨22230416667812042370664783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118562222228330892643545509 22230416667812042370664783)
    ·
      refine ⟨33345625001718063555997175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22230416667812042370664783 33345625001718063555997175)
      ·
        refine ⟨50018437502577095333995763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33345625001718063555997175 50018437502577095333995763)
        ·
          refine ⟨75027656253865643000993645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50018437502577095333995763 75027656253865643000993645)
          ·
            refine ⟨28135371095199616125372617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75027656253865643000993645 28135371095199616125372617)
            ·
              refine ⟨21101528321399712094029463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28135371095199616125372617 21101528321399712094029463)
              ·
                refine ⟨31652292482099568141044195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21101528321399712094029463 31652292482099568141044195)
                ·
                  refine ⟨47478438723149352211566293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31652292482099568141044195 47478438723149352211566293)
                  ·
                    refine ⟨1112775907573812942458585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47478438723149352211566293 1112775907573812942458585)
                    ·
                      rfl

theorem cell22_3250685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_3250685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250685 prefixEnd_3250685 := by exact prefixLift 3250685
  have htrace : WordTrace (prefixWord ++ tailWord_3250685) baseStart_3250685 baseEnd_3250685 := by
    simpa [prefixWord, tailWord_3250685, baseEnd_3250685] using wordTrace_append hprefix tailTrace_3250685
  have hstable : (prefixWord ++ tailWord_3250685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250685).length < 2 ^ (prefixWord ++ tailWord_3250685).sum := by decide
  have hdescent : baseEnd_3250685 < baseStart_3250685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250760 : List Nat := [2, 1, 3, 1, 1, 1, 1, 12]
def baseStart_3250760 : Nat := 118140960795 + 3250760 * 2 ^ 59
def prefixEnd_3250760 : Nat := 4983230072969 + 3 ^ 40 * 3250760 * 2
def baseEnd_3250760 : Nat := 123644620178504194092595

theorem tailTrace_3250760 : CollatzResearch.WordTrace tailWord_3250760 prefixEnd_3250760 123644620178504194092595 := by
  unfold tailWord_3250760
  simp only [CollatzResearch.WordTrace]
  refine ⟨59282478851529590226262867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79043305135372786968350489 59282478851529590226262867)
  ·
    refine ⟨88923718277294385339394301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59282478851529590226262867 88923718277294385339394301)
    ·
      refine ⟨33346394353985394502272863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88923718277294385339394301 33346394353985394502272863)
      ·
        refine ⟨50019591530978091753409295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33346394353985394502272863 50019591530978091753409295)
        ·
          refine ⟨75029387296467137630113943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50019591530978091753409295 75029387296467137630113943)
          ·
            refine ⟨112544080944700706445170915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75029387296467137630113943 112544080944700706445170915)
            ·
              refine ⟨168816121417051059667756373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112544080944700706445170915 168816121417051059667756373)
              ·
                refine ⟨123644620178504194092595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 168816121417051059667756373 123644620178504194092595)
                ·
                  rfl

theorem cell22_3250760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 12].length) (baseStart_3250760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250760 prefixEnd_3250760 := by exact prefixLift 3250760
  have htrace : WordTrace (prefixWord ++ tailWord_3250760) baseStart_3250760 baseEnd_3250760 := by
    simpa [prefixWord, tailWord_3250760, baseEnd_3250760] using wordTrace_append hprefix tailTrace_3250760
  have hstable : (prefixWord ++ tailWord_3250760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250760).length < 2 ^ (prefixWord ++ tailWord_3250760).sum := by decide
  have hdescent : baseEnd_3250760 < baseStart_3250760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250762 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_3250762 : Nat := 118140960795 + 3250762 * 2 ^ 59
def prefixEnd_3250762 : Nat := 4983230072969 + 3 ^ 40 * 3250762 * 2
def baseEnd_3250762 : Nat := 1112802266247410408283349

theorem tailTrace_3250762 : CollatzResearch.WordTrace tailWord_3250762 prefixEnd_3250762 1112802266247410408283349 := by
  unfold tailWord_3250762
  simp only [CollatzResearch.WordTrace]
  refine ⟨29641257662262983698524635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79043353766034623196065693 29641257662262983698524635)
  ·
    refine ⟨44461886493394475547786953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29641257662262983698524635 44461886493394475547786953)
    ·
      refine ⟨33346414870045856660840215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44461886493394475547786953 33346414870045856660840215)
      ·
        refine ⟨50019622305068784991260323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33346414870045856660840215 50019622305068784991260323)
        ·
          refine ⟨75029433457603177486890485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50019622305068784991260323 75029433457603177486890485)
          ·
            refine ⟨7034009386650297889395983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75029433457603177486890485 7034009386650297889395983)
            ·
              refine ⟨10551014079975446834093975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7034009386650297889395983 10551014079975446834093975)
              ·
                refine ⟨15826521119963170251140963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10551014079975446834093975 15826521119963170251140963)
                ·
                  refine ⟨23739781679944755376711445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15826521119963170251140963 23739781679944755376711445)
                  ·
                    refine ⟨1112802266247410408283349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23739781679944755376711445 1112802266247410408283349)
                    ·
                      rfl

theorem cell22_3250762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_3250762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250762 prefixEnd_3250762 := by exact prefixLift 3250762
  have htrace : WordTrace (prefixWord ++ tailWord_3250762) baseStart_3250762 baseEnd_3250762 := by
    simpa [prefixWord, tailWord_3250762, baseEnd_3250762] using wordTrace_append hprefix tailTrace_3250762
  have hstable : (prefixWord ++ tailWord_3250762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250762).length < 2 ^ (prefixWord ++ tailWord_3250762).sum := by decide
  have hdescent : baseEnd_3250762 < baseStart_3250762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250798 : List Nat := [4, 1, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3250798 : Nat := 118140960795 + 3250798 * 2 ^ 59
def prefixEnd_3250798 : Nat := 4983230072969 + 3 ^ 40 * 3250798 * 2
def baseEnd_3250798 : Nat := 1112814589783118314383239

theorem tailTrace_3250798 : CollatzResearch.WordTrace tailWord_3250798 prefixEnd_3250798 1112814589783118314383239 := by
  unfold tailWord_3250798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14820792959615189117801131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79044229117947675294939365 14820792959615189117801131)
  ·
    refine ⟨22231189439422783676701697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14820792959615189117801131 22231189439422783676701697)
    ·
      refine ⟨16673392079567087757526273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22231189439422783676701697 16673392079567087757526273)
      ·
        refine ⟨12505044059675315818144705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16673392079567087757526273 12505044059675315818144705)
        ·
          refine ⟨9378783044756486863608529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12505044059675315818144705 9378783044756486863608529)
          ·
            refine ⟨7034087283567365147706397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9378783044756486863608529 7034087283567365147706397)
            ·
              refine ⟨2637782731337761930389899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7034087283567365147706397 2637782731337761930389899)
              ·
                refine ⟨3956674097006642895584849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637782731337761930389899 3956674097006642895584849)
                ·
                  refine ⟨2967505572754982171688637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3956674097006642895584849 2967505572754982171688637)
                  ·
                    refine ⟨1112814589783118314383239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2967505572754982171688637 1112814589783118314383239)
                    ·
                      rfl

theorem cell22_3250798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3250798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250798 prefixEnd_3250798 := by exact prefixLift 3250798
  have htrace : WordTrace (prefixWord ++ tailWord_3250798) baseStart_3250798 baseEnd_3250798 := by
    simpa [prefixWord, tailWord_3250798, baseEnd_3250798] using wordTrace_append hprefix tailTrace_3250798
  have hstable : (prefixWord ++ tailWord_3250798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250798).length < 2 ^ (prefixWord ++ tailWord_3250798).sum := by decide
  have hdescent : baseEnd_3250798 < baseStart_3250798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250809 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 3, 3]
def baseStart_3250809 : Nat := 118140960795 + 3250809 * 2 ^ 59
def prefixEnd_3250809 : Nat := 4983230072969 + 3 ^ 40 * 3250809 * 2
def baseEnd_3250809 : Nat := 1112818355307917952358205

theorem tailTrace_3250809 : CollatzResearch.WordTrace tailWord_3250809 prefixEnd_3250809 1112818355307917952358205 := by
  unfold tailWord_3250809
  simp only [CollatzResearch.WordTrace]
  refine ⟨118566744879881661821059481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79044496586587774547372987 118566744879881661821059481)
  ·
    refine ⟨88925058659911246365794611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118566744879881661821059481 88925058659911246365794611)
    ·
      refine ⟨133387587989866869548691917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88925058659911246365794611 133387587989866869548691917)
      ·
        refine ⟨50020345496200076080759469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133387587989866869548691917 50020345496200076080759469)
        ·
          refine ⟨18757629561075028530284801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50020345496200076080759469 18757629561075028530284801)
          ·
            refine ⟨14068222170806271397713601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18757629561075028530284801 14068222170806271397713601)
            ·
              refine ⟨10551166628104703548285201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14068222170806271397713601 10551166628104703548285201)
              ·
                refine ⟨7913374971078527661213901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10551166628104703548285201 7913374971078527661213901)
                ·
                  refine ⟨2967515614154447872955213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7913374971078527661213901 2967515614154447872955213)
                  ·
                    refine ⟨1112818355307917952358205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2967515614154447872955213 1112818355307917952358205)
                    ·
                      rfl

theorem cell22_3250809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 3].length) (baseStart_3250809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250809 prefixEnd_3250809 := by exact prefixLift 3250809
  have htrace : WordTrace (prefixWord ++ tailWord_3250809) baseStart_3250809 baseEnd_3250809 := by
    simpa [prefixWord, tailWord_3250809, baseEnd_3250809] using wordTrace_append hprefix tailTrace_3250809
  have hstable : (prefixWord ++ tailWord_3250809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250809).length < 2 ^ (prefixWord ++ tailWord_3250809).sum := by decide
  have hdescent : baseEnd_3250809 < baseStart_3250809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250916 : List Nat := [2, 3, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_3250916 : Nat := 118140960795 + 3250916 * 2 ^ 59
def prefixEnd_3250916 : Nat := 4983230072969 + 3 ^ 40 * 3250916 * 2
def baseEnd_3250916 : Nat := 1112854983594605339932877

theorem tailTrace_3250916 : CollatzResearch.WordTrace tailWord_3250916 prefixEnd_3250916 1112854983594605339932877 := by
  unfold tailWord_3250916
  simp only [CollatzResearch.WordTrace]
  refine ⟨59285323745247009547602301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79047098326996012730136401 59285323745247009547602301)
  ·
    refine ⟨22231996404467628580350863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59285323745247009547602301 22231996404467628580350863)
    ·
      refine ⟨33347994606701442870526295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22231996404467628580350863 33347994606701442870526295)
      ·
        refine ⟨50021991910052164305789443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33347994606701442870526295 50021991910052164305789443)
        ·
          refine ⟨75032987865078246458684165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50021991910052164305789443 75032987865078246458684165)
          ·
            refine ⟨14068685224702171211003281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75032987865078246458684165 14068685224702171211003281)
            ·
              refine ⟨10551513918526628408252461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14068685224702171211003281 10551513918526628408252461)
              ·
                refine ⟨3956817719447485653094673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10551513918526628408252461 3956817719447485653094673)
                ·
                  refine ⟨2967613289585614239821005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3956817719447485653094673 2967613289585614239821005)
                  ·
                    refine ⟨1112854983594605339932877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2967613289585614239821005 1112854983594605339932877)
                    ·
                      rfl

theorem cell22_3250916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_3250916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250916 prefixEnd_3250916 := by exact prefixLift 3250916
  have htrace : WordTrace (prefixWord ++ tailWord_3250916) baseStart_3250916 baseEnd_3250916 := by
    simpa [prefixWord, tailWord_3250916, baseEnd_3250916] using wordTrace_append hprefix tailTrace_3250916
  have hstable : (prefixWord ++ tailWord_3250916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250916).length < 2 ^ (prefixWord ++ tailWord_3250916).sum := by decide
  have hdescent : baseEnd_3250916 < baseStart_3250916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250929 : List Nat := [1, 2, 2, 2, 2, 2, 5, 6]
def baseStart_3250929 : Nat := 118140960795 + 3250929 * 2 ^ 59
def prefixEnd_3250929 : Nat := 4983230072969 + 3 ^ 40 * 3250929 * 2
def baseEnd_3250929 : Nat := 123651048195586404373093

theorem tailTrace_3250929 : CollatzResearch.WordTrace tailWord_3250929 prefixEnd_3250929 123651048195586404373093 := by
  unfold tailWord_3250929
  simp only [CollatzResearch.WordTrace]
  refine ⟨118571121639446922315427841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79047414426297948210285227 118571121639446922315427841)
  ·
    refine ⟨88928341229585191736570881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118571121639446922315427841 88928341229585191736570881)
    ·
      refine ⟨66696255922188893802428161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88928341229585191736570881 66696255922188893802428161)
      ·
        refine ⟨50022191941641670351821121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66696255922188893802428161 50022191941641670351821121)
        ·
          refine ⟨37516643956231252763865841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50022191941641670351821121 37516643956231252763865841)
          ·
            refine ⟨28137482967173439572899381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37516643956231252763865841 28137482967173439572899381)
            ·
              refine ⟨2637889028172509959959317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28137482967173439572899381 2637889028172509959959317)
              ·
                refine ⟨123651048195586404373093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2637889028172509959959317 123651048195586404373093)
                ·
                  rfl

theorem cell22_3250929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 6].length) (baseStart_3250929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250929 prefixEnd_3250929 := by exact prefixLift 3250929
  have htrace : WordTrace (prefixWord ++ tailWord_3250929) baseStart_3250929 baseEnd_3250929 := by
    simpa [prefixWord, tailWord_3250929, baseEnd_3250929] using wordTrace_append hprefix tailTrace_3250929
  have hstable : (prefixWord ++ tailWord_3250929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250929).length < 2 ^ (prefixWord ++ tailWord_3250929).sum := by decide
  have hdescent : baseEnd_3250929 < baseStart_3250929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250995 : List Nat := [1, 1, 1, 2, 6, 3, 1, 3, 1, 3]
def baseStart_3250995 : Nat := 118140960795 + 3250995 * 2 ^ 59
def prefixEnd_3250995 : Nat := 4983230072969 + 3 ^ 40 * 3250995 * 2
def baseEnd_3250995 : Nat := 1112882026909075467207635

theorem tailTrace_3250995 : CollatzResearch.WordTrace tailWord_3250995 prefixEnd_3250995 1112882026909075467207635 := by
  unfold tailWord_3250995
  simp only [CollatzResearch.WordTrace]
  refine ⟨118573528857207815587330439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79049019238138543724886959 118573528857207815587330439)
  ·
    refine ⟨177860293285811723380995659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118573528857207815587330439 177860293285811723380995659)
    ·
      refine ⟨266790439928717585071493489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177860293285811723380995659 266790439928717585071493489)
      ·
        refine ⟨200092829946538188803620117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266790439928717585071493489 200092829946538188803620117)
        ·
          refine ⟨9379351403743977600169693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 200092829946538188803620117 9379351403743977600169693)
          ·
            refine ⟨3517256776403991600063635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9379351403743977600169693 3517256776403991600063635)
            ·
              refine ⟨5275885164605987400095453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517256776403991600063635 5275885164605987400095453)
              ·
                refine ⟨1978456936727245275035795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5275885164605987400095453 1978456936727245275035795)
                ·
                  refine ⟨2967685405090867912553693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978456936727245275035795 2967685405090867912553693)
                  ·
                    refine ⟨1112882026909075467207635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2967685405090867912553693 1112882026909075467207635)
                    ·
                      rfl

theorem cell22_3250995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 1, 3].length) (baseStart_3250995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3250995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3250995 prefixEnd_3250995 := by exact prefixLift 3250995
  have htrace : WordTrace (prefixWord ++ tailWord_3250995) baseStart_3250995 baseEnd_3250995 := by
    simpa [prefixWord, tailWord_3250995, baseEnd_3250995] using wordTrace_append hprefix tailTrace_3250995
  have hstable : (prefixWord ++ tailWord_3250995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250995).length < 2 ^ (prefixWord ++ tailWord_3250995).sum := by decide
  have hdescent : baseEnd_3250995 < baseStart_3250995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251004 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_3251004 : Nat := 118140960795 + 3251004 * 2 ^ 59
def prefixEnd_3251004 : Nat := 4983230072969 + 3 ^ 40 * 3251004 * 2
def baseEnd_3251004 : Nat := 1112885107793002443732607

theorem tailTrace_3251004 : CollatzResearch.WordTrace tailWord_3251004 prefixEnd_3251004 1112885107793002443732607 := by
  unfold tailWord_3251004
  simp only [CollatzResearch.WordTrace]
  refine ⟨59286928557087605062204033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79049238076116806749605377 59286928557087605062204033)
  ·
    refine ⟨44465196417815703796653025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59286928557087605062204033 44465196417815703796653025)
    ·
      refine ⟨33348897313361777847489769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44465196417815703796653025 33348897313361777847489769)
      ·
        refine ⟨25011672985021333385617327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33348897313361777847489769 25011672985021333385617327)
        ·
          refine ⟨37517509477532000078425991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25011672985021333385617327 37517509477532000078425991)
          ·
            refine ⟨56276264216298000117638987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37517509477532000078425991 56276264216298000117638987)
            ·
              refine ⟨84414396324447000176458481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56276264216298000117638987 84414396324447000176458481)
              ·
                refine ⟨63310797243335250132343861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84414396324447000176458481 63310797243335250132343861)
                ·
                  refine ⟨5935387241562679699907237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63310797243335250132343861 5935387241562679699907237)
                  ·
                    refine ⟨1112885107793002443732607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5935387241562679699907237 1112885107793002443732607)
                    ·
                      rfl

theorem cell22_3251004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_3251004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251004 prefixEnd_3251004 := by exact prefixLift 3251004
  have htrace : WordTrace (prefixWord ++ tailWord_3251004) baseStart_3251004 baseEnd_3251004 := by
    simpa [prefixWord, tailWord_3251004, baseEnd_3251004] using wordTrace_append hprefix tailTrace_3251004
  have hstable : (prefixWord ++ tailWord_3251004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251004).length < 2 ^ (prefixWord ++ tailWord_3251004).sum := by decide
  have hdescent : baseEnd_3251004 < baseStart_3251004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251012 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3251012 : Nat := 118140960795 + 3251012 * 2 ^ 59
def prefixEnd_3251012 : Nat := 4983230072969 + 3 ^ 40 * 3251012 * 2
def baseEnd_3251012 : Nat := 1112887846356493089532583

theorem tailTrace_3251012 : CollatzResearch.WordTrace tailWord_3251012 prefixEnd_3251012 1112887846356493089532583 := by
  unfold tailWord_3251012
  simp only [CollatzResearch.WordTrace]
  refine ⟨59287074449073113745349645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79049432598764151660466193 59287074449073113745349645)
  ·
    refine ⟨22232652918402417654506117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59287074449073113745349645 22232652918402417654506117)
    ·
      refine ⟨4168622422200453310219897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22232652918402417654506117 4168622422200453310219897)
      ·
        refine ⟨3126466816650339982664923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4168622422200453310219897 3126466816650339982664923)
        ·
          refine ⟨4689700224975509973997385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126466816650339982664923 4689700224975509973997385)
          ·
            refine ⟨3517275168731632480498039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4689700224975509973997385 3517275168731632480498039)
            ·
              refine ⟨5275912753097448720747059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517275168731632480498039 5275912753097448720747059)
              ·
                refine ⟨7913869129646173081120589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275912753097448720747059 7913869129646173081120589)
                ·
                  refine ⟨2967700923617314905420221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7913869129646173081120589 2967700923617314905420221)
                  ·
                    refine ⟨1112887846356493089532583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2967700923617314905420221 1112887846356493089532583)
                    ·
                      rfl

theorem cell22_3251012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3251012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251012 prefixEnd_3251012 := by exact prefixLift 3251012
  have htrace : WordTrace (prefixWord ++ tailWord_3251012) baseStart_3251012 baseEnd_3251012 := by
    simpa [prefixWord, tailWord_3251012, baseEnd_3251012] using wordTrace_append hprefix tailTrace_3251012
  have hstable : (prefixWord ++ tailWord_3251012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251012).length < 2 ^ (prefixWord ++ tailWord_3251012).sum := by decide
  have hdescent : baseEnd_3251012 < baseStart_3251012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251025 : List Nat := [1, 2, 2, 1, 7, 1, 2, 1, 5]
def baseStart_3251025 : Nat := 118140960795 + 3251025 * 2 ^ 59
def prefixEnd_3251025 : Nat := 4983230072969 + 3 ^ 40 * 3251025 * 2
def baseEnd_3251025 : Nat := 370964098840721796319181

theorem tailTrace_3251025 : CollatzResearch.WordTrace tailWord_3251025 prefixEnd_3251025 370964098840721796319181 := by
  unfold tailWord_3251025
  simp only [CollatzResearch.WordTrace]
  refine ⟨118574623047099130710922529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79049748698066087140615019 118574623047099130710922529)
  ·
    refine ⟨88930967285324348033191897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118574623047099130710922529 88930967285324348033191897)
    ·
      refine ⟨66698225463993261024893923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88930967285324348033191897 66698225463993261024893923)
      ·
        refine ⟨100047338195989891537340885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66698225463993261024893923 100047338195989891537340885)
        ·
          refine ⟨2344859488968513082906427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 100047338195989891537340885 2344859488968513082906427)
          ·
            refine ⟨3517289233452769624359641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2344859488968513082906427 3517289233452769624359641)
            ·
              refine ⟨2637966925089577218269731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3517289233452769624359641 2637966925089577218269731)
              ·
                refine ⟨3956950387634365827404597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637966925089577218269731 3956950387634365827404597)
                ·
                  refine ⟨370964098840721796319181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3956950387634365827404597 370964098840721796319181)
                  ·
                    rfl

theorem cell22_3251025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 5].length) (baseStart_3251025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251025 prefixEnd_3251025 := by exact prefixLift 3251025
  have htrace : WordTrace (prefixWord ++ tailWord_3251025) baseStart_3251025 baseEnd_3251025 := by
    simpa [prefixWord, tailWord_3251025, baseEnd_3251025] using wordTrace_append hprefix tailTrace_3251025
  have hstable : (prefixWord ++ tailWord_3251025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251025).length < 2 ^ (prefixWord ++ tailWord_3251025).sum := by decide
  have hdescent : baseEnd_3251025 < baseStart_3251025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251081 : List Nat := [1, 2, 1, 1, 5, 4, 1, 7]
def baseStart_3251081 : Nat := 118140960795 + 3251081 * 2 ^ 59
def prefixEnd_3251081 : Nat := 4983230072969 + 3 ^ 40 * 3251081 * 2
def baseEnd_3251081 : Nat := 123656829607399989950819

theorem tailTrace_3251081 : CollatzResearch.WordTrace tailWord_3251081 prefixEnd_3251081 123656829607399989950819 := by
  unfold tailWord_3251081
  simp only [CollatzResearch.WordTrace]
  refine ⟨118576665534896252274961097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79051110356597501516640731 118576665534896252274961097)
  ·
    refine ⟨88932499151172189206220823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118576665534896252274961097 88932499151172189206220823)
    ·
      refine ⟨133398748726758283809331235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88932499151172189206220823 133398748726758283809331235)
      ·
        refine ⟨200098123090137425713996853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133398748726758283809331235 200098123090137425713996853)
        ·
          refine ⟨18759199039700383660687205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200098123090137425713996853 18759199039700383660687205)
          ·
            refine ⟨3517349819943821936378851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18759199039700383660687205 3517349819943821936378851)
            ·
              refine ⟨5276024729915732904568277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517349819943821936378851 5276024729915732904568277)
              ·
                refine ⟨123656829607399989950819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5276024729915732904568277 123656829607399989950819)
                ·
                  rfl

theorem cell22_3251081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 7].length) (baseStart_3251081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251081 prefixEnd_3251081 := by exact prefixLift 3251081
  have htrace : WordTrace (prefixWord ++ tailWord_3251081) baseStart_3251081 baseEnd_3251081 := by
    simpa [prefixWord, tailWord_3251081, baseEnd_3251081] using wordTrace_append hprefix tailTrace_3251081
  have hstable : (prefixWord ++ tailWord_3251081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251081).length < 2 ^ (prefixWord ++ tailWord_3251081).sum := by decide
  have hdescent : baseEnd_3251081 < baseStart_3251081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251098 : List Nat := [3, 1, 1, 4, 3, 1, 3, 6]
def baseStart_3251098 : Nat := 118140960795 + 3251098 * 2 ^ 59
def prefixEnd_3251098 : Nat := 4983230072969 + 3 ^ 40 * 3251098 * 2
def baseEnd_3251098 : Nat := 123657476212668614653591

theorem tailTrace_3251098 : CollatzResearch.WordTrace tailWord_3251098 prefixEnd_3251098 123657476212668614653591 := by
  unfold tailWord_3251098
  simp only [CollatzResearch.WordTrace]
  refine ⟨29644321393958666044582487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79051523717223109452219965 29644321393958666044582487)
  ·
    refine ⟨44466482090937999066873731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29644321393958666044582487 44466482090937999066873731)
    ·
      refine ⟨66699723136406998600310597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44466482090937999066873731 66699723136406998600310597)
      ·
        refine ⟨12506198088076312237558237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66699723136406998600310597 12506198088076312237558237)
        ·
          refine ⟨4689824283028617089084339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12506198088076312237558237 4689824283028617089084339)
          ·
            refine ⟨7034736424542925633626509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689824283028617089084339 7034736424542925633626509)
            ·
              refine ⟨2638026159203597112609941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7034736424542925633626509 2638026159203597112609941)
              ·
                refine ⟨123657476212668614653591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2638026159203597112609941 123657476212668614653591)
                ·
                  rfl

theorem cell22_3251098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_3251098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251098 prefixEnd_3251098 := by exact prefixLift 3251098
  have htrace : WordTrace (prefixWord ++ tailWord_3251098) baseStart_3251098 baseEnd_3251098 := by
    simpa [prefixWord, tailWord_3251098, baseEnd_3251098] using wordTrace_append hprefix tailTrace_3251098
  have hstable : (prefixWord ++ tailWord_3251098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251098).length < 2 ^ (prefixWord ++ tailWord_3251098).sum := by decide
  have hdescent : baseEnd_3251098 < baseStart_3251098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251100 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 2, 4]
def baseStart_3251100 : Nat := 118140960795 + 3251100 * 2 ^ 59
def prefixEnd_3251100 : Nat := 4983230072969 + 3 ^ 40 * 3251100 * 2
def baseEnd_3251100 : Nat := 1112917970554890193332313

theorem tailTrace_3251100 : CollatzResearch.WordTrace tailWord_3251100 prefixEnd_3251100 1112917970554890193332313 := by
  unfold tailWord_3251100
  simp only [CollatzResearch.WordTrace]
  refine ⟨59288679260913709259951377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79051572347884945679935169 59288679260913709259951377)
  ·
    refine ⟨44466509445685281944963533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59288679260913709259951377 44466509445685281944963533)
    ·
      refine ⟨16674941042131980729361325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44466509445685281944963533 16674941042131980729361325)
      ·
        refine ⟨6253102890799492773510497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16674941042131980729361325 6253102890799492773510497)
        ·
          refine ⟨4689827168099619580132873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6253102890799492773510497 4689827168099619580132873)
          ·
            refine ⟨3517370376074714685099655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4689827168099619580132873 3517370376074714685099655)
            ·
              refine ⟨5276055564112072027649483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517370376074714685099655 5276055564112072027649483)
              ·
                refine ⟨7914083346168108041474225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276055564112072027649483 7914083346168108041474225)
                ·
                  refine ⟨5935562509626081031105669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7914083346168108041474225 5935562509626081031105669)
                  ·
                    refine ⟨1112917970554890193332313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5935562509626081031105669 1112917970554890193332313)
                    ·
                      rfl

theorem cell22_3251100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_3251100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251100 prefixEnd_3251100 := by exact prefixLift 3251100
  have htrace : WordTrace (prefixWord ++ tailWord_3251100) baseStart_3251100 baseEnd_3251100 := by
    simpa [prefixWord, tailWord_3251100, baseEnd_3251100] using wordTrace_append hprefix tailTrace_3251100
  have hstable : (prefixWord ++ tailWord_3251100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251100).length < 2 ^ (prefixWord ++ tailWord_3251100).sum := by decide
  have hdescent : baseEnd_3251100 < baseStart_3251100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251149 : List Nat := [1, 6, 3, 1, 1, 2, 2, 6]
def baseStart_3251149 : Nat := 118140960795 + 3251149 * 2 ^ 59
def prefixEnd_3251149 : Nat := 4983230072969 + 3 ^ 40 * 3251149 * 2
def baseEnd_3251149 : Nat := 123659416028474488761907

theorem tailTrace_3251149 : CollatzResearch.WordTrace tailWord_3251149 prefixEnd_3251149 123659416028474488761907 := by
  unfold tailWord_3251149
  simp only [CollatzResearch.WordTrace]
  refine ⟨118579145698649899888436501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79052763799099933258957667 118579145698649899888436501)
  ·
    refine ⟨5558397454624214057270461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118579145698649899888436501 5558397454624214057270461)
    ·
      refine ⟨2084399045484080271476423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5558397454624214057270461 2084399045484080271476423)
      ·
        refine ⟨3126598568226120407214635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084399045484080271476423 3126598568226120407214635)
        ·
          refine ⟨4689897852339180610821953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126598568226120407214635 4689897852339180610821953)
          ·
            refine ⟨3517423389254385458116465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4689897852339180610821953 3517423389254385458116465)
            ·
              refine ⟨2638067541940789093587349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3517423389254385458116465 2638067541940789093587349)
              ·
                refine ⟨123659416028474488761907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2638067541940789093587349 123659416028474488761907)
                ·
                  rfl

theorem cell22_3251149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 6].length) (baseStart_3251149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251149 prefixEnd_3251149 := by exact prefixLift 3251149
  have htrace : WordTrace (prefixWord ++ tailWord_3251149) baseStart_3251149 baseEnd_3251149 := by
    simpa [prefixWord, tailWord_3251149, baseEnd_3251149] using wordTrace_append hprefix tailTrace_3251149
  have hstable : (prefixWord ++ tailWord_3251149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251149).length < 2 ^ (prefixWord ++ tailWord_3251149).sum := by decide
  have hdescent : baseEnd_3251149 < baseStart_3251149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251239 : List Nat := [1, 1, 7, 1, 1, 3, 2, 2, 4]
def baseStart_3251239 : Nat := 118140960795 + 3251239 * 2 ^ 59
def prefixEnd_3251239 : Nat := 4983230072969 + 3 ^ 40 * 3251239 * 2
def baseEnd_3251239 : Nat := 370988517698513388035629

theorem tailTrace_3251239 : CollatzResearch.WordTrace tailWord_3251239 prefixEnd_3251239 370988517698513388035629 := by
  unfold tailWord_3251239
  simp only [CollatzResearch.WordTrace]
  refine ⟨118582428268323845259212771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79054952178882563506141847 118582428268323845259212771)
  ·
    refine ⟨177873642402485767888819157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118582428268323845259212771 177873642402485767888819157)
    ·
      refine ⟨4168913493808260184894199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 177873642402485767888819157 4168913493808260184894199)
      ·
        refine ⟨6253370240712390277341299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4168913493808260184894199 6253370240712390277341299)
        ·
          refine ⟨9380055361068585416011949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6253370240712390277341299 9380055361068585416011949)
          ·
            refine ⟨3517520760400719531004481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9380055361068585416011949 3517520760400719531004481)
            ·
              refine ⟨2638140570300539648253361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3517520760400719531004481 2638140570300539648253361)
              ·
                refine ⟨1978605427725404736190021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638140570300539648253361 1978605427725404736190021)
                ·
                  refine ⟨370988517698513388035629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978605427725404736190021 370988517698513388035629)
                  ·
                    rfl

theorem cell22_3251239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 4].length) (baseStart_3251239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251239 prefixEnd_3251239 := by exact prefixLift 3251239
  have htrace : WordTrace (prefixWord ++ tailWord_3251239) baseStart_3251239 baseEnd_3251239 := by
    simpa [prefixWord, tailWord_3251239, baseEnd_3251239] using wordTrace_append hprefix tailTrace_3251239
  have hstable : (prefixWord ++ tailWord_3251239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251239).length < 2 ^ (prefixWord ++ tailWord_3251239).sum := by decide
  have hdescent : baseEnd_3251239 < baseStart_3251239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251248 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 3, 3]
def baseStart_3251248 : Nat := 118140960795 + 3251248 * 2 ^ 59
def prefixEnd_3251248 : Nat := 4983230072969 + 3 ^ 40 * 3251248 * 2
def baseEnd_3251248 : Nat := 1112968633979467140631859

theorem tailTrace_3251248 : CollatzResearch.WordTrace tailWord_3251248 prefixEnd_3251248 1112968633979467140631859 := by
  unfold tailWord_3251248
  simp only [CollatzResearch.WordTrace]
  refine ⟨59291378262645619898145199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79055171016860826530860265 59291378262645619898145199)
  ·
    refine ⟨88937067393968429847217799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59291378262645619898145199 88937067393968429847217799)
    ·
      refine ⟨133405601090952644770826699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88937067393968429847217799 133405601090952644770826699)
      ·
        refine ⟨200108401636428967156240049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133405601090952644770826699 200108401636428967156240049)
        ·
          refine ⟨150081301227321725367180037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200108401636428967156240049 150081301227321725367180037)
          ·
            refine ⟨28140243980122823506346257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150081301227321725367180037 28140243980122823506346257)
            ·
              refine ⟨21105182985092117629759693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28140243980122823506346257 21105182985092117629759693)
              ·
                refine ⟨7914443619409544111159885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21105182985092117629759693 7914443619409544111159885)
                ·
                  refine ⟨2967916357278579041684957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7914443619409544111159885 2967916357278579041684957)
                  ·
                    refine ⟨1112968633979467140631859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2967916357278579041684957 1112968633979467140631859)
                    ·
                      rfl

theorem cell22_3251248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 3, 3].length) (baseStart_3251248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251248 prefixEnd_3251248 := by exact prefixLift 3251248
  have htrace : WordTrace (prefixWord ++ tailWord_3251248) baseStart_3251248 baseEnd_3251248 := by
    simpa [prefixWord, tailWord_3251248, baseEnd_3251248] using wordTrace_append hprefix tailTrace_3251248
  have hstable : (prefixWord ++ tailWord_3251248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251248).length < 2 ^ (prefixWord ++ tailWord_3251248).sum := by decide
  have hdescent : baseEnd_3251248 < baseStart_3251248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251276 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_3251276 : Nat := 118140960795 + 3251276 * 2 ^ 59
def prefixEnd_3251276 : Nat := 4983230072969 + 3 ^ 40 * 3251276 * 2
def baseEnd_3251276 : Nat := 1112978218951684400931773

theorem tailTrace_3251276 : CollatzResearch.WordTrace tailWord_3251276 prefixEnd_3251276 1112978218951684400931773 := by
  unfold tailWord_3251276
  simp only [CollatzResearch.WordTrace]
  refine ⟨59291888884594900289154841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79055851846126533718873121 59291888884594900289154841)
  ·
    refine ⟨44468916663446175216866131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59291888884594900289154841 44468916663446175216866131)
    ·
      refine ⟨66703374995169262825299197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44468916663446175216866131 66703374995169262825299197)
      ·
        refine ⟨25013765623188473559487199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66703374995169262825299197 25013765623188473559487199)
        ·
          refine ⟨37520648434782710339230799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25013765623188473559487199 37520648434782710339230799)
          ·
            refine ⟨56280972652174065508846199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37520648434782710339230799 56280972652174065508846199)
            ·
              refine ⟨84421458978261098263269299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56280972652174065508846199 84421458978261098263269299)
              ·
                refine ⟨126632188467391647394903949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84421458978261098263269299 126632188467391647394903949)
                ·
                  refine ⟨47487070675271867773088981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126632188467391647394903949 47487070675271867773088981)
                  ·
                    refine ⟨1112978218951684400931773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47487070675271867773088981 1112978218951684400931773)
                    ·
                      rfl

theorem cell22_3251276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_3251276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251276 prefixEnd_3251276 := by exact prefixLift 3251276
  have htrace : WordTrace (prefixWord ++ tailWord_3251276) baseStart_3251276 baseEnd_3251276 := by
    simpa [prefixWord, tailWord_3251276, baseEnd_3251276] using wordTrace_append hprefix tailTrace_3251276
  have hstable : (prefixWord ++ tailWord_3251276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251276).length < 2 ^ (prefixWord ++ tailWord_3251276).sum := by decide
  have hdescent : baseEnd_3251276 < baseStart_3251276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251282 : List Nat := [3, 2, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_3251282 : Nat := 118140960795 + 3251282 * 2 ^ 59
def prefixEnd_3251282 : Nat := 4983230072969 + 3 ^ 40 * 3251282 * 2
def baseEnd_3251282 : Nat := 1112980272874302385281755

theorem tailTrace_3251282 : CollatzResearch.WordTrace tailWord_3251282 prefixEnd_3251282 1112980272874302385281755 := by
  unfold tailWord_3251282
  simp only [CollatzResearch.WordTrace]
  refine ⟨29645999151792015900757025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79055997738112042402018733 29645999151792015900757025)
  ·
    refine ⟨22234499363844011925567769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29645999151792015900757025 22234499363844011925567769)
    ·
      refine ⟨16675874522883008944175827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22234499363844011925567769 16675874522883008944175827)
      ·
        refine ⟨25013811784324513416263741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16675874522883008944175827 25013811784324513416263741)
        ·
          refine ⟨9380179419121692531098903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25013811784324513416263741 9380179419121692531098903)
          ·
            refine ⟨14070269128682538796648355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9380179419121692531098903 14070269128682538796648355)
            ·
              refine ⟨21105403693023808194972533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14070269128682538796648355 21105403693023808194972533)
              ·
                refine ⟨1978631596220982018278675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21105403693023808194972533 1978631596220982018278675)
                ·
                  refine ⟨2967947394331473027418013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978631596220982018278675 2967947394331473027418013)
                  ·
                    refine ⟨1112980272874302385281755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2967947394331473027418013 1112980272874302385281755)
                    ·
                      rfl

theorem cell22_3251282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_3251282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251282 prefixEnd_3251282 := by exact prefixLift 3251282
  have htrace : WordTrace (prefixWord ++ tailWord_3251282) baseStart_3251282 baseEnd_3251282 := by
    simpa [prefixWord, tailWord_3251282, baseEnd_3251282] using wordTrace_append hprefix tailTrace_3251282
  have hstable : (prefixWord ++ tailWord_3251282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251282).length < 2 ^ (prefixWord ++ tailWord_3251282).sum := by decide
  have hdescent : baseEnd_3251282 < baseStart_3251282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251325 : List Nat := [1, 4, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_3251325 : Nat := 118140960795 + 3251325 * 2 ^ 59
def prefixEnd_3251325 : Nat := 4983230072969 + 3 ^ 40 * 3251325 * 2
def baseEnd_3251325 : Nat := 1112994992653064606456623

theorem tailTrace_3251325 : CollatzResearch.WordTrace tailWord_3251325 prefixEnd_3251325 1112994992653064606456623 := by
  unfold tailWord_3251325
  simp only [CollatzResearch.WordTrace]
  refine ⟨118585564946012281946843429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79057043297341521297895619 118585564946012281946843429)
  ·
    refine ⟨22234793427377302865033143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118585564946012281946843429 22234793427377302865033143)
    ·
      refine ⟨33352190141065954297549715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22234793427377302865033143 33352190141065954297549715)
      ·
        refine ⟨50028285211598931446324573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33352190141065954297549715 50028285211598931446324573)
        ·
          refine ⟨18760606954349599292371715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50028285211598931446324573 18760606954349599292371715)
          ·
            refine ⟨28140910431524398938557573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18760606954349599292371715 28140910431524398938557573)
            ·
              refine ⟨5276420705910824800979545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28140910431524398938557573 5276420705910824800979545)
              ·
                refine ⟨3957315529433118600734659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5276420705910824800979545 3957315529433118600734659)
                ·
                  refine ⟨5935973294149677901101989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3957315529433118600734659 5935973294149677901101989)
                  ·
                    refine ⟨1112994992653064606456623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5935973294149677901101989 1112994992653064606456623)
                    ·
                      rfl

theorem cell22_3251325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_3251325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251325 prefixEnd_3251325 := by exact prefixLift 3251325
  have htrace : WordTrace (prefixWord ++ tailWord_3251325) baseStart_3251325 baseEnd_3251325 := by
    simpa [prefixWord, tailWord_3251325, baseEnd_3251325] using wordTrace_append hprefix tailTrace_3251325
  have hstable : (prefixWord ++ tailWord_3251325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251325).length < 2 ^ (prefixWord ++ tailWord_3251325).sum := by decide
  have hdescent : baseEnd_3251325 < baseStart_3251325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251338 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_3251338 : Nat := 118140960795 + 3251338 * 2 ^ 59
def prefixEnd_3251338 : Nat := 4983230072969 + 3 ^ 40 * 3251338 * 2
def baseEnd_3251338 : Nat := 1112999442818736905881583

theorem tailTrace_3251338 : CollatzResearch.WordTrace tailWord_3251338 prefixEnd_3251338 1112999442818736905881583 := by
  unfold tailWord_3251338
  simp only [CollatzResearch.WordTrace]
  refine ⟨29646509773741296291766667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79057359396643456778044445 29646509773741296291766667)
  ·
    refine ⟨44469764660611944437650001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29646509773741296291766667 44469764660611944437650001)
    ·
      refine ⟨33352323495458958328237501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44469764660611944437650001 33352323495458958328237501)
      ·
        refine ⟨12507121310797109373089063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33352323495458958328237501 12507121310797109373089063)
        ·
          refine ⟨18760681966195664059633595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12507121310797109373089063 18760681966195664059633595)
          ·
            refine ⟨28141022949293496089450393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18760681966195664059633595 28141022949293496089450393)
            ·
              refine ⟨21105767211970122067087795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28141022949293496089450393 21105767211970122067087795)
              ·
                refine ⟨31658650817955183100631693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21105767211970122067087795 31658650817955183100631693)
                ·
                  refine ⟨11871994056733193662736885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31658650817955183100631693 11871994056733193662736885)
                  ·
                    refine ⟨1112999442818736905881583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11871994056733193662736885 1112999442818736905881583)
                    ·
                      rfl

theorem cell22_3251338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_3251338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251338 prefixEnd_3251338 := by exact prefixLift 3251338
  have htrace : WordTrace (prefixWord ++ tailWord_3251338) baseStart_3251338 baseEnd_3251338 := by
    simpa [prefixWord, tailWord_3251338, baseEnd_3251338] using wordTrace_append hprefix tailTrace_3251338
  have hstable : (prefixWord ++ tailWord_3251338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251338).length < 2 ^ (prefixWord ++ tailWord_3251338).sum := by decide
  have hdescent : baseEnd_3251338 < baseStart_3251338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251357 : List Nat := [1, 4, 2, 1, 1, 2, 5, 2, 4]
def baseStart_3251357 : Nat := 118140960795 + 3251357 * 2 ^ 59
def prefixEnd_3251357 : Nat := 4983230072969 + 3 ^ 40 * 3251357 * 2
def baseEnd_3251357 : Nat := 371001982302342396552175

theorem tailTrace_3251357 : CollatzResearch.WordTrace tailWord_3251357 prefixEnd_3251357 371001982302342396552175 := by
  unfold tailWord_3251357
  simp only [CollatzResearch.WordTrace]
  refine ⟨118586732081896351412008325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79057821387930900941338883 118586732081896351412008325)
  ·
    refine ⟨22235012265355565889751561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118586732081896351412008325 22235012265355565889751561)
    ·
      refine ⟨16676259199016674417313671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22235012265355565889751561 16676259199016674417313671)
      ·
        refine ⟨25014388798525011625970507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16676259199016674417313671 25014388798525011625970507)
        ·
          refine ⟨37521583197787517438955761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25014388798525011625970507 37521583197787517438955761)
          ·
            refine ⟨28141187398340638079216821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37521583197787517438955761 28141187398340638079216821)
            ·
              refine ⟨2638236318594434819926577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28141187398340638079216821 2638236318594434819926577)
              ·
                refine ⟨1978677238945826114944933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638236318594434819926577 1978677238945826114944933)
                ·
                  refine ⟨371001982302342396552175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978677238945826114944933 371001982302342396552175)
                  ·
                    rfl

theorem cell22_3251357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_3251357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251357 prefixEnd_3251357 := by exact prefixLift 3251357
  have htrace : WordTrace (prefixWord ++ tailWord_3251357) baseStart_3251357 baseEnd_3251357 := by
    simpa [prefixWord, tailWord_3251357, baseEnd_3251357] using wordTrace_append hprefix tailTrace_3251357
  have hstable : (prefixWord ++ tailWord_3251357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251357).length < 2 ^ (prefixWord ++ tailWord_3251357).sum := by decide
  have hdescent : baseEnd_3251357 < baseStart_3251357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251428 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_3251428 : Nat := 118140960795 + 3251428 * 2 ^ 59
def prefixEnd_3251428 : Nat := 4983230072969 + 3 ^ 40 * 3251428 * 2
def baseEnd_3251428 : Nat := 1113030251658006671131307

theorem tailTrace_3251428 : CollatzResearch.WordTrace tailWord_3251428 prefixEnd_3251428 1113030251658006671131307 := by
  unfold tailWord_3251428
  simp only [CollatzResearch.WordTrace]
  refine ⟨59294660832319565268921469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79059547776426087025228625 59294660832319565268921469)
  ·
    refine ⟨22235497812119836975845551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59294660832319565268921469 22235497812119836975845551)
    ·
      refine ⟨33353246718179755463768327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22235497812119836975845551 33353246718179755463768327)
      ·
        refine ⟨50029870077269633195652491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33353246718179755463768327 50029870077269633195652491)
        ·
          refine ⟨75044805115904449793478737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50029870077269633195652491 75044805115904449793478737)
          ·
            refine ⟨56283603836928337345109053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75044805115904449793478737 56283603836928337345109053)
            ·
              refine ⟨21106351438848126504415895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56283603836928337345109053 21106351438848126504415895)
              ·
                refine ⟨31659527158272189756623843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21106351438848126504415895 31659527158272189756623843)
                ·
                  refine ⟨47489290737408284634935765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31659527158272189756623843 47489290737408284634935765)
                  ·
                    refine ⟨1113030251658006671131307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47489290737408284634935765 1113030251658006671131307)
                    ·
                      rfl

theorem cell22_3251428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_3251428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251428 prefixEnd_3251428 := by exact prefixLift 3251428
  have htrace : WordTrace (prefixWord ++ tailWord_3251428) baseStart_3251428 baseEnd_3251428 := by
    simpa [prefixWord, tailWord_3251428, baseEnd_3251428] using wordTrace_append hprefix tailTrace_3251428
  have hstable : (prefixWord ++ tailWord_3251428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251428).length < 2 ^ (prefixWord ++ tailWord_3251428).sum := by decide
  have hdescent : baseEnd_3251428 < baseStart_3251428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251464 : List Nat := [2, 1, 3, 2, 5, 1, 1, 2, 5]
def baseStart_3251464 : Nat := 118140960795 + 3251464 * 2 ^ 59
def prefixEnd_3251464 : Nat := 4983230072969 + 3 ^ 40 * 3251464 * 2
def baseEnd_3251464 : Nat := 371014191731238192410399

theorem tailTrace_3251464 : CollatzResearch.WordTrace tailWord_3251464 prefixEnd_3251464 371014191731238192410399 := by
  unfold tailWord_3251464
  simp only [CollatzResearch.WordTrace]
  refine ⟨59295317346254354343076723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79060423128339139124102297 59295317346254354343076723)
  ·
    refine ⟨88942976019381531514615085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59295317346254354343076723 88942976019381531514615085)
    ·
      refine ⟨33353616007268074317980657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88942976019381531514615085 33353616007268074317980657)
      ·
        refine ⟨25015212005451055738485493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33353616007268074317980657 25015212005451055738485493)
        ·
          refine ⟨2345176125511036475483015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25015212005451055738485493 2345176125511036475483015)
          ·
            refine ⟨3517764188266554713224523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345176125511036475483015 3517764188266554713224523)
            ·
              refine ⟨5276646282399832069836785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517764188266554713224523 5276646282399832069836785)
              ·
                refine ⟨3957484711799874052377589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5276646282399832069836785 3957484711799874052377589)
                ·
                  refine ⟨371014191731238192410399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3957484711799874052377589 371014191731238192410399)
                  ·
                    rfl

theorem cell22_3251464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 5].length) (baseStart_3251464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251464 prefixEnd_3251464 := by exact prefixLift 3251464
  have htrace : WordTrace (prefixWord ++ tailWord_3251464) baseStart_3251464 baseEnd_3251464 := by
    simpa [prefixWord, tailWord_3251464, baseEnd_3251464] using wordTrace_append hprefix tailTrace_3251464
  have hstable : (prefixWord ++ tailWord_3251464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251464).length < 2 ^ (prefixWord ++ tailWord_3251464).sum := by decide
  have hdescent : baseEnd_3251464 < baseStart_3251464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251505 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 1, 6]
def baseStart_3251505 : Nat := 118140960795 + 3251505 * 2 ^ 59
def prefixEnd_3251505 : Nat := 4983230072969 + 3 ^ 40 * 3251505 * 2
def baseEnd_3251505 : Nat := 1113056610331604136956071

theorem tailTrace_3251505 : CollatzResearch.WordTrace tailWord_3251505 prefixEnd_3251505 1113056610331604136956071 := by
  unfold tailWord_3251505
  simp only [CollatzResearch.WordTrace]
  refine ⟨118592130085360172688395969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79061420056906781792263979 118592130085360172688395969)
  ·
    refine ⟨88944097564020129516296977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118592130085360172688395969 88944097564020129516296977)
    ·
      refine ⟨66708073173015097137222733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88944097564020129516296977 66708073173015097137222733)
      ·
        refine ⟨25015527439880661426458525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66708073173015097137222733 25015527439880661426458525)
        ·
          refine ⟨9380822789955248034921947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25015527439880661426458525 9380822789955248034921947)
          ·
            refine ⟨14071234184932872052382921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9380822789955248034921947 14071234184932872052382921)
            ·
              refine ⟨10553425638699654039287191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14071234184932872052382921 10553425638699654039287191)
              ·
                refine ⟨15830138458049481058930787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10553425638699654039287191 15830138458049481058930787)
                ·
                  refine ⟨23745207687074221588396181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15830138458049481058930787 23745207687074221588396181)
                  ·
                    refine ⟨1113056610331604136956071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23745207687074221588396181 1113056610331604136956071)
                    ·
                      rfl

theorem cell22_3251505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_3251505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251505 prefixEnd_3251505 := by exact prefixLift 3251505
  have htrace : WordTrace (prefixWord ++ tailWord_3251505) baseStart_3251505 baseEnd_3251505 := by
    simpa [prefixWord, tailWord_3251505, baseEnd_3251505] using wordTrace_append hprefix tailTrace_3251505
  have hstable : (prefixWord ++ tailWord_3251505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251505).length < 2 ^ (prefixWord ++ tailWord_3251505).sum := by decide
  have hdescent : baseEnd_3251505 < baseStart_3251505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251509 : List Nat := [1, 3, 3, 1, 2, 4, 1, 3, 4]
def baseStart_3251509 : Nat := 118140960795 + 3251509 * 2 ^ 59
def prefixEnd_3251509 : Nat := 4983230072969 + 3 ^ 40 * 3251509 * 2
def baseEnd_3251509 : Nat := 371019326537783153285353

theorem tailTrace_3251509 : CollatzResearch.WordTrace tailWord_3251509 prefixEnd_3251509 371019326537783153285353 := by
  unfold tailWord_3251509
  simp only [CollatzResearch.WordTrace]
  refine ⟨118592275977345681371541581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79061517318230454247694387 118592275977345681371541581)
  ·
    refine ⟨44472103491504630514328093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118592275977345681371541581 44472103491504630514328093)
    ·
      refine ⟨16677038809314236442873035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44472103491504630514328093 16677038809314236442873035)
      ·
        refine ⟨25015558213971354664309553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16677038809314236442873035 25015558213971354664309553)
        ·
          refine ⟨18761668660478515998232165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25015558213971354664309553 18761668660478515998232165)
          ·
            refine ⟨3517812873839721749668531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18761668660478515998232165 3517812873839721749668531)
            ·
              refine ⟨5276719310759582624502797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517812873839721749668531 5276719310759582624502797)
              ·
                refine ⟨1978769741534843484188549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5276719310759582624502797 1978769741534843484188549)
                ·
                  refine ⟨371019326537783153285353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978769741534843484188549 371019326537783153285353)
                  ·
                    rfl

theorem cell22_3251509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_3251509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251509 prefixEnd_3251509 := by exact prefixLift 3251509
  have htrace : WordTrace (prefixWord ++ tailWord_3251509) baseStart_3251509 baseEnd_3251509 := by
    simpa [prefixWord, tailWord_3251509, baseEnd_3251509] using wordTrace_append hprefix tailTrace_3251509
  have hstable : (prefixWord ++ tailWord_3251509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251509).length < 2 ^ (prefixWord ++ tailWord_3251509).sum := by decide
  have hdescent : baseEnd_3251509 < baseStart_3251509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251524 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3251524 : Nat := 118140960795 + 3251524 * 2 ^ 59
def prefixEnd_3251524 : Nat := 4983230072969 + 3 ^ 40 * 3251524 * 2
def baseEnd_3251524 : Nat := 1113063114419894420731013

theorem tailTrace_3251524 : CollatzResearch.WordTrace tailWord_3251524 prefixEnd_3251524 1113063114419894420731013 := by
  unfold tailWord_3251524
  simp only [CollatzResearch.WordTrace]
  refine ⟨59296411536145669466668813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79061882048194225955558417 59296411536145669466668813)
  ·
    refine ⟨22236154326054626050000805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59296411536145669466668813 22236154326054626050000805)
    ·
      refine ⟨4169278936135242384375151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22236154326054626050000805 4169278936135242384375151)
      ·
        refine ⟨6253918404202863576562727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4169278936135242384375151 6253918404202863576562727)
        ·
          refine ⟨9380877606304295364844091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6253918404202863576562727 9380877606304295364844091)
          ·
            refine ⟨14071316409456443047266137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9380877606304295364844091 14071316409456443047266137)
            ·
              refine ⟨10553487307092332285449603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14071316409456443047266137 10553487307092332285449603)
              ·
                refine ⟨15830230960638498428174405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10553487307092332285449603 15830230960638498428174405)
                ·
                  refine ⟨2968168305119718455282701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15830230960638498428174405 2968168305119718455282701)
                  ·
                    refine ⟨1113063114419894420731013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2968168305119718455282701 1113063114419894420731013)
                    ·
                      rfl

theorem cell22_3251524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3251524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251524 prefixEnd_3251524 := by exact prefixLift 3251524
  have htrace : WordTrace (prefixWord ++ tailWord_3251524) baseStart_3251524 baseEnd_3251524 := by
    simpa [prefixWord, tailWord_3251524, baseEnd_3251524] using wordTrace_append hprefix tailTrace_3251524
  have hstable : (prefixWord ++ tailWord_3251524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251524).length < 2 ^ (prefixWord ++ tailWord_3251524).sum := by decide
  have hdescent : baseEnd_3251524 < baseStart_3251524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251541 : List Nat := [1, 3, 2, 2, 3, 3, 2, 1, 2, 3]
def baseStart_3251541 : Nat := 118140960795 + 3251541 * 2 ^ 59
def prefixEnd_3251541 : Nat := 4983230072969 + 3 ^ 40 * 3251541 * 2
def baseEnd_3251541 : Nat := 1113068933867312043055961

theorem tailTrace_3251541 : CollatzResearch.WordTrace tailWord_3251541 prefixEnd_3251541 1113068933867312043055961 := by
  unfold tailWord_3251541
  simp only [CollatzResearch.WordTrace]
  refine ⟨118593443113229750836706477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79062295408819833891137651 118593443113229750836706477)
  ·
    refine ⟨44472541167461156563764929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118593443113229750836706477 44472541167461156563764929)
    ·
      refine ⟨33354405875595867422823697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44472541167461156563764929 33354405875595867422823697)
      ·
        refine ⟨25015804406696900567117773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33354405875595867422823697 25015804406696900567117773)
        ·
          refine ⟨9380926652511337712669165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25015804406696900567117773 9380926652511337712669165)
          ·
            refine ⟨3517847494691751642250937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9380926652511337712669165 3517847494691751642250937)
            ·
              refine ⟨2638385621018813731688203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3517847494691751642250937 2638385621018813731688203)
              ·
                refine ⟨3957578431528220597532305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638385621018813731688203 3957578431528220597532305)
                ·
                  refine ⟨2968183823646165448149229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3957578431528220597532305 2968183823646165448149229)
                  ·
                    refine ⟨1113068933867312043055961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2968183823646165448149229 1113068933867312043055961)
                    ·
                      rfl

theorem cell22_3251541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_3251541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251541 prefixEnd_3251541 := by exact prefixLift 3251541
  have htrace : WordTrace (prefixWord ++ tailWord_3251541) baseStart_3251541 baseEnd_3251541 := by
    simpa [prefixWord, tailWord_3251541, baseEnd_3251541] using wordTrace_append hprefix tailTrace_3251541
  have hstable : (prefixWord ++ tailWord_3251541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251541).length < 2 ^ (prefixWord ++ tailWord_3251541).sum := by decide
  have hdescent : baseEnd_3251541 < baseStart_3251541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251580 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_3251580 : Nat := 118140960795 + 3251580 * 2 ^ 59
def prefixEnd_3251580 : Nat := 4983230072969 + 3 ^ 40 * 3251580 * 2
def baseEnd_3251580 : Nat := 1113082284364328941330841

theorem tailTrace_3251580 : CollatzResearch.WordTrace tailWord_3251580 prefixEnd_3251580 1113082284364328941330841 := by
  unfold tailWord_3251580
  simp only [CollatzResearch.WordTrace]
  refine ⟨59297432780044230248688097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79063243706725640331584129 59297432780044230248688097)
  ·
    refine ⟨44473074585033172686516073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59297432780044230248688097 44473074585033172686516073)
    ·
      refine ⟨33354805938774879514887055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44473074585033172686516073 33354805938774879514887055)
      ·
        refine ⟨50032208908162319272330583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33354805938774879514887055 50032208908162319272330583)
        ·
          refine ⟨75048313362243478908495875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50032208908162319272330583 75048313362243478908495875)
          ·
            refine ⟨112572470043365218362743813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75048313362243478908495875 112572470043365218362743813)
            ·
              refine ⟨21107338133130978443014465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112572470043365218362743813 21107338133130978443014465)
              ·
                refine ⟨15830503599848233832260849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21107338133130978443014465 15830503599848233832260849)
                ·
                  refine ⟨11872877699886175374195637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15830503599848233832260849 11872877699886175374195637)
                  ·
                    refine ⟨1113082284364328941330841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11872877699886175374195637 1113082284364328941330841)
                    ·
                      rfl

theorem cell22_3251580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_3251580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251580 prefixEnd_3251580 := by exact prefixLift 3251580
  have htrace : WordTrace (prefixWord ++ tailWord_3251580) baseStart_3251580 baseEnd_3251580 := by
    simpa [prefixWord, tailWord_3251580, baseEnd_3251580] using wordTrace_append hprefix tailTrace_3251580
  have hstable : (prefixWord ++ tailWord_3251580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251580).length < 2 ^ (prefixWord ++ tailWord_3251580).sum := by decide
  have hdescent : baseEnd_3251580 < baseStart_3251580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251595 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 5, 4]
def baseStart_3251595 : Nat := 118140960795 + 3251595 * 2 ^ 59
def prefixEnd_3251595 : Nat := 4983230072969 + 3 ^ 40 * 3251595 * 2
def baseEnd_3251595 : Nat := 1113087419170873902205795

theorem tailTrace_3251595 : CollatzResearch.WordTrace tailWord_3251595 prefixEnd_3251595 1113087419170873902205795 := by
  unfold tailWord_3251595
  simp only [CollatzResearch.WordTrace]
  refine ⟨118595412655034118059172239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79063608436689412039448159 118595412655034118059172239)
  ·
    refine ⟨177893118982551177088758359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118595412655034118059172239 177893118982551177088758359)
    ·
      refine ⟨266839678473826765633137539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177893118982551177088758359 266839678473826765633137539)
      ·
        refine ⟨400259517710740148449706309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266839678473826765633137539 400259517710740148449706309)
        ·
          refine ⟨75048659570763777834319933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400259517710740148449706309 75048659570763777834319933)
          ·
            refine ⟨28143247339036416687869975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75048659570763777834319933 28143247339036416687869975)
            ·
              refine ⟨42214871008554625031804963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28143247339036416687869975 42214871008554625031804963)
              ·
                refine ⟨63322306512831937547707445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42214871008554625031804963 63322306512831937547707445)
                ·
                  refine ⟨5936466235577994145097573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63322306512831937547707445 5936466235577994145097573)
                  ·
                    refine ⟨1113087419170873902205795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5936466235577994145097573 1113087419170873902205795)
                    ·
                      rfl

theorem cell22_3251595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 4].length) (baseStart_3251595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251595 prefixEnd_3251595 := by exact prefixLift 3251595
  have htrace : WordTrace (prefixWord ++ tailWord_3251595) baseStart_3251595 baseEnd_3251595 := by
    simpa [prefixWord, tailWord_3251595, baseEnd_3251595] using wordTrace_append hprefix tailTrace_3251595
  have hstable : (prefixWord ++ tailWord_3251595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251595).length < 2 ^ (prefixWord ++ tailWord_3251595).sum := by decide
  have hdescent : baseEnd_3251595 < baseStart_3251595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251644 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 6]
def baseStart_3251644 : Nat := 118140960795 + 3251644 * 2 ^ 59
def prefixEnd_3251644 : Nat := 4983230072969 + 3 ^ 40 * 3251644 * 2
def baseEnd_3251644 : Nat := 371034730957418035910215

theorem tailTrace_3251644 : CollatzResearch.WordTrace tailWord_3251644 prefixEnd_3251644 371034730957418035910215 := by
  unfold tailWord_3251644
  simp only [CollatzResearch.WordTrace]
  refine ⟨59298599915928299713852993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79064799887904399618470657 59298599915928299713852993)
  ·
    refine ⟨44473949936946224785389745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59298599915928299713852993 44473949936946224785389745)
    ·
      refine ⟨33355462452709668589042309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44473949936946224785389745 33355462452709668589042309)
      ·
        refine ⟨6254149209883062860445433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33355462452709668589042309 6254149209883062860445433)
        ·
          refine ⟨4690611907412297145334075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6254149209883062860445433 4690611907412297145334075)
          ·
            refine ⟨7035917861118445718001113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4690611907412297145334075 7035917861118445718001113)
            ·
              refine ⟨5276938395838834288500835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7035917861118445718001113 5276938395838834288500835)
              ·
                refine ⟨7915407593758251432751253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276938395838834288500835 7915407593758251432751253)
                ·
                  refine ⟨371034730957418035910215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7915407593758251432751253 371034730957418035910215)
                  ·
                    rfl

theorem cell22_3251644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_3251644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251644 prefixEnd_3251644 := by exact prefixLift 3251644
  have htrace : WordTrace (prefixWord ++ tailWord_3251644) baseStart_3251644 baseEnd_3251644 := by
    simpa [prefixWord, tailWord_3251644, baseEnd_3251644] using wordTrace_append hprefix tailTrace_3251644
  have hstable : (prefixWord ++ tailWord_3251644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251644).length < 2 ^ (prefixWord ++ tailWord_3251644).sum := by decide
  have hdescent : baseEnd_3251644 < baseStart_3251644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251655 : List Nat := [1, 1, 4, 1, 1, 3, 2, 9]
def baseStart_3251655 : Nat := 118140960795 + 3251655 * 2 ^ 59
def prefixEnd_3251655 : Nat := 4983230072969 + 3 ^ 40 * 3251655 * 2
def baseEnd_3251655 : Nat := 123678662044117082856179

theorem tailTrace_3251655 : CollatzResearch.WordTrace tailWord_3251655 prefixEnd_3251655 123678662044117082856179 := by
  unfold tailWord_3251655
  simp only [CollatzResearch.WordTrace]
  refine ⟨118597601034816748306356419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79065067356544498870904279 118597601034816748306356419)
  ·
    refine ⟨177896401552225122459534629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118597601034816748306356419 177896401552225122459534629)
    ·
      refine ⟨33355575291042210461162743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177896401552225122459534629 33355575291042210461162743)
      ·
        refine ⟨50033362936563315691744115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33355575291042210461162743 50033362936563315691744115)
        ·
          refine ⟨75050044404844973537616173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50033362936563315691744115 75050044404844973537616173)
          ·
            refine ⟨28143766651816865076606065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75050044404844973537616173 28143766651816865076606065)
            ·
              refine ⟨21107824988862648807454549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28143766651816865076606065 21107824988862648807454549)
              ·
                refine ⟨123678662044117082856179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21107824988862648807454549 123678662044117082856179)
                ·
                  rfl

theorem cell22_3251655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 9].length) (baseStart_3251655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251655 prefixEnd_3251655 := by exact prefixLift 3251655
  have htrace : WordTrace (prefixWord ++ tailWord_3251655) baseStart_3251655 baseEnd_3251655 := by
    simpa [prefixWord, tailWord_3251655, baseEnd_3251655] using wordTrace_append hprefix tailTrace_3251655
  have hstable : (prefixWord ++ tailWord_3251655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251655).length < 2 ^ (prefixWord ++ tailWord_3251655).sum := by decide
  have hdescent : baseEnd_3251655 < baseStart_3251655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251672 : List Nat := [2, 1, 2, 2, 2, 1, 6, 6]
def baseStart_3251672 : Nat := 118140960795 + 3251672 * 2 ^ 59
def prefixEnd_3251672 : Nat := 4983230072969 + 3 ^ 40 * 3251672 * 2
def baseEnd_3251672 : Nat := 123679308649385707558951

theorem tailTrace_3251672 : CollatzResearch.WordTrace tailWord_3251672 prefixEnd_3251672 123679308649385707558951 := by
  unfold tailWord_3251672
  simp only [CollatzResearch.WordTrace]
  refine ⟨59299110537877580104862635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79065480717170106806483513 59299110537877580104862635)
  ·
    refine ⟨88948665806816370157293953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59299110537877580104862635 88948665806816370157293953)
    ·
      refine ⟨66711499355112277617970465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88948665806816370157293953 66711499355112277617970465)
      ·
        refine ⟨50033624516334208213477849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66711499355112277617970465 50033624516334208213477849)
        ·
          refine ⟨37525218387250656160108387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50033624516334208213477849 37525218387250656160108387)
          ·
            refine ⟨56287827580875984240162581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37525218387250656160108387 56287827580875984240162581)
            ·
              refine ⟨2638491917853561761257621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56287827580875984240162581 2638491917853561761257621)
              ·
                refine ⟨123679308649385707558951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2638491917853561761257621 123679308649385707558951)
                ·
                  rfl

theorem cell22_3251672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 6].length) (baseStart_3251672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251672 prefixEnd_3251672 := by exact prefixLift 3251672
  have htrace : WordTrace (prefixWord ++ tailWord_3251672) baseStart_3251672 baseEnd_3251672 := by
    simpa [prefixWord, tailWord_3251672, baseEnd_3251672] using wordTrace_append hprefix tailTrace_3251672
  have hstable : (prefixWord ++ tailWord_3251672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251672).length < 2 ^ (prefixWord ++ tailWord_3251672).sum := by decide
  have hdescent : baseEnd_3251672 < baseStart_3251672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251704 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 3, 3]
def baseStart_3251704 : Nat := 118140960795 + 3251704 * 2 ^ 59
def prefixEnd_3251704 : Nat := 4983230072969 + 3 ^ 40 * 3251704 * 2
def baseEnd_3251704 : Nat := 1113124732098433951230461

theorem tailTrace_3251704 : CollatzResearch.WordTrace tailWord_3251704 prefixEnd_3251704 1113124732098433951230461 := by
  unfold tailWord_3251704
  simp only [CollatzResearch.WordTrace]
  refine ⟨59299694105819614837445083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79066258807759486449926777 59299694105819614837445083)
  ·
    refine ⟨88949541158729422256167625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59299694105819614837445083 88949541158729422256167625)
    ·
      refine ⟨66712155869047066692125719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88949541158729422256167625 66712155869047066692125719)
      ·
        refine ⟨100068233803570600038188579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66712155869047066692125719 100068233803570600038188579)
        ·
          refine ⟨150102350705355900057282869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100068233803570600038188579 150102350705355900057282869)
          ·
            refine ⟨14072095378627115630370269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150102350705355900057282869 14072095378627115630370269)
            ·
              refine ⟨5277035766985168361388851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14072095378627115630370269 5277035766985168361388851)
              ·
                refine ⟨7915553650477752542083277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277035766985168361388851 7915553650477752542083277)
                ·
                  refine ⟨2968332618929157203281229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7915553650477752542083277 2968332618929157203281229)
                  ·
                    refine ⟨1113124732098433951230461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2968332618929157203281229 1113124732098433951230461)
                    ·
                      rfl

theorem cell22_3251704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_3251704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251704 prefixEnd_3251704 := by exact prefixLift 3251704
  have htrace : WordTrace (prefixWord ++ tailWord_3251704) baseStart_3251704 baseEnd_3251704 := by
    simpa [prefixWord, tailWord_3251704, baseEnd_3251704] using wordTrace_append hprefix tailTrace_3251704
  have hstable : (prefixWord ++ tailWord_3251704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251704).length < 2 ^ (prefixWord ++ tailWord_3251704).sum := by decide
  have hdescent : baseEnd_3251704 < baseStart_3251704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251762 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 6]
def baseStart_3251762 : Nat := 118140960795 + 3251762 * 2 ^ 59
def prefixEnd_3251762 : Nat := 4983230072969 + 3 ^ 40 * 3251762 * 2
def baseEnd_3251762 : Nat := 371048195561247044426761

theorem tailTrace_3251762 : CollatzResearch.WordTrace tailWord_3251762 prefixEnd_3251762 371048195561247044426761 := by
  unfold tailWord_3251762
  simp only [CollatzResearch.WordTrace]
  refine ⟨29650375911357276395125385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79067669096952737053667693 29650375911357276395125385)
  ·
    refine ⟨22237781933517957296344039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29650375911357276395125385 22237781933517957296344039)
    ·
      refine ⟨33356672900276935944516059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22237781933517957296344039 33356672900276935944516059)
      ·
        refine ⟨50035009350415403916774089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33356672900276935944516059 50035009350415403916774089)
        ·
          refine ⟨37526257012811552937580567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50035009350415403916774089 37526257012811552937580567)
          ·
            refine ⟨56289385519217329406370851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37526257012811552937580567 56289385519217329406370851)
            ·
              refine ⟨84434078278825994109556277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56289385519217329406370851 84434078278825994109556277)
              ·
                refine ⟨7915694838639936947770901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84434078278825994109556277 7915694838639936947770901)
                ·
                  refine ⟨371048195561247044426761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7915694838639936947770901 371048195561247044426761)
                  ·
                    rfl

theorem cell22_3251762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_3251762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251762 prefixEnd_3251762 := by exact prefixLift 3251762
  have htrace : WordTrace (prefixWord ++ tailWord_3251762) baseStart_3251762 baseEnd_3251762 := by
    simpa [prefixWord, tailWord_3251762, baseEnd_3251762] using wordTrace_append hprefix tailTrace_3251762
  have hstable : (prefixWord ++ tailWord_3251762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251762).length < 2 ^ (prefixWord ++ tailWord_3251762).sum := by decide
  have hdescent : baseEnd_3251762 < baseStart_3251762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251766 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3251766 : Nat := 118140960795 + 3251766 * 2 ^ 59
def prefixEnd_3251766 : Nat := 4983230072969 + 3 ^ 40 * 3251766 * 2
def baseEnd_3251766 : Nat := 1113145955965486456180271

theorem tailTrace_3251766 : CollatzResearch.WordTrace tailWord_3251766 prefixEnd_3251766 1113145955965486456180271 := by
  unfold tailWord_3251766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7412603096088413391477947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79067766358276409509098101 7412603096088413391477947)
  ·
    refine ⟨11118904644132620087216921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7412603096088413391477947 11118904644132620087216921)
    ·
      refine ⟨8339178483099465065412691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11118904644132620087216921 8339178483099465065412691)
      ·
        refine ⟨12508767724649197598119037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8339178483099465065412691 12508767724649197598119037)
        ·
          refine ⟨4690787896743449099294639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12508767724649197598119037 4690787896743449099294639)
          ·
            refine ⟨7036181845115173648941959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4690787896743449099294639 7036181845115173648941959)
            ·
              refine ⟨10554272767672760473412939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7036181845115173648941959 10554272767672760473412939)
              ·
                refine ⟨15831409151509140710119409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10554272767672760473412939 15831409151509140710119409)
                ·
                  refine ⟨11873556863631855532589557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15831409151509140710119409 11873556863631855532589557)
                  ·
                    refine ⟨1113145955965486456180271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11873556863631855532589557 1113145955965486456180271)
                    ·
                      rfl

theorem cell22_3251766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3251766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251766 prefixEnd_3251766 := by exact prefixLift 3251766
  have htrace : WordTrace (prefixWord ++ tailWord_3251766) baseStart_3251766 baseEnd_3251766 := by
    simpa [prefixWord, tailWord_3251766, baseEnd_3251766] using wordTrace_append hprefix tailTrace_3251766
  have hstable : (prefixWord ++ tailWord_3251766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251766).length < 2 ^ (prefixWord ++ tailWord_3251766).sum := by decide
  have hdescent : baseEnd_3251766 < baseStart_3251766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251792 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 1, 6]
def baseStart_3251792 : Nat := 118140960795 + 3251792 * 2 ^ 59
def prefixEnd_3251792 : Nat := 4983230072969 + 3 ^ 40 * 3251792 * 2
def baseEnd_3251792 : Nat := 1113154856296831055030191

theorem tailTrace_3251792 : CollatzResearch.WordTrace tailWord_3251792 prefixEnd_3251792 1113154856296831055030191 := by
  unfold tailWord_3251792
  simp only [CollatzResearch.WordTrace]
  refine ⟨59301298917660210352046815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79068398556880280469395753 59301298917660210352046815)
  ·
    refine ⟨88951948376490315528070223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59301298917660210352046815 88951948376490315528070223)
    ·
      refine ⟨133427922564735473292105335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88951948376490315528070223 133427922564735473292105335)
      ·
        refine ⟨200141883847103209938158003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133427922564735473292105335 200141883847103209938158003)
        ·
          refine ⟨300212825770654814907237005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200141883847103209938158003 300212825770654814907237005)
          ·
            refine ⟨112579809663995555590213877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300212825770654814907237005 112579809663995555590213877)
            ·
              refine ⟨10554357155999583336582551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112579809663995555590213877 10554357155999583336582551)
              ·
                refine ⟨15831535733999375004873827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10554357155999583336582551 15831535733999375004873827)
                ·
                  refine ⟨23747303600999062507310741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15831535733999375004873827 23747303600999062507310741)
                  ·
                    refine ⟨1113154856296831055030191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23747303600999062507310741 1113154856296831055030191)
                    ·
                      rfl

theorem cell22_3251792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_3251792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251792 prefixEnd_3251792 := by exact prefixLift 3251792
  have htrace : WordTrace (prefixWord ++ tailWord_3251792) baseStart_3251792 baseEnd_3251792 := by
    simpa [prefixWord, tailWord_3251792, baseEnd_3251792] using wordTrace_append hprefix tailTrace_3251792
  have hstable : (prefixWord ++ tailWord_3251792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251792).length < 2 ^ (prefixWord ++ tailWord_3251792).sum := by decide
  have hdescent : baseEnd_3251792 < baseStart_3251792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251794 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_3251794 : Nat := 118140960795 + 3251794 * 2 ^ 59
def prefixEnd_3251794 : Nat := 4983230072969 + 3 ^ 40 * 3251794 * 2
def baseEnd_3251794 : Nat := 1113155540937703716480185

theorem tailTrace_3251794 : CollatzResearch.WordTrace tailWord_3251794 prefixEnd_3251794 1113155540937703716480185 := by
  unfold tailWord_3251794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29650667695328293761416609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79068447187542116697110957 29650667695328293761416609)
  ·
    refine ⟨22238000771496220321062457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29650667695328293761416609 22238000771496220321062457)
    ·
      refine ⟨16678500578622165240796843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22238000771496220321062457 16678500578622165240796843)
      ·
        refine ⟨25017750867933247861195265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16678500578622165240796843 25017750867933247861195265)
        ·
          refine ⟨18763313150949935895896449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25017750867933247861195265 18763313150949935895896449)
          ·
            refine ⟨14072484863212451921922337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18763313150949935895896449 14072484863212451921922337)
            ·
              refine ⟨10554363647409338941441753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14072484863212451921922337 10554363647409338941441753)
              ·
                refine ⟨7915772735557004206081315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10554363647409338941441753 7915772735557004206081315)
                ·
                  refine ⟨11873659103335506309121973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7915772735557004206081315 11873659103335506309121973)
                  ·
                    refine ⟨1113155540937703716480185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11873659103335506309121973 1113155540937703716480185)
                    ·
                      rfl

theorem cell22_3251794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_3251794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251794 prefixEnd_3251794 := by exact prefixLift 3251794
  have htrace : WordTrace (prefixWord ++ tailWord_3251794) baseStart_3251794 baseEnd_3251794 := by
    simpa [prefixWord, tailWord_3251794, baseEnd_3251794] using wordTrace_append hprefix tailTrace_3251794
  have hstable : (prefixWord ++ tailWord_3251794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251794).length < 2 ^ (prefixWord ++ tailWord_3251794).sum := by decide
  have hdescent : baseEnd_3251794 < baseStart_3251794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251796 : List Nat := [2, 4, 1, 1, 1, 2, 4, 3, 4]
def baseStart_3251796 : Nat := 118140960795 + 3251796 * 2 ^ 59
def prefixEnd_3251796 : Nat := 4983230072969 + 3 ^ 40 * 3251796 * 2
def baseEnd_3251796 : Nat := 371052075192858792643393

theorem tailTrace_3251796 : CollatzResearch.WordTrace tailWord_3251796 prefixEnd_3251796 371052075192858792643393 := by
  unfold tailWord_3251796
  simp only [CollatzResearch.WordTrace]
  refine ⟨59301371863652964693619621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79068495818203952924826161 59301371863652964693619621)
  ·
    refine ⟨11119007224434930880053679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59301371863652964693619621 11119007224434930880053679)
    ·
      refine ⟨16678510836652396320080519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11119007224434930880053679 16678510836652396320080519)
      ·
        refine ⟨25017766254978594480120779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16678510836652396320080519 25017766254978594480120779)
        ·
          refine ⟨37526649382467891720181169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25017766254978594480120779 37526649382467891720181169)
          ·
            refine ⟨28144987036850918790135877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37526649382467891720181169 28144987036850918790135877)
            ·
              refine ⟨5277185069409547273150477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28144987036850918790135877 5277185069409547273150477)
              ·
                refine ⟨1978944401028580227431429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5277185069409547273150477 1978944401028580227431429)
                ·
                  refine ⟨371052075192858792643393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978944401028580227431429 371052075192858792643393)
                  ·
                    rfl

theorem cell22_3251796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_3251796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251796 prefixEnd_3251796 := by exact prefixLift 3251796
  have htrace : WordTrace (prefixWord ++ tailWord_3251796) baseStart_3251796 baseEnd_3251796 := by
    simpa [prefixWord, tailWord_3251796, baseEnd_3251796] using wordTrace_append hprefix tailTrace_3251796
  have hstable : (prefixWord ++ tailWord_3251796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251796).length < 2 ^ (prefixWord ++ tailWord_3251796).sum := by decide
  have hdescent : baseEnd_3251796 < baseStart_3251796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251811 : List Nat := [1, 1, 1, 5, 1, 3, 3, 2, 2, 3]
def baseStart_3251811 : Nat := 118140960795 + 3251811 * 2 ^ 59
def prefixEnd_3251811 : Nat := 4983230072969 + 3 ^ 40 * 3251811 * 2
def baseEnd_3251811 : Nat := 1113161360385121338805133

theorem tailTrace_3251811 : CollatzResearch.WordTrace tailWord_3251811 prefixEnd_3251811 1113161360385121338805133 := by
  unfold tailWord_3251811
  simp only [CollatzResearch.WordTrace]
  refine ⟨118603290822251586949035287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79068860548167724632690191 118603290822251586949035287)
  ·
    refine ⟨177904936233377380423552931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118603290822251586949035287 177904936233377380423552931)
    ·
      refine ⟨266857404350066070635329397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177904936233377380423552931 266857404350066070635329397)
      ·
        refine ⟨25017881657818694122062131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266857404350066070635329397 25017881657818694122062131)
        ·
          refine ⟨37526822486728041183093197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25017881657818694122062131 37526822486728041183093197)
          ·
            refine ⟨14072558432523015443659949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37526822486728041183093197 14072558432523015443659949)
            ·
              refine ⟨5277209412196130791372481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14072558432523015443659949 5277209412196130791372481)
              ·
                refine ⟨3957907059147098093529361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5277209412196130791372481 3957907059147098093529361)
                ·
                  refine ⟨2968430294360323570147021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3957907059147098093529361 2968430294360323570147021)
                  ·
                    refine ⟨1113161360385121338805133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2968430294360323570147021 1113161360385121338805133)
                    ·
                      rfl

theorem cell22_3251811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 3].length) (baseStart_3251811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251811 prefixEnd_3251811 := by exact prefixLift 3251811
  have htrace : WordTrace (prefixWord ++ tailWord_3251811) baseStart_3251811 baseEnd_3251811 := by
    simpa [prefixWord, tailWord_3251811, baseEnd_3251811] using wordTrace_append hprefix tailTrace_3251811
  have hstable : (prefixWord ++ tailWord_3251811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251811).length < 2 ^ (prefixWord ++ tailWord_3251811).sum := by decide
  have hdescent : baseEnd_3251811 < baseStart_3251811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251841 : List Nat := [1, 2, 4, 2, 1, 4, 2, 6]
def baseStart_3251841 : Nat := 118140960795 + 3251841 * 2 ^ 59
def prefixEnd_3251841 : Nat := 4983230072969 + 3 ^ 40 * 3251841 * 2
def baseEnd_3251841 : Nat := 123685736666467917839449

theorem tailTrace_3251841 : CollatzResearch.WordTrace tailWord_3251841 prefixEnd_3251841 123685736666467917839449 := by
  unfold tailWord_3251841
  simp only [CollatzResearch.WordTrace]
  refine ⟨118604385012142902072627377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79069590008095268048418251 118604385012142902072627377)
  ·
    refine ⟨88953288759107176554470533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118604385012142902072627377 88953288759107176554470533)
    ·
      refine ⟨16678741642332595603963225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88953288759107176554470533 16678741642332595603963225)
      ·
        refine ⟨12509056231749446702972419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16678741642332595603963225 12509056231749446702972419)
        ·
          refine ⟨18763584347624170054458629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12509056231749446702972419 18763584347624170054458629)
          ·
            refine ⟨3518172065179531885210993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18763584347624170054458629 3518172065179531885210993)
            ·
              refine ⟨2638629048884648913908245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3518172065179531885210993 2638629048884648913908245)
              ·
                refine ⟨123685736666467917839449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2638629048884648913908245 123685736666467917839449)
                ·
                  rfl

theorem cell22_3251841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 6].length) (baseStart_3251841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251841 prefixEnd_3251841 := by exact prefixLift 3251841
  have htrace : WordTrace (prefixWord ++ tailWord_3251841) baseStart_3251841 baseEnd_3251841 := by
    simpa [prefixWord, tailWord_3251841, baseEnd_3251841] using wordTrace_append hprefix tailTrace_3251841
  have hstable : (prefixWord ++ tailWord_3251841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251841).length < 2 ^ (prefixWord ++ tailWord_3251841).sum := by decide
  have hdescent : baseEnd_3251841 < baseStart_3251841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251852 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 9]
def baseStart_3251852 : Nat := 118140960795 + 3251852 * 2 ^ 59
def prefixEnd_3251852 : Nat := 4983230072969 + 3 ^ 40 * 3251852 * 2
def baseEnd_3251852 : Nat := 371058465174336966176669

theorem tailTrace_3251852 : CollatzResearch.WordTrace tailWord_3251852 prefixEnd_3251852 371058465174336966176669 := by
  unfold tailWord_3251852
  simp only [CollatzResearch.WordTrace]
  refine ⟨59302393107551525475638905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79069857476735367300851873 59302393107551525475638905)
  ·
    refine ⟨44476794830663644106729179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59302393107551525475638905 44476794830663644106729179)
    ·
      refine ⟨66715192245995466160093769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44476794830663644106729179 66715192245995466160093769)
      ·
        refine ⟨50036394184496599620070327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66715192245995466160093769 50036394184496599620070327)
        ·
          refine ⟨75054591276744899430105491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50036394184496599620070327 75054591276744899430105491)
          ·
            refine ⟨112581886915117349145158237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75054591276744899430105491 112581886915117349145158237)
            ·
              refine ⟨42218207593169005929434339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112581886915117349145158237 42218207593169005929434339)
              ·
                refine ⟨63327311389753508894151509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42218207593169005929434339 63327311389753508894151509)
                ·
                  refine ⟨371058465174336966176669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63327311389753508894151509 371058465174336966176669)
                  ·
                    rfl

theorem cell22_3251852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_3251852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251852 prefixEnd_3251852 := by exact prefixLift 3251852
  have htrace : WordTrace (prefixWord ++ tailWord_3251852) baseStart_3251852 baseEnd_3251852 := by
    simpa [prefixWord, tailWord_3251852, baseEnd_3251852] using wordTrace_append hprefix tailTrace_3251852
  have hstable : (prefixWord ++ tailWord_3251852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251852).length < 2 ^ (prefixWord ++ tailWord_3251852).sum := by decide
  have hdescent : baseEnd_3251852 < baseStart_3251852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251869 : List Nat := [1, 4, 2, 1, 1, 1, 1, 6, 5]
def baseStart_3251869 : Nat := 118140960795 + 3251869 * 2 ^ 59
def prefixEnd_3251869 : Nat := 4983230072969 + 3 ^ 40 * 3251869 * 2
def baseEnd_3251869 : Nat := 371060404990142840284985

theorem tailTrace_3251869 : CollatzResearch.WordTrace tailWord_3251869 prefixEnd_3251869 371060404990142840284985 := by
  unfold tailWord_3251869
  simp only [CollatzResearch.WordTrace]
  refine ⟨118605406256041462854646661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79070270837360975236431107 118605406256041462854646661)
  ·
    refine ⟨22238513673007774285246249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118605406256041462854646661 22238513673007774285246249)
    ·
      refine ⟨16678885254755830713934687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22238513673007774285246249 16678885254755830713934687)
      ·
        refine ⟨25018327882133746070902031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16678885254755830713934687 25018327882133746070902031)
        ·
          refine ⟨37527491823200619106353047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25018327882133746070902031 37527491823200619106353047)
          ·
            refine ⟨56291237734800928659529571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37527491823200619106353047 56291237734800928659529571)
            ·
              refine ⟨84436856602201392989294357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56291237734800928659529571 84436856602201392989294357)
              ·
                refine ⟨3957977653228190296373173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84436856602201392989294357 3957977653228190296373173)
                ·
                  refine ⟨371060404990142840284985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3957977653228190296373173 371060404990142840284985)
                  ·
                    rfl

theorem cell22_3251869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_3251869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251869 prefixEnd_3251869 := by exact prefixLift 3251869
  have htrace : WordTrace (prefixWord ++ tailWord_3251869) baseStart_3251869 baseEnd_3251869 := by
    simpa [prefixWord, tailWord_3251869, baseEnd_3251869] using wordTrace_append hprefix tailTrace_3251869
  have hstable : (prefixWord ++ tailWord_3251869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251869).length < 2 ^ (prefixWord ++ tailWord_3251869).sum := by decide
  have hdescent : baseEnd_3251869 < baseStart_3251869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251873 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 3, 3]
def baseStart_3251873 : Nat := 118140960795 + 3251873 * 2 ^ 59
def prefixEnd_3251873 : Nat := 4983230072969 + 3 ^ 40 * 3251873 * 2
def baseEnd_3251873 : Nat := 1113182584252173843754943

theorem tailTrace_3251873 : CollatzResearch.WordTrace tailWord_3251873 prefixEnd_3251873 1113182584252173843754943 := by
  unfold tailWord_3251873
  simp only [CollatzResearch.WordTrace]
  refine ⟨118605552148026971537792273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79070368098684647691861515 118605552148026971537792273)
  ·
    refine ⟨88954164111020228653344205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118605552148026971537792273 88954164111020228653344205)
    ·
      refine ⟨33357811541632585745004077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88954164111020228653344205 33357811541632585745004077)
      ·
        refine ⟨12509179328112219654376529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33357811541632585745004077 12509179328112219654376529)
        ·
          refine ⟨9381884496084164740782397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12509179328112219654376529 9381884496084164740782397)
          ·
            refine ⟨3518206686031561777793399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9381884496084164740782397 3518206686031561777793399)
            ·
              refine ⟨5277310029047342666690099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3518206686031561777793399 5277310029047342666690099)
              ·
                refine ⟨7915965043571014000035149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277310029047342666690099 7915965043571014000035149)
                ·
                  refine ⟨2968486891339130250013181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7915965043571014000035149 2968486891339130250013181)
                  ·
                    refine ⟨1113182584252173843754943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2968486891339130250013181 1113182584252173843754943)
                    ·
                      rfl

theorem cell22_3251873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_3251873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3251873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3251873 prefixEnd_3251873 := by exact prefixLift 3251873
  have htrace : WordTrace (prefixWord ++ tailWord_3251873) baseStart_3251873 baseEnd_3251873 := by
    simpa [prefixWord, tailWord_3251873, baseEnd_3251873] using wordTrace_append hprefix tailTrace_3251873
  have hstable : (prefixWord ++ tailWord_3251873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251873).length < 2 ^ (prefixWord ++ tailWord_3251873).sum := by decide
  have hdescent : baseEnd_3251873 < baseStart_3251873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252008 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 3, 3]
def baseStart_3252008 : Nat := 118140960795 + 3252008 * 2 ^ 59
def prefixEnd_3252008 : Nat := 4983230072969 + 3 ^ 40 * 3252008 * 2
def baseEnd_3252008 : Nat := 1113228797511078491629529

theorem tailTrace_3252008 : CollatzResearch.WordTrace tailWord_3252008 prefixEnd_3252008 1113228797511078491629529 := by
  unfold tailWord_3252008
  simp only [CollatzResearch.WordTrace]
  refine ⟨59305238001268944796978339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79073650668358593062637785 59305238001268944796978339)
  ·
    refine ⟨88957857001903417195467509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59305238001268944796978339 88957857001903417195467509)
    ·
      refine ⟨8339799093928445362075079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88957857001903417195467509 8339799093928445362075079)
      ·
        refine ⟨12509698640892668043112619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8339799093928445362075079 12509698640892668043112619)
        ·
          refine ⟨18764547961339002064668929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12509698640892668043112619 18764547961339002064668929)
          ·
            refine ⟨14073410971004251548501697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18764547961339002064668929 14073410971004251548501697)
            ·
              refine ⟨10555058228253188661376273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14073410971004251548501697 10555058228253188661376273)
              ·
                refine ⟨7916293671189891496032205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10555058228253188661376273 7916293671189891496032205)
                ·
                  refine ⟨2968610126696209311012077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7916293671189891496032205 2968610126696209311012077)
                  ·
                    refine ⟨1113228797511078491629529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2968610126696209311012077 1113228797511078491629529)
                    ·
                      rfl

theorem cell22_3252008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_3252008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252008 prefixEnd_3252008 := by exact prefixLift 3252008
  have htrace : WordTrace (prefixWord ++ tailWord_3252008) baseStart_3252008 baseEnd_3252008 := by
    simpa [prefixWord, tailWord_3252008, baseEnd_3252008] using wordTrace_append hprefix tailTrace_3252008
  have hstable : (prefixWord ++ tailWord_3252008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252008).length < 2 ^ (prefixWord ++ tailWord_3252008).sum := by decide
  have hdescent : baseEnd_3252008 < baseStart_3252008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252055 : List Nat := [1, 1, 3, 2, 5, 2, 2, 1, 5]
def baseStart_3252055 : Nat := 118140960795 + 3252055 * 2 ^ 59
def prefixEnd_3252055 : Nat := 4983230072969 + 3 ^ 40 * 3252055 * 2
def baseEnd_3252055 : Nat := 371081628857195345234795

theorem tailTrace_3252055 : CollatzResearch.WordTrace tailWord_3252055 prefixEnd_3252055 371081628857195345234795 := by
  unfold tailWord_3252055
  simp only [CollatzResearch.WordTrace]
  refine ⟨118612190233367616620917619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79074793488911744413945079 118612190233367616620917619)
  ·
    refine ⟨177918285350051424931376429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118612190233367616620917619 177918285350051424931376429)
    ·
      refine ⟨66719357006269284349266161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177918285350051424931376429 66719357006269284349266161)
      ·
        refine ⟨50039517754701963261949621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66719357006269284349266161 50039517754701963261949621)
        ·
          refine ⟨4691204789503309055807777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50039517754701963261949621 4691204789503309055807777)
          ·
            refine ⟨3518403592127481791855833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4691204789503309055807777 3518403592127481791855833)
            ·
              refine ⟨2638802694095611343891875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3518403592127481791855833 2638802694095611343891875)
              ·
                refine ⟨3958204041143417015837813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638802694095611343891875 3958204041143417015837813)
                ·
                  refine ⟨371081628857195345234795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3958204041143417015837813 371081628857195345234795)
                  ·
                    rfl

theorem cell22_3252055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 5].length) (baseStart_3252055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252055 prefixEnd_3252055 := by exact prefixLift 3252055
  have htrace : WordTrace (prefixWord ++ tailWord_3252055) baseStart_3252055 baseEnd_3252055 := by
    simpa [prefixWord, tailWord_3252055, baseEnd_3252055] using wordTrace_append hprefix tailTrace_3252055
  have hstable : (prefixWord ++ tailWord_3252055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252055).length < 2 ^ (prefixWord ++ tailWord_3252055).sum := by decide
  have hdescent : baseEnd_3252055 < baseStart_3252055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252068 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_3252068 : Nat := 118140960795 + 3252068 * 2 ^ 59
def prefixEnd_3252068 : Nat := 4983230072969 + 3 ^ 40 * 3252068 * 2
def baseEnd_3252068 : Nat := 1113249336737258335129345

theorem tailTrace_3252068 : CollatzResearch.WordTrace tailWord_3252068 prefixEnd_3252068 1113249336737258335129345 := by
  unfold tailWord_3252068
  simp only [CollatzResearch.WordTrace]
  refine ⟨59306332191160259920570429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79075109588213679894093905 59306332191160259920570429)
  ·
    refine ⟨22239874571685097470213911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59306332191160259920570429 22239874571685097470213911)
    ·
      refine ⟨33359811857527646205320867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22239874571685097470213911 33359811857527646205320867)
      ·
        refine ⟨50039717786291469307981301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33359811857527646205320867 50039717786291469307981301)
        ·
          refine ⟨4691223542464825247623247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50039717786291469307981301 4691223542464825247623247)
          ·
            refine ⟨7036835313697237871434871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4691223542464825247623247 7036835313697237871434871)
            ·
              refine ⟨10555252970545856807152307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7036835313697237871434871 10555252970545856807152307)
              ·
                refine ⟨15832879455818785210728461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10555252970545856807152307 15832879455818785210728461)
                ·
                  refine ⟨5937329795932044454023173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15832879455818785210728461 5937329795932044454023173)
                  ·
                    refine ⟨1113249336737258335129345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5937329795932044454023173 1113249336737258335129345)
                    ·
                      rfl

theorem cell22_3252068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_3252068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252068 prefixEnd_3252068 := by exact prefixLift 3252068
  have htrace : WordTrace (prefixWord ++ tailWord_3252068) baseStart_3252068 baseEnd_3252068 := by
    simpa [prefixWord, tailWord_3252068, baseEnd_3252068] using wordTrace_append hprefix tailTrace_3252068
  have hstable : (prefixWord ++ tailWord_3252068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252068).length < 2 ^ (prefixWord ++ tailWord_3252068).sum := by decide
  have hdescent : baseEnd_3252068 < baseStart_3252068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252081 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 1, 5]
def baseStart_3252081 : Nat := 118140960795 + 3252081 * 2 ^ 59
def prefixEnd_3252081 : Nat := 4983230072969 + 3 ^ 40 * 3252081 * 2
def baseEnd_3252081 : Nat := 1113253786902930634554305

theorem tailTrace_3252081 : CollatzResearch.WordTrace tailWord_3252081 prefixEnd_3252081 1113253786902930634554305 := by
  unfold tailWord_3252081
  simp only [CollatzResearch.WordTrace]
  refine ⟨118613138531273423061364097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79075425687515615374242731 118613138531273423061364097)
  ·
    refine ⟨88959853898455067296023073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118613138531273423061364097 88959853898455067296023073)
    ·
      refine ⟨66719890423841300472017305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88959853898455067296023073 66719890423841300472017305)
      ·
        refine ⟨50039917817880975354012979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66719890423841300472017305 50039917817880975354012979)
        ·
          refine ⟨75059876726821463031019469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50039917817880975354012979 75059876726821463031019469)
          ·
            refine ⟨28147453772558048636632301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75059876726821463031019469 28147453772558048636632301)
            ·
              refine ⟨10555295164709268238737113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28147453772558048636632301 10555295164709268238737113)
              ·
                refine ⟨7916471373531951179052835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10555295164709268238737113 7916471373531951179052835)
                ·
                  refine ⟨11874707060297926768579253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7916471373531951179052835 11874707060297926768579253)
                  ·
                    refine ⟨1113253786902930634554305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11874707060297926768579253 1113253786902930634554305)
                    ·
                      rfl

theorem cell22_3252081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_3252081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252081 prefixEnd_3252081 := by exact prefixLift 3252081
  have htrace : WordTrace (prefixWord ++ tailWord_3252081) baseStart_3252081 baseEnd_3252081 := by
    simpa [prefixWord, tailWord_3252081, baseEnd_3252081] using wordTrace_append hprefix tailTrace_3252081
  have hstable : (prefixWord ++ tailWord_3252081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252081).length < 2 ^ (prefixWord ++ tailWord_3252081).sum := by decide
  have hdescent : baseEnd_3252081 < baseStart_3252081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252085 : List Nat := [1, 3, 4, 1, 1, 1, 5, 1, 1, 4]
def baseStart_3252085 : Nat := 118140960795 + 3252085 * 2 ^ 59
def prefixEnd_3252085 : Nat := 4983230072969 + 3 ^ 40 * 3252085 * 2
def baseEnd_3252085 : Nat := 1113255156184675957454293

theorem tailTrace_3252085 : CollatzResearch.WordTrace tailWord_3252085 prefixEnd_3252085 1113255156184675957454293 := by
  unfold tailWord_3252085
  simp only [CollatzResearch.WordTrace]
  refine ⟨118613284423258931744509709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79075522948839287829673139 118613284423258931744509709)
  ·
    refine ⟨44479981658722099404191141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118613284423258931744509709 44479981658722099404191141)
    ·
      refine ⟨8339996561010393638285839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44479981658722099404191141 8339996561010393638285839)
      ·
        refine ⟨12509994841515590457428759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8339996561010393638285839 12509994841515590457428759)
        ·
          refine ⟨18764992262273385686143139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12509994841515590457428759 18764992262273385686143139)
          ·
            refine ⟨28147488393410078529214709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18764992262273385686143139 28147488393410078529214709)
            ·
              refine ⟨2638827036882194862113879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28147488393410078529214709 2638827036882194862113879)
              ·
                refine ⟨3958240555323292293170819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638827036882194862113879 3958240555323292293170819)
                ·
                  refine ⟨5937360832984938439756229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958240555323292293170819 5937360832984938439756229)
                  ·
                    refine ⟨1113255156184675957454293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5937360832984938439756229 1113255156184675957454293)
                    ·
                      rfl

theorem cell22_3252085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_3252085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252085 prefixEnd_3252085 := by exact prefixLift 3252085
  have htrace : WordTrace (prefixWord ++ tailWord_3252085) baseStart_3252085 baseEnd_3252085 := by
    simpa [prefixWord, tailWord_3252085, baseEnd_3252085] using wordTrace_append hprefix tailTrace_3252085
  have hstable : (prefixWord ++ tailWord_3252085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252085).length < 2 ^ (prefixWord ++ tailWord_3252085).sum := by decide
  have hdescent : baseEnd_3252085 < baseStart_3252085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252096 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 2, 4]
def baseStart_3252096 : Nat := 118140960795 + 3252096 * 2 ^ 59
def prefixEnd_3252096 : Nat := 4983230072969 + 3 ^ 40 * 3252096 * 2
def baseEnd_3252096 : Nat := 1113258921709475595429259

theorem tailTrace_3252096 : CollatzResearch.WordTrace tailWord_3252096 prefixEnd_3252096 1113258921709475595429259 := by
  unfold tailWord_3252096
  simp only [CollatzResearch.WordTrace]
  refine ⟨59306842813109540311580071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79075790417479387082106761 59306842813109540311580071)
  ·
    refine ⟨88960264219664310467370107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59306842813109540311580071 88960264219664310467370107)
    ·
      refine ⟨133440396329496465701055161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88960264219664310467370107 133440396329496465701055161)
      ·
        refine ⟨100080297247122349275791371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133440396329496465701055161 100080297247122349275791371)
        ·
          refine ⟨150120445870683523913687057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100080297247122349275791371 150120445870683523913687057)
          ·
            refine ⟨112590334403012642935265293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150120445870683523913687057 112590334403012642935265293)
            ·
              refine ⟨42221375401129741100724485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112590334403012642935265293 42221375401129741100724485)
              ·
                refine ⟨7916507887711826456385841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42221375401129741100724485 7916507887711826456385841)
                ·
                  refine ⟨5937380915783869842289381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7916507887711826456385841 5937380915783869842289381)
                  ·
                    refine ⟨1113258921709475595429259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5937380915783869842289381 1113258921709475595429259)
                    ·
                      rfl

theorem cell22_3252096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_3252096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252096 prefixEnd_3252096 := by exact prefixLift 3252096
  have htrace : WordTrace (prefixWord ++ tailWord_3252096) baseStart_3252096 baseEnd_3252096 := by
    simpa [prefixWord, tailWord_3252096, baseEnd_3252096] using wordTrace_append hprefix tailTrace_3252096
  have hstable : (prefixWord ++ tailWord_3252096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252096).length < 2 ^ (prefixWord ++ tailWord_3252096).sum := by decide
  have hdescent : baseEnd_3252096 < baseStart_3252096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252100 : List Nat := [2, 3, 2, 1, 1, 1, 6, 2, 4]
def baseStart_3252100 : Nat := 118140960795 + 3252100 * 2 ^ 59
def prefixEnd_3252100 : Nat := 4983230072969 + 3 ^ 40 * 3252100 * 2
def baseEnd_3252100 : Nat := 371086763663740306109749

theorem tailTrace_3252100 : CollatzResearch.WordTrace tailWord_3252100 prefixEnd_3252100 371086763663740306109749 := by
  unfold tailWord_3252100
  simp only [CollatzResearch.WordTrace]
  refine ⟨59306915759102294653152877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79075887678803059537537169 59306915759102294653152877)
  ·
    refine ⟨22240093409663360494932329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59306915759102294653152877 22240093409663360494932329)
    ·
      refine ⟨16680070057247520371199247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22240093409663360494932329 16680070057247520371199247)
      ·
        refine ⟨25020105085871280556798871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16680070057247520371199247 25020105085871280556798871)
        ·
          refine ⟨37530157628806920835198307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25020105085871280556798871 37530157628806920835198307)
          ·
            refine ⟨56295236443210381252797461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37530157628806920835198307 56295236443210381252797461)
            ·
              refine ⟨2638839208275486621224881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56295236443210381252797461 2638839208275486621224881)
              ·
                refine ⟨1979129406206614965918661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638839208275486621224881 1979129406206614965918661)
                ·
                  refine ⟨371086763663740306109749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1979129406206614965918661 371086763663740306109749)
                  ·
                    rfl

theorem cell22_3252100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_3252100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252100 prefixEnd_3252100 := by exact prefixLift 3252100
  have htrace : WordTrace (prefixWord ++ tailWord_3252100) baseStart_3252100 baseEnd_3252100 := by
    simpa [prefixWord, tailWord_3252100, baseEnd_3252100] using wordTrace_append hprefix tailTrace_3252100
  have hstable : (prefixWord ++ tailWord_3252100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252100).length < 2 ^ (prefixWord ++ tailWord_3252100).sum := by decide
  have hdescent : baseEnd_3252100 < baseStart_3252100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252136 : List Nat := [2, 1, 6, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3252136 : Nat := 118140960795 + 3252136 * 2 ^ 59
def prefixEnd_3252136 : Nat := 4983230072969 + 3 ^ 40 * 3252136 * 2
def baseEnd_3252136 : Nat := 1113272614526928824429137

theorem tailTrace_3252136 : CollatzResearch.WordTrace tailWord_3252136 prefixEnd_3252136 1113272614526928824429137 := by
  unfold tailWord_3252136
  simp only [CollatzResearch.WordTrace]
  refine ⟨59307572273037083727308131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79076763030716111636410841 59307572273037083727308131)
  ·
    refine ⟨88961358409555625590962197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59307572273037083727308131 88961358409555625590962197)
    ·
      refine ⟨4170063675447919949576353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88961358409555625590962197 4170063675447919949576353)
      ·
        refine ⟨3127547756585939962182265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4170063675447919949576353 3127547756585939962182265)
        ·
          refine ⟨2345660817439454971636699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3127547756585939962182265 2345660817439454971636699)
          ·
            refine ⟨3518491226159182457455049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345660817439454971636699 3518491226159182457455049)
            ·
              refine ⟨2638868419619386843091287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3518491226159182457455049 2638868419619386843091287)
              ·
                refine ⟨3958302629429080264636931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638868419619386843091287 3958302629429080264636931)
                ·
                  refine ⟨5937453944143620396955397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958302629429080264636931 5937453944143620396955397)
                  ·
                    refine ⟨1113272614526928824429137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5937453944143620396955397 1113272614526928824429137)
                    ·
                      rfl

theorem cell22_3252136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3252136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252136 prefixEnd_3252136 := by exact prefixLift 3252136
  have htrace : WordTrace (prefixWord ++ tailWord_3252136) baseStart_3252136 baseEnd_3252136 := by
    simpa [prefixWord, tailWord_3252136, baseEnd_3252136] using wordTrace_append hprefix tailTrace_3252136
  have hstable : (prefixWord ++ tailWord_3252136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252136).length < 2 ^ (prefixWord ++ tailWord_3252136).sum := by decide
  have hdescent : baseEnd_3252136 < baseStart_3252136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252160 : List Nat := [2, 1, 1, 2, 3, 2, 1, 6, 1, 3]
def baseStart_3252160 : Nat := 118140960795 + 3252160 * 2 ^ 59
def prefixEnd_3252160 : Nat := 4983230072969 + 3 ^ 40 * 3252160 * 2
def baseEnd_3252160 : Nat := 1113280830217400761829063

theorem tailTrace_3252160 : CollatzResearch.WordTrace tailWord_3252160 prefixEnd_3252160 1113280830217400761829063 := by
  unfold tailWord_3252160
  simp only [CollatzResearch.WordTrace]
  refine ⟨59308009948993609776744967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79077346598658146368993289 59308009948993609776744967)
  ·
    refine ⟨88962014923490414665117451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59308009948993609776744967 88962014923490414665117451)
    ·
      refine ⟨133443022385235621997676177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88962014923490414665117451 133443022385235621997676177)
      ·
        refine ⟨100082266788926716498257133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133443022385235621997676177 100082266788926716498257133)
        ·
          refine ⟨37530850045847518686846425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100082266788926716498257133 37530850045847518686846425)
          ·
            refine ⟨28148137534385639015134819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37530850045847518686846425 28148137534385639015134819)
            ·
              refine ⟨42222206301578458522702229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28148137534385639015134819 42222206301578458522702229)
              ·
                refine ⟨1979165920386490243251667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42222206301578458522702229 1979165920386490243251667)
                ·
                  refine ⟨2968748880579735364877501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1979165920386490243251667 2968748880579735364877501)
                  ·
                    refine ⟨1113280830217400761829063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2968748880579735364877501 1113280830217400761829063)
                    ·
                      rfl

theorem cell22_3252160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 1, 3].length) (baseStart_3252160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252160 prefixEnd_3252160 := by exact prefixLift 3252160
  have htrace : WordTrace (prefixWord ++ tailWord_3252160) baseStart_3252160 baseEnd_3252160 := by
    simpa [prefixWord, tailWord_3252160, baseEnd_3252160] using wordTrace_append hprefix tailTrace_3252160
  have hstable : (prefixWord ++ tailWord_3252160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252160).length < 2 ^ (prefixWord ++ tailWord_3252160).sum := by decide
  have hdescent : baseEnd_3252160 < baseStart_3252160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252171 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 2, 5]
def baseStart_3252171 : Nat := 118140960795 + 3252171 * 2 ^ 59
def prefixEnd_3252171 : Nat := 4983230072969 + 3 ^ 40 * 3252171 * 2
def baseEnd_3252171 : Nat := 1113284595742200399804029

theorem tailTrace_3252171 : CollatzResearch.WordTrace tailWord_3252171 prefixEnd_3252171 1113284595742200399804029 := by
  unfold tailWord_3252171
  simp only [CollatzResearch.WordTrace]
  refine ⟨118616421100947368432140367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79077614067298245621426911 118616421100947368432140367)
  ·
    refine ⟨177924631651421052648210551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118616421100947368432140367 177924631651421052648210551)
    ·
      refine ⟨266886947477131578972315827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177924631651421052648210551 266886947477131578972315827)
      ·
        refine ⟨400330421215697368458473741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266886947477131578972315827 400330421215697368458473741)
        ·
          refine ⟨150123907955886513171927653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400330421215697368458473741 150123907955886513171927653)
          ·
            refine ⟨28148232741728721219736435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150123907955886513171927653 28148232741728721219736435)
            ·
              refine ⟨42222349112593081829604653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28148232741728721219736435 42222349112593081829604653)
              ·
                refine ⟨15833380917222405686101745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42222349112593081829604653 15833380917222405686101745)
                ·
                  refine ⟨11875035687916804264576309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15833380917222405686101745 11875035687916804264576309)
                  ·
                    refine ⟨1113284595742200399804029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11875035687916804264576309 1113284595742200399804029)
                    ·
                      rfl

theorem cell22_3252171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_3252171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252171 prefixEnd_3252171 := by exact prefixLift 3252171
  have htrace : WordTrace (prefixWord ++ tailWord_3252171) baseStart_3252171 baseEnd_3252171 := by
    simpa [prefixWord, tailWord_3252171, baseEnd_3252171] using wordTrace_append hprefix tailTrace_3252171
  have hstable : (prefixWord ++ tailWord_3252171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252171).length < 2 ^ (prefixWord ++ tailWord_3252171).sum := by decide
  have hdescent : baseEnd_3252171 < baseStart_3252171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252263 : List Nat := [1, 1, 7, 1, 12]
def baseStart_3252263 : Nat := 118140960795 + 3252263 * 2 ^ 59
def prefixEnd_3252263 : Nat := 4983230072969 + 3 ^ 40 * 3252263 * 2
def baseEnd_3252263 : Nat := 4581547692273015746929

theorem tailTrace_3252263 : CollatzResearch.WordTrace tailWord_3252263 prefixEnd_3252263 4581547692273015746929 := by
  unfold tailWord_3252263
  simp only [CollatzResearch.WordTrace]
  refine ⟨118619776616614068144489443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79079851077742712096326295 118619776616614068144489443)
  ·
    refine ⟨177929664924921102216734165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118619776616614068144489443 177929664924921102216734165)
    ·
      refine ⟨4170226521677838333204707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 177929664924921102216734165 4170226521677838333204707)
      ·
        refine ⟨6255339782516757499807061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170226521677838333204707 6255339782516757499807061)
        ·
          refine ⟨4581547692273015746929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6255339782516757499807061 4581547692273015746929)
          ·
            rfl

theorem cell22_3252263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 12].length) (baseStart_3252263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252263 prefixEnd_3252263 := by exact prefixLift 3252263
  have htrace : WordTrace (prefixWord ++ tailWord_3252263) baseStart_3252263 baseEnd_3252263 := by
    simpa [prefixWord, tailWord_3252263, baseEnd_3252263] using wordTrace_append hprefix tailTrace_3252263
  have hstable : (prefixWord ++ tailWord_3252263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252263).length < 2 ^ (prefixWord ++ tailWord_3252263).sum := by decide
  have hdescent : baseEnd_3252263 < baseStart_3252263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252280 : List Nat := [2, 1, 2, 1, 6, 2, 1, 7]
def baseStart_3252280 : Nat := 118140960795 + 3252280 * 2 ^ 59
def prefixEnd_3252280 : Nat := 4983230072969 + 3 ^ 40 * 3252280 * 2
def baseEnd_3252280 : Nat := 123702434296640049869855

theorem tailTrace_3252280 : CollatzResearch.WordTrace tailWord_3252280 prefixEnd_3252280 123702434296640049869855 := by
  unfold tailWord_3252280
  simp only [CollatzResearch.WordTrace]
  refine ⟨59310198328776240023929147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79080264438368320031905529 59310198328776240023929147)
  ·
    refine ⟨88965297493164360035893721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59310198328776240023929147 88965297493164360035893721)
    ·
      refine ⟨66723973119873270026920291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88965297493164360035893721 66723973119873270026920291)
      ·
        refine ⟨100085959679809905040380437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66723973119873270026920291 100085959679809905040380437)
        ·
          refine ⟨4691529359991089298767833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100085959679809905040380437 4691529359991089298767833)
          ·
            refine ⟨3518647019993316974075875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4691529359991089298767833 3518647019993316974075875)
            ·
              refine ⟨5277970529989975461113813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3518647019993316974075875 5277970529989975461113813)
              ·
                refine ⟨123702434296640049869855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5277970529989975461113813 123702434296640049869855)
                ·
                  rfl

theorem cell22_3252280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 7].length) (baseStart_3252280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252280 prefixEnd_3252280 := by exact prefixLift 3252280
  have htrace : WordTrace (prefixWord ++ tailWord_3252280) baseStart_3252280 baseEnd_3252280 := by
    simpa [prefixWord, tailWord_3252280, baseEnd_3252280] using wordTrace_append hprefix tailTrace_3252280
  have hstable : (prefixWord ++ tailWord_3252280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252280).length < 2 ^ (prefixWord ++ tailWord_3252280).sum := by decide
  have hdescent : baseEnd_3252280 < baseStart_3252280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252295 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 3, 3]
def baseStart_3252295 : Nat := 118140960795 + 3252295 * 2 ^ 59
def prefixEnd_3252295 : Nat := 4983230072969 + 3 ^ 40 * 3252295 * 2
def baseEnd_3252295 : Nat := 1113327043476305409703649

theorem tailTrace_3252295 : CollatzResearch.WordTrace tailWord_3252295 prefixEnd_3252295 1113327043476305409703649 := by
  unfold tailWord_3252295
  simp only [CollatzResearch.WordTrace]
  refine ⟨118620943752498137609654339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79080629168332091739769559 118620943752498137609654339)
  ·
    refine ⟨177931415628747206414481509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118620943752498137609654339 177931415628747206414481509)
    ·
      refine ⟨33362140430390101202715283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177931415628747206414481509 33362140430390101202715283)
      ·
        refine ⟨50043210645585151804072925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33362140430390101202715283 50043210645585151804072925)
        ·
          refine ⟨18766203992094431926527347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50043210645585151804072925 18766203992094431926527347)
          ·
            refine ⟨28149305988141647889791021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18766203992094431926527347 28149305988141647889791021)
            ·
              refine ⟨10555989745553117958671633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28149305988141647889791021 10555989745553117958671633)
              ·
                refine ⟨7916992309164838469003725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10555989745553117958671633 7916992309164838469003725)
                ·
                  refine ⟨2968872115936814425876397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7916992309164838469003725 2968872115936814425876397)
                  ·
                    refine ⟨1113327043476305409703649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2968872115936814425876397 1113327043476305409703649)
                    ·
                      rfl

theorem cell22_3252295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_3252295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252295 prefixEnd_3252295 := by exact prefixLift 3252295
  have htrace : WordTrace (prefixWord ++ tailWord_3252295) baseStart_3252295 baseEnd_3252295 := by
    simpa [prefixWord, tailWord_3252295, baseEnd_3252295] using wordTrace_append hprefix tailTrace_3252295
  have hstable : (prefixWord ++ tailWord_3252295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252295).length < 2 ^ (prefixWord ++ tailWord_3252295).sum := by decide
  have hdescent : baseEnd_3252295 < baseStart_3252295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252308 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 7]
def baseStart_3252308 : Nat := 118140960795 + 3252308 * 2 ^ 59
def prefixEnd_3252308 : Nat := 4983230072969 + 3 ^ 40 * 3252308 * 2
def baseEnd_3252308 : Nat := 371110497880659236376203

theorem tailTrace_3252308 : CollatzResearch.WordTrace tailWord_3252308 prefixEnd_3252308 371110497880659236376203 := by
  unfold tailWord_3252308
  simp only [CollatzResearch.WordTrace]
  refine ⟨59310708950725520414938789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79080945267634027219918385 59310708950725520414938789)
  ·
    refine ⟨11120757928261035077801023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59310708950725520414938789 11120757928261035077801023)
    ·
      refine ⟨16681136892391552616701535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11120757928261035077801023 16681136892391552616701535)
      ·
        refine ⟨25021705338587328925052303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16681136892391552616701535 25021705338587328925052303)
        ·
          refine ⟨37532558007880993387578455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25021705338587328925052303 37532558007880993387578455)
          ·
            refine ⟨56298837011821490081367683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37532558007880993387578455 56298837011821490081367683)
            ·
              refine ⟨84448255517732235122051525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56298837011821490081367683 84448255517732235122051525)
              ·
                refine ⟨15834047909574794085384661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84448255517732235122051525 15834047909574794085384661)
                ·
                  refine ⟨371110497880659236376203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15834047909574794085384661 371110497880659236376203)
                  ·
                    rfl

theorem cell22_3252308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_3252308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252308 prefixEnd_3252308 := by exact prefixLift 3252308
  have htrace : WordTrace (prefixWord ++ tailWord_3252308) baseStart_3252308 baseEnd_3252308 := by
    simpa [prefixWord, tailWord_3252308, baseEnd_3252308] using wordTrace_append hprefix tailTrace_3252308
  have hstable : (prefixWord ++ tailWord_3252308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252308).length < 2 ^ (prefixWord ++ tailWord_3252308).sum := by decide
  have hdescent : baseEnd_3252308 < baseStart_3252308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252312 : List Nat := [2, 1, 2, 2, 1, 4, 1, 5, 1, 3]
def baseStart_3252312 : Nat := 118140960795 + 3252312 * 2 ^ 59
def prefixEnd_3252312 : Nat := 4983230072969 + 3 ^ 40 * 3252312 * 2
def baseEnd_3252312 : Nat := 1113332862923723032028597

theorem tailTrace_3252312 : CollatzResearch.WordTrace tailWord_3252312 prefixEnd_3252312 1113332862923723032028597 := by
  unfold tailWord_3252312
  simp only [CollatzResearch.WordTrace]
  refine ⟨59310781896718274756511595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79081042528957699675348793 59310781896718274756511595)
  ·
    refine ⟨88966172845077412134767393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59310781896718274756511595 88966172845077412134767393)
    ·
      refine ⟨66724629633808059101075545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88966172845077412134767393 66724629633808059101075545)
      ·
        refine ⟨50043472225356044325806659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66724629633808059101075545 50043472225356044325806659)
        ·
          refine ⟨75065208338034066488709989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50043472225356044325806659 75065208338034066488709989)
          ·
            refine ⟨14074726563381387466633123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75065208338034066488709989 14074726563381387466633123)
            ·
              refine ⟨21112089845072081199949685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14074726563381387466633123 21112089845072081199949685)
              ·
                refine ⟨1979258422975507612495283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21112089845072081199949685 1979258422975507612495283)
                ·
                  refine ⟨2968887634463261418742925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1979258422975507612495283 2968887634463261418742925)
                  ·
                    refine ⟨1113332862923723032028597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2968887634463261418742925 1113332862923723032028597)
                    ·
                      rfl

theorem cell22_3252312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_3252312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252312 prefixEnd_3252312 := by exact prefixLift 3252312
  have htrace : WordTrace (prefixWord ++ tailWord_3252312) baseStart_3252312 baseEnd_3252312 := by
    simpa [prefixWord, tailWord_3252312, baseEnd_3252312] using wordTrace_append hprefix tailTrace_3252312
  have hstable : (prefixWord ++ tailWord_3252312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252312).length < 2 ^ (prefixWord ++ tailWord_3252312).sum := by decide
  have hdescent : baseEnd_3252312 < baseStart_3252312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252318 : List Nat := [4, 4, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3252318 : Nat := 118140960795 + 3252318 * 2 ^ 59
def prefixEnd_3252318 : Nat := 4983230072969 + 3 ^ 40 * 3252318 * 2
def baseEnd_3252318 : Nat := 1113334916846341016378579

theorem tailTrace_3252318 : CollatzResearch.WordTrace tailWord_3252318 prefixEnd_3252318 1113334916846341016378579 := by
  unfold tailWord_3252318
  simp only [CollatzResearch.WordTrace]
  refine ⟨14827722828926851567217701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79081188420943208358494405 14827722828926851567217701)
  ·
    refine ⟨2780198030423784668853319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14827722828926851567217701 2780198030423784668853319)
    ·
      refine ⟨4170297045635677003279979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2780198030423784668853319 4170297045635677003279979)
      ·
        refine ⟨6255445568453515504919969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170297045635677003279979 6255445568453515504919969)
        ·
          refine ⟨4691584176340136628689977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6255445568453515504919969 4691584176340136628689977)
          ·
            refine ⟨3518688132255102471517483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4691584176340136628689977 3518688132255102471517483)
            ·
              refine ⟨5278032198382653707276225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3518688132255102471517483 5278032198382653707276225)
              ·
                refine ⟨3958524148786990280457169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5278032198382653707276225 3958524148786990280457169)
                ·
                  refine ⟨2968893111590242710342877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3958524148786990280457169 2968893111590242710342877)
                  ·
                    refine ⟨1113334916846341016378579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2968893111590242710342877 1113334916846341016378579)
                    ·
                      rfl

theorem cell22_3252318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3252318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252318 prefixEnd_3252318 := by exact prefixLift 3252318
  have htrace : WordTrace (prefixWord ++ tailWord_3252318) baseStart_3252318 baseEnd_3252318 := by
    simpa [prefixWord, tailWord_3252318, baseEnd_3252318] using wordTrace_append hprefix tailTrace_3252318
  have hstable : (prefixWord ++ tailWord_3252318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252318).length < 2 ^ (prefixWord ++ tailWord_3252318).sum := by decide
  have hdescent : baseEnd_3252318 < baseStart_3252318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252323 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 2, 5]
def baseStart_3252323 : Nat := 118140960795 + 3252323 * 2 ^ 59
def prefixEnd_3252323 : Nat := 4983230072969 + 3 ^ 40 * 3252323 * 2
def baseEnd_3252323 : Nat := 1113336628448522670003563

theorem tailTrace_3252323 : CollatzResearch.WordTrace tailWord_3252323 prefixEnd_3252323 1113336628448522670003563 := by
  unfold tailWord_3252323
  simp only [CollatzResearch.WordTrace]
  refine ⟨118621964996396698391673623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79081309997597798927782415 118621964996396698391673623)
  ·
    refine ⟨177932947494595047587510435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118621964996396698391673623 177932947494595047587510435)
    ·
      refine ⟨266899421241892571381265653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177932947494595047587510435 266899421241892571381265653)
      ·
        refine ⟨25021820741427428566993655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266899421241892571381265653 25021820741427428566993655)
        ·
          refine ⟨37532731112141142850490483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25021820741427428566993655 37532731112141142850490483)
          ·
            refine ⟨56299096668211714275735725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37532731112141142850490483 56299096668211714275735725)
            ·
              refine ⟨21112161250579392853400897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56299096668211714275735725 21112161250579392853400897)
              ·
                refine ⟨15834120937934544640050673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21112161250579392853400897 15834120937934544640050673)
                ·
                  refine ⟨11875590703450908480038005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15834120937934544640050673 11875590703450908480038005)
                  ·
                    refine ⟨1113336628448522670003563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11875590703450908480038005 1113336628448522670003563)
                    ·
                      rfl

theorem cell22_3252323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_3252323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252323 prefixEnd_3252323 := by exact prefixLift 3252323
  have htrace : WordTrace (prefixWord ++ tailWord_3252323) baseStart_3252323 baseEnd_3252323 := by
    simpa [prefixWord, tailWord_3252323, baseEnd_3252323] using wordTrace_append hprefix tailTrace_3252323
  have hstable : (prefixWord ++ tailWord_3252323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252323).length < 2 ^ (prefixWord ++ tailWord_3252323).sum := by decide
  have hdescent : baseEnd_3252323 < baseStart_3252323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252325 : List Nat := [1, 3, 1, 3, 2, 2, 3, 2, 5]
def baseStart_3252325 : Nat := 118140960795 + 3252325 * 2 ^ 59
def prefixEnd_3252325 : Nat := 4983230072969 + 3 ^ 40 * 3252325 * 2
def baseEnd_3252325 : Nat := 371112437696465110484519

theorem tailTrace_3252325 : CollatzResearch.WordTrace tailWord_3252325 prefixEnd_3252325 371112437696465110484519 := by
  unfold tailWord_3252325
  simp only [CollatzResearch.WordTrace]
  refine ⟨118622037942389452733246429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79081358628259635155497619 118622037942389452733246429)
  ·
    refine ⟨44483264228396044774967411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118622037942389452733246429 44483264228396044774967411)
    ·
      refine ⟨66724896342594067162451117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44483264228396044774967411 66724896342594067162451117)
      ·
        refine ⟨25021836128472775185919169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66724896342594067162451117 25021836128472775185919169)
        ·
          refine ⟨18766377096354581389439377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25021836128472775185919169 18766377096354581389439377)
          ·
            refine ⟨14074782822265936042079533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18766377096354581389439377 14074782822265936042079533)
            ·
              refine ⟨5278043558349726015779825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14074782822265936042079533 5278043558349726015779825)
              ·
                refine ⟨3958532668762294511834869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5278043558349726015779825 3958532668762294511834869)
                ·
                  refine ⟨371112437696465110484519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3958532668762294511834869 371112437696465110484519)
                  ·
                    rfl

theorem cell22_3252325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_3252325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252325 prefixEnd_3252325 := by exact prefixLift 3252325
  have htrace : WordTrace (prefixWord ++ tailWord_3252325) baseStart_3252325 baseEnd_3252325 := by
    simpa [prefixWord, tailWord_3252325, baseEnd_3252325] using wordTrace_append hprefix tailTrace_3252325
  have hstable : (prefixWord ++ tailWord_3252325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252325).length < 2 ^ (prefixWord ++ tailWord_3252325).sum := by decide
  have hdescent : baseEnd_3252325 < baseStart_3252325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252355 : List Nat := [1, 1, 1, 3, 3, 3, 1, 4, 1, 4]
def baseStart_3252355 : Nat := 118140960795 + 3252355 * 2 ^ 59
def prefixEnd_3252355 : Nat := 4983230072969 + 3 ^ 40 * 3252355 * 2
def baseEnd_3252355 : Nat := 1113347582702485253203465

theorem tailTrace_3252355 : CollatzResearch.WordTrace tailWord_3252355 prefixEnd_3252355 1113347582702485253203465 := by
  unfold tailWord_3252355
  simp only [CollatzResearch.WordTrace]
  refine ⟨118623132132280767856838519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79082088088187178571225679 118623132132280767856838519)
  ·
    refine ⟨177934698198421151785257779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118623132132280767856838519 177934698198421151785257779)
    ·
      refine ⟨266902047297631727677886669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177934698198421151785257779 266902047297631727677886669)
      ·
        refine ⟨100088267736611897879207501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266902047297631727677886669 100088267736611897879207501)
        ·
          refine ⟨37533100401229461704702813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100088267736611897879207501 37533100401229461704702813)
          ·
            refine ⟨14074912650461048139263555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37533100401229461704702813 14074912650461048139263555)
            ·
              refine ⟨21112368975691572208895333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14074912650461048139263555 21112368975691572208895333)
              ·
                refine ⟨3958569182942169789167875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21112368975691572208895333 3958569182942169789167875)
                ·
                  refine ⟨5937853774413254683751813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958569182942169789167875 5937853774413254683751813)
                  ·
                    refine ⟨1113347582702485253203465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5937853774413254683751813 1113347582702485253203465)
                    ·
                      rfl

theorem cell22_3252355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 4].length) (baseStart_3252355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252355 prefixEnd_3252355 := by exact prefixLift 3252355
  have htrace : WordTrace (prefixWord ++ tailWord_3252355) baseStart_3252355 baseEnd_3252355 := by
    simpa [prefixWord, tailWord_3252355, baseEnd_3252355] using wordTrace_append hprefix tailTrace_3252355
  have hstable : (prefixWord ++ tailWord_3252355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252355).length < 2 ^ (prefixWord ++ tailWord_3252355).sum := by decide
  have hdescent : baseEnd_3252355 < baseStart_3252355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252368 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 3, 5]
def baseStart_3252368 : Nat := 118140960795 + 3252368 * 2 ^ 59
def prefixEnd_3252368 : Nat := 4983230072969 + 3 ^ 40 * 3252368 * 2
def baseEnd_3252368 : Nat := 1113352032868157552628425

theorem tailTrace_3252368 : CollatzResearch.WordTrace tailWord_3252368 prefixEnd_3252368 1113352032868157552628425 := by
  unfold tailWord_3252368
  simp only [CollatzResearch.WordTrace]
  refine ⟨59311803140616835538530879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79082404187489114051374505 59311803140616835538530879)
  ·
    refine ⟨88967704710925253307796319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59311803140616835538530879 88967704710925253307796319)
    ·
      refine ⟨133451557066387879961694479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88967704710925253307796319 133451557066387879961694479)
      ·
        refine ⟨200177335599581819942541719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133451557066387879961694479 200177335599581819942541719)
        ·
          refine ⟨300266003399372729913812579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200177335599581819942541719 300266003399372729913812579)
          ·
            refine ⟨450399005099059094870718869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300266003399372729913812579 450399005099059094870718869)
            ·
              refine ⟨21112453364018395072064947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 450399005099059094870718869 21112453364018395072064947)
              ·
                refine ⟨31668680046027592608097421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21112453364018395072064947 31668680046027592608097421)
                ·
                  refine ⟨11875755017260347228036533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31668680046027592608097421 11875755017260347228036533)
                  ·
                    refine ⟨1113352032868157552628425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11875755017260347228036533 1113352032868157552628425)
                    ·
                      rfl

theorem cell22_3252368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_3252368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252368 prefixEnd_3252368 := by exact prefixLift 3252368
  have htrace : WordTrace (prefixWord ++ tailWord_3252368) baseStart_3252368 baseEnd_3252368 := by
    simpa [prefixWord, tailWord_3252368, baseEnd_3252368] using wordTrace_append hprefix tailTrace_3252368
  have hstable : (prefixWord ++ tailWord_3252368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252368).length < 2 ^ (prefixWord ++ tailWord_3252368).sum := by decide
  have hdescent : baseEnd_3252368 < baseStart_3252368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252402 : List Nat := [3, 2, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_3252402 : Nat := 118140960795 + 3252402 * 2 ^ 59
def prefixEnd_3252402 : Nat := 4983230072969 + 3 ^ 40 * 3252402 * 2
def baseEnd_3252402 : Nat := 1113363671762992797278321

theorem tailTrace_3252402 : CollatzResearch.WordTrace tailWord_3252402 prefixEnd_3252402 1113363671762992797278321 := by
  unfold tailWord_3252402
  simp only [CollatzResearch.WordTrace]
  refine ⟨29656211590777623720949865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79083230908740329922532973 29656211590777623720949865)
  ·
    refine ⟨22242158693083217790712399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29656211590777623720949865 22242158693083217790712399)
    ·
      refine ⟨33363238039624826686068599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22242158693083217790712399 33363238039624826686068599)
      ·
        refine ⟨50044857059437240029102899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33363238039624826686068599 50044857059437240029102899)
        ·
          refine ⟨75067285589155860043654349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50044857059437240029102899 75067285589155860043654349)
          ·
            refine ⟨28150232095933447516370381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75067285589155860043654349 28150232095933447516370381)
            ·
              refine ⟨10556337035975042818638893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28150232095933447516370381 10556337035975042818638893)
              ·
                refine ⟨3958626388490641056989585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10556337035975042818638893 3958626388490641056989585)
                ·
                  refine ⟨2968969791367980792742189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3958626388490641056989585 2968969791367980792742189)
                  ·
                    refine ⟨1113363671762992797278321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2968969791367980792742189 1113363671762992797278321)
                    ·
                      rfl

theorem cell22_3252402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_3252402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252402 prefixEnd_3252402 := by exact prefixLift 3252402
  have htrace : WordTrace (prefixWord ++ tailWord_3252402) baseStart_3252402 baseEnd_3252402 := by
    simpa [prefixWord, tailWord_3252402, baseEnd_3252402] using wordTrace_append hprefix tailTrace_3252402
  have hstable : (prefixWord ++ tailWord_3252402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252402).length < 2 ^ (prefixWord ++ tailWord_3252402).sum := by decide
  have hdescent : baseEnd_3252402 < baseStart_3252402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252438 : List Nat := [5, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_3252438 : Nat := 118140960795 + 3252438 * 2 ^ 59
def prefixEnd_3252438 : Nat := 4983230072969 + 3 ^ 40 * 3252438 * 2
def baseEnd_3252438 : Nat := 371125331766233567792737

theorem tailTrace_3252438 : CollatzResearch.WordTrace tailWord_3252438 prefixEnd_3252438 371125331766233567792737 := by
  unfold tailWord_3252438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7414134961936254564506873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79084106260653382021406645 7414134961936254564506873)
  ·
    refine ⟨5560601221452190923380155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7414134961936254564506873 5560601221452190923380155)
    ·
      refine ⟨8340901832178286385070233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5560601221452190923380155 8340901832178286385070233)
      ·
        refine ⟨6255676374133714788802675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8340901832178286385070233 6255676374133714788802675)
        ·
          refine ⟨9383514561200572183204013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6255676374133714788802675 9383514561200572183204013)
          ·
            refine ⟨3518817960450214568701505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9383514561200572183204013 3518817960450214568701505)
            ·
              refine ⟨2639113470337660926526129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3518817960450214568701505 2639113470337660926526129)
              ·
                refine ⟨1979335102753245694894597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2639113470337660926526129 1979335102753245694894597)
                ·
                  refine ⟨371125331766233567792737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1979335102753245694894597 371125331766233567792737)
                  ·
                    rfl

theorem cell22_3252438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_3252438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252438 prefixEnd_3252438 := by exact prefixLift 3252438
  have htrace : WordTrace (prefixWord ++ tailWord_3252438) baseStart_3252438 baseEnd_3252438 := by
    simpa [prefixWord, tailWord_3252438, baseEnd_3252438] using wordTrace_append hprefix tailTrace_3252438
  have hstable : (prefixWord ++ tailWord_3252438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252438).length < 2 ^ (prefixWord ++ tailWord_3252438).sum := by decide
  have hdescent : baseEnd_3252438 < baseStart_3252438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252460 : List Nat := [2, 2, 1, 1, 2, 3, 1, 5, 5]
def baseStart_3252460 : Nat := 118140960795 + 3252460 * 2 ^ 59
def prefixEnd_3252460 : Nat := 4983230072969 + 3 ^ 40 * 3252460 * 2
def baseEnd_3252460 : Nat := 371127842116099993109381

theorem tailTrace_3252460 : CollatzResearch.WordTrace tailWord_3252460 prefixEnd_3252460 371127842116099993109381 := by
  unfold tailWord_3252460
  simp only [CollatzResearch.WordTrace]
  refine ⟨59313480898450185394705417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79084641197933580526273889 59313480898450185394705417)
  ·
    refine ⟨44485110673837639046029063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59313480898450185394705417 44485110673837639046029063)
    ·
      refine ⟨66727666010756458569043595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44485110673837639046029063 66727666010756458569043595)
      ·
        refine ⟨100091499016134687853565393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66727666010756458569043595 100091499016134687853565393)
        ·
          refine ⟨75068624262101015890174045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100091499016134687853565393 75068624262101015890174045)
          ·
            refine ⟨28150734098287880958815267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75068624262101015890174045 28150734098287880958815267)
            ·
              refine ⟨42226101147431821438222901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28150734098287880958815267 42226101147431821438222901)
              ·
                refine ⟨3958696982571733259833397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42226101147431821438222901 3958696982571733259833397)
                ·
                  refine ⟨371127842116099993109381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3958696982571733259833397 371127842116099993109381)
                  ·
                    rfl

theorem cell22_3252460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_3252460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252460 prefixEnd_3252460 := by exact prefixLift 3252460
  have htrace : WordTrace (prefixWord ++ tailWord_3252460) baseStart_3252460 baseEnd_3252460 := by
    simpa [prefixWord, tailWord_3252460, baseEnd_3252460] using wordTrace_append hprefix tailTrace_3252460
  have hstable : (prefixWord ++ tailWord_3252460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252460).length < 2 ^ (prefixWord ++ tailWord_3252460).sum := by decide
  have hdescent : baseEnd_3252460 < baseStart_3252460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252535 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 6, 4]
def baseStart_3252535 : Nat := 118140960795 + 3252535 * 2 ^ 59
def prefixEnd_3252535 : Nat := 4983230072969 + 3 ^ 40 * 3252535 * 2
def baseEnd_3252535 : Nat := 1113409200381024783702913

theorem tailTrace_3252535 : CollatzResearch.WordTrace tailWord_3252535 prefixEnd_3252535 1113409200381024783702913 := by
  unfold tailWord_3252535
  simp only [CollatzResearch.WordTrace]
  refine ⟨118629697271628658598391059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79086464847752439065594039 118629697271628658598391059)
  ·
    refine ⟨177944545907442987897586589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118629697271628658598391059 177944545907442987897586589)
    ·
      refine ⟨66729204715291120461594971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177944545907442987897586589 66729204715291120461594971)
      ·
        refine ⟨100093807072936680692392457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66729204715291120461594971 100093807072936680692392457)
        ·
          refine ⟨75070355304702510519294343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100093807072936680692392457 75070355304702510519294343)
          ·
            refine ⟨112605532957053765778941515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75070355304702510519294343 112605532957053765778941515)
            ·
              refine ⟨168908299435580648668412273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112605532957053765778941515 168908299435580648668412273)
              ·
                refine ⟨126681224576685486501309205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168908299435580648668412273 126681224576685486501309205)
                ·
                  refine ⟨5938182402032132179748869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126681224576685486501309205 5938182402032132179748869)
                  ·
                    refine ⟨1113409200381024783702913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5938182402032132179748869 1113409200381024783702913)
                    ·
                      rfl

theorem cell22_3252535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_3252535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252535 prefixEnd_3252535 := by exact prefixLift 3252535
  have htrace : WordTrace (prefixWord ++ tailWord_3252535) baseStart_3252535 baseEnd_3252535 := by
    simpa [prefixWord, tailWord_3252535, baseEnd_3252535] using wordTrace_append hprefix tailTrace_3252535
  have hstable : (prefixWord ++ tailWord_3252535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252535).length < 2 ^ (prefixWord ++ tailWord_3252535).sum := by decide
  have hdescent : baseEnd_3252535 < baseStart_3252535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252616 : List Nat := [2, 1, 3, 3, 1, 1, 3, 4, 1, 3]
def baseStart_3252616 : Nat := 118140960795 + 3252616 * 2 ^ 59
def prefixEnd_3252616 : Nat := 4983230072969 + 3 ^ 40 * 3252616 * 2
def baseEnd_3252616 : Nat := 1113436928336367572427665

theorem tailTrace_3252616 : CollatzResearch.WordTrace tailWord_3252616 prefixEnd_3252616 1113436928336367572427665 := by
  unfold tailWord_3252616
  simp only [CollatzResearch.WordTrace]
  refine ⟨59316325792167604716044851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79088434389556806288059801 59316325792167604716044851)
  ·
    refine ⟨88974488688251407074067277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59316325792167604716044851 88974488688251407074067277)
    ·
      refine ⟨33365433258094277652775229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88974488688251407074067277 33365433258094277652775229)
      ·
        refine ⟨12512037471785354119790711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33365433258094277652775229 12512037471785354119790711)
        ·
          refine ⟨18768056207678031179686067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12512037471785354119790711 18768056207678031179686067)
          ·
            refine ⟨28152084311517046769529101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18768056207678031179686067 28152084311517046769529101)
            ·
              refine ⟨10557031616818892538573413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28152084311517046769529101 10557031616818892538573413)
              ·
                refine ⟨1979443428153542350982515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10557031616818892538573413 1979443428153542350982515)
                ·
                  refine ⟨2969165142230313526473773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1979443428153542350982515 2969165142230313526473773)
                  ·
                    refine ⟨1113436928336367572427665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2969165142230313526473773 1113436928336367572427665)
                    ·
                      rfl

theorem cell22_3252616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_3252616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252616 prefixEnd_3252616 := by exact prefixLift 3252616
  have htrace : WordTrace (prefixWord ++ tailWord_3252616) baseStart_3252616 baseEnd_3252616 := by
    simpa [prefixWord, tailWord_3252616, baseEnd_3252616] using wordTrace_append hprefix tailTrace_3252616
  have hstable : (prefixWord ++ tailWord_3252616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252616).length < 2 ^ (prefixWord ++ tailWord_3252616).sum := by decide
  have hdescent : baseEnd_3252616 < baseStart_3252616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252625 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 1, 10]
def baseStart_3252625 : Nat := 118140960795 + 3252625 * 2 ^ 59
def prefixEnd_3252625 : Nat := 4983230072969 + 3 ^ 40 * 3252625 * 2
def baseEnd_3252625 : Nat := 1113440009220294548952637

theorem tailTrace_3252625 : CollatzResearch.WordTrace tailWord_3252625 prefixEnd_3252625 1113440009220294548952637 := by
  unfold tailWord_3252625
  simp only [CollatzResearch.WordTrace]
  refine ⟨118632979841302603969167329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79088653227535069312778219 118632979841302603969167329)
  ·
    refine ⟨88974734880976952976875497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118632979841302603969167329 88974734880976952976875497)
    ·
      refine ⟨66731051160732714732656623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88974734880976952976875497 66731051160732714732656623)
      ·
        refine ⟨100096576741099072098984935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66731051160732714732656623 100096576741099072098984935)
        ·
          refine ⟨150144865111648608148477403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100096576741099072098984935 150144865111648608148477403)
          ·
            refine ⟨225217297667472912222716105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150144865111648608148477403 225217297667472912222716105)
            ·
              refine ⟨168912973250604684167037079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225217297667472912222716105 168912973250604684167037079)
              ·
                refine ⟨253369459875907026250555619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168912973250604684167037079 253369459875907026250555619)
                ·
                  refine ⟨380054189813860539375833429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253369459875907026250555619 380054189813860539375833429)
                  ·
                    refine ⟨1113440009220294548952637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 380054189813860539375833429 1113440009220294548952637)
                    ·
                      rfl

theorem cell22_3252625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_3252625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252625 prefixEnd_3252625 := by exact prefixLift 3252625
  have htrace : WordTrace (prefixWord ++ tailWord_3252625) baseStart_3252625 baseEnd_3252625 := by
    simpa [prefixWord, tailWord_3252625, baseEnd_3252625] using wordTrace_append hprefix tailTrace_3252625
  have hstable : (prefixWord ++ tailWord_3252625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252625).length < 2 ^ (prefixWord ++ tailWord_3252625).sum := by decide
  have hdescent : baseEnd_3252625 < baseStart_3252625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252689 : List Nat := [1, 2, 2, 1, 2, 1, 1, 7, 2, 3]
def baseStart_3252689 : Nat := 118140960795 + 3252689 * 2 ^ 59
def prefixEnd_3252689 : Nat := 4983230072969 + 3 ^ 40 * 3252689 * 2
def baseEnd_3252689 : Nat := 1113461917728219715352441

theorem tailTrace_3252689 : CollatzResearch.WordTrace tailWord_3252689 prefixEnd_3252689 1113461917728219715352441 := by
  unfold tailWord_3252689
  simp only [CollatzResearch.WordTrace]
  refine ⟨118635314113070742899497121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79090209408713828599664747 118635314113070742899497121)
  ·
    refine ⟨88976485584803057174622841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118635314113070742899497121 88976485584803057174622841)
    ·
      refine ⟨66732364188602292880967131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88976485584803057174622841 66732364188602292880967131)
      ·
        refine ⟨100098546282903439321450697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66732364188602292880967131 100098546282903439321450697)
        ·
          refine ⟨75073909712177579491088023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100098546282903439321450697 75073909712177579491088023)
          ·
            refine ⟨112610864568266369236632035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75073909712177579491088023 112610864568266369236632035)
            ·
              refine ⟨168916296852399553854948053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112610864568266369236632035 168916296852399553854948053)
              ·
                refine ⟨3958975707478114543475345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 168916296852399553854948053 3958975707478114543475345)
                ·
                  refine ⟨2969231780608585907606509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3958975707478114543475345 2969231780608585907606509)
                  ·
                    refine ⟨1113461917728219715352441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2969231780608585907606509 1113461917728219715352441)
                    ·
                      rfl

theorem cell22_3252689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_3252689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252689 prefixEnd_3252689 := by exact prefixLift 3252689
  have htrace : WordTrace (prefixWord ++ tailWord_3252689) baseStart_3252689 baseEnd_3252689 := by
    simpa [prefixWord, tailWord_3252689, baseEnd_3252689] using wordTrace_append hprefix tailTrace_3252689
  have hstable : (prefixWord ++ tailWord_3252689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252689).length < 2 ^ (prefixWord ++ tailWord_3252689).sum := by decide
  have hdescent : baseEnd_3252689 < baseStart_3252689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252725 : List Nat := [1, 3, 5, 1, 2, 1, 3, 2, 4]
def baseStart_3252725 : Nat := 118140960795 + 3252725 * 2 ^ 59
def prefixEnd_3252725 : Nat := 4983230072969 + 3 ^ 40 * 3252725 * 2
def baseEnd_3252725 : Nat := 371158080421309207150777

theorem tailTrace_3252725 : CollatzResearch.WordTrace tailWord_3252725 prefixEnd_3252725 371158080421309207150777 := by
  unfold tailWord_3252725
  simp only [CollatzResearch.WordTrace]
  refine ⟨118636627140940321047807629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79091084760626880698538419 118636627140940321047807629)
  ·
    refine ⟨44488735177852620392927861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118636627140940321047807629 44488735177852620392927861)
    ·
      refine ⟨4170818922923683161836987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44488735177852620392927861 4170818922923683161836987)
      ·
        refine ⟨6256228384385524742755481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170818922923683161836987 6256228384385524742755481)
        ·
          refine ⟨4692171288289143557066611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6256228384385524742755481 4692171288289143557066611)
          ·
            refine ⟨7038256932433715335599917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4692171288289143557066611 7038256932433715335599917)
            ·
              refine ⟨2639346349662643250849969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7038256932433715335599917 2639346349662643250849969)
              ·
                refine ⟨1979509762246982438137477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2639346349662643250849969 1979509762246982438137477)
                ·
                  refine ⟨371158080421309207150777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1979509762246982438137477 371158080421309207150777)
                  ·
                    rfl

theorem cell22_3252725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_3252725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252725 prefixEnd_3252725 := by exact prefixLift 3252725
  have htrace : WordTrace (prefixWord ++ tailWord_3252725) baseStart_3252725 baseEnd_3252725 := by
    simpa [prefixWord, tailWord_3252725, baseEnd_3252725] using wordTrace_append hprefix tailTrace_3252725
  have hstable : (prefixWord ++ tailWord_3252725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252725).length < 2 ^ (prefixWord ++ tailWord_3252725).sum := by decide
  have hdescent : baseEnd_3252725 < baseStart_3252725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252732 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_3252732 : Nat := 118140960795 + 3252732 * 2 ^ 59
def prefixEnd_3252732 : Nat := 4983230072969 + 3 ^ 40 * 3252732 * 2
def baseEnd_3252732 : Nat := 1113476637506981936527309

theorem tailTrace_3252732 : CollatzResearch.WordTrace tailWord_3252732 prefixEnd_3252732 1113476637506981936527309 := by
  unfold tailWord_3252732
  simp only [CollatzResearch.WordTrace]
  refine ⟨59318441225957480621656225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79091254967943307495541633 59318441225957480621656225)
  ·
    refine ⟨44488830919468110466242169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59318441225957480621656225 44488830919468110466242169)
    ·
      refine ⟨33366623189601082849681627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44488830919468110466242169 33366623189601082849681627)
      ·
        refine ⟨50049934784401624274522441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33366623189601082849681627 50049934784401624274522441)
        ·
          refine ⟨37537451088301218205891831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50049934784401624274522441 37537451088301218205891831)
          ·
            refine ⟨56306176632451827308837747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37537451088301218205891831 56306176632451827308837747)
            ·
              refine ⟨84459264948677740963256621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56306176632451827308837747 84459264948677740963256621)
              ·
                refine ⟨31672224355754152861221233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84459264948677740963256621 31672224355754152861221233)
                ·
                  refine ⟨23754168266815614645915925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31672224355754152861221233 23754168266815614645915925)
                  ·
                    refine ⟨1113476637506981936527309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23754168266815614645915925 1113476637506981936527309)
                    ·
                      rfl

theorem cell22_3252732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_3252732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252732 prefixEnd_3252732 := by exact prefixLift 3252732
  have htrace : WordTrace (prefixWord ++ tailWord_3252732) baseStart_3252732 baseEnd_3252732 := by
    simpa [prefixWord, tailWord_3252732, baseEnd_3252732] using wordTrace_append hprefix tailTrace_3252732
  have hstable : (prefixWord ++ tailWord_3252732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252732).length < 2 ^ (prefixWord ++ tailWord_3252732).sum := by decide
  have hdescent : baseEnd_3252732 < baseStart_3252732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252740 : List Nat := [2, 3, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_3252740 : Nat := 118140960795 + 3252740 * 2 ^ 59
def prefixEnd_3252740 : Nat := 4983230072969 + 3 ^ 40 * 3252740 * 2
def baseEnd_3252740 : Nat := 1113479376070472582327285

theorem tailTrace_3252740 : CollatzResearch.WordTrace tailWord_3252740 prefixEnd_3252740 1113479376070472582327285 := by
  unfold tailWord_3252740
  simp only [CollatzResearch.WordTrace]
  refine ⟨59318587117942989304801837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79091449490590652406402449 59318587117942989304801837)
  ·
    refine ⟨22244470169228620989300689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59318587117942989304801837 22244470169228620989300689)
    ·
      refine ⟨16683352626921465741975517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22244470169228620989300689 16683352626921465741975517)
      ·
        refine ⟨6256257235095549653240819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16683352626921465741975517 6256257235095549653240819)
        ·
          refine ⟨9384385852643324479861229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6256257235095549653240819 9384385852643324479861229)
          ·
            refine ⟨3519144694741246679947961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9384385852643324479861229 3519144694741246679947961)
            ·
              refine ⟨2639358521055935009960971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3519144694741246679947961 2639358521055935009960971)
              ·
                refine ⟨3959037781583902514941457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639358521055935009960971 3959037781583902514941457)
                ·
                  refine ⟨2969278336187926886206093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3959037781583902514941457 2969278336187926886206093)
                  ·
                    refine ⟨1113479376070472582327285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2969278336187926886206093 1113479376070472582327285)
                    ·
                      rfl

theorem cell22_3252740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_3252740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252740 prefixEnd_3252740 := by exact prefixLift 3252740
  have htrace : WordTrace (prefixWord ++ tailWord_3252740) baseStart_3252740 baseEnd_3252740 := by
    simpa [prefixWord, tailWord_3252740, baseEnd_3252740] using wordTrace_append hprefix tailTrace_3252740
  have hstable : (prefixWord ++ tailWord_3252740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252740).length < 2 ^ (prefixWord ++ tailWord_3252740).sum := by decide
  have hdescent : baseEnd_3252740 < baseStart_3252740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252794 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_3252794 : Nat := 118140960795 + 3252794 * 2 ^ 59
def prefixEnd_3252794 : Nat := 4983230072969 + 3 ^ 40 * 3252794 * 2
def baseEnd_3252794 : Nat := 1113497861374034441477119

theorem tailTrace_3252794 : CollatzResearch.WordTrace tailWord_3252794 prefixEnd_3252794 1113497861374034441477119 := by
  unfold tailWord_3252794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29659785944422586458017359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79092762518460230554712957 29659785944422586458017359)
  ·
    refine ⟨44489678916633879687026039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29659785944422586458017359 44489678916633879687026039)
    ·
      refine ⟨66734518374950819530539059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44489678916633879687026039 66734518374950819530539059)
      ·
        refine ⟨100101777562426229295808589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66734518374950819530539059 100101777562426229295808589)
        ·
          refine ⟨37538166585909835985928221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100101777562426229295808589 37538166585909835985928221)
          ·
            refine ⟨14076812469716188494723083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37538166585909835985928221 14076812469716188494723083)
            ·
              refine ⟨21115218704574282742084625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14076812469716188494723083 21115218704574282742084625)
              ·
                refine ⟨15836414028430712056563469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21115218704574282742084625 15836414028430712056563469)
                ·
                  refine ⟨5938655260661517021211301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15836414028430712056563469 5938655260661517021211301)
                  ·
                    refine ⟨1113497861374034441477119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5938655260661517021211301 1113497861374034441477119)
                    ·
                      rfl

theorem cell22_3252794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_3252794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252794 prefixEnd_3252794 := by exact prefixLift 3252794
  have htrace : WordTrace (prefixWord ++ tailWord_3252794) baseStart_3252794 baseEnd_3252794 := by
    simpa [prefixWord, tailWord_3252794, baseEnd_3252794] using wordTrace_append hprefix tailTrace_3252794
  have hstable : (prefixWord ++ tailWord_3252794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252794).length < 2 ^ (prefixWord ++ tailWord_3252794).sum := by decide
  have hdescent : baseEnd_3252794 < baseStart_3252794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252824 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 1, 5]
def baseStart_3252824 : Nat := 118140960795 + 3252824 * 2 ^ 59
def prefixEnd_3252824 : Nat := 4983230072969 + 3 ^ 40 * 3252824 * 2
def baseEnd_3252824 : Nat := 1113508130987124363227027

theorem tailTrace_3252824 : CollatzResearch.WordTrace tailWord_3252824 prefixEnd_3252824 1113508130987124363227027 := by
  unfold tailWord_3252824
  simp only [CollatzResearch.WordTrace]
  refine ⟨59320118983790830477830763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79093491978387773970441017 59320118983790830477830763)
  ·
    refine ⟨88980178475686245716746145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59320118983790830477830763 88980178475686245716746145)
    ·
      refine ⟨66735133856764684287559609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88980178475686245716746145 66735133856764684287559609)
      ·
        refine ⟨50051350392573513215669707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66735133856764684287559609 50051350392573513215669707)
        ·
          refine ⟨75077025588860269823504561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50051350392573513215669707 75077025588860269823504561)
          ·
            refine ⟨56307769191645202367628421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75077025588860269823504561 56307769191645202367628421)
            ·
              refine ⟨10557706723433475443930329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56307769191645202367628421 10557706723433475443930329)
              ·
                refine ⟨7918280042575106582947747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10557706723433475443930329 7918280042575106582947747)
                ·
                  refine ⟨11877420063862659874421621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7918280042575106582947747 11877420063862659874421621)
                  ·
                    refine ⟨1113508130987124363227027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11877420063862659874421621 1113508130987124363227027)
                    ·
                      rfl

theorem cell22_3252824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_3252824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252824 prefixEnd_3252824 := by exact prefixLift 3252824
  have htrace : WordTrace (prefixWord ++ tailWord_3252824) baseStart_3252824 baseEnd_3252824 := by
    simpa [prefixWord, tailWord_3252824, baseEnd_3252824] using wordTrace_append hprefix tailTrace_3252824
  have hstable : (prefixWord ++ tailWord_3252824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252824).length < 2 ^ (prefixWord ++ tailWord_3252824).sum := by decide
  have hdescent : baseEnd_3252824 < baseStart_3252824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252828 : List Nat := [2, 2, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3252828 : Nat := 118140960795 + 3252828 * 2 ^ 59
def prefixEnd_3252828 : Nat := 4983230072969 + 3 ^ 40 * 3252828 * 2
def baseEnd_3252828 : Nat := 1113509500268869686127015

theorem tailTrace_3252828 : CollatzResearch.WordTrace tailWord_3252828 prefixEnd_3252828 1113509500268869686127015 := by
  unfold tailWord_3252828
  simp only [CollatzResearch.WordTrace]
  refine ⟨59320191929783584819403569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79093589239711446425871425 59320191929783584819403569)
  ·
    refine ⟨44490143947337688614552677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59320191929783584819403569 44490143947337688614552677)
    ·
      refine ⟨8341901990125816615228627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44490143947337688614552677 8341901990125816615228627)
      ·
        refine ⟨12512852985188724922842941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8341901990125816615228627 12512852985188724922842941)
        ·
          refine ⟨4692319869445771846066103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12512852985188724922842941 4692319869445771846066103)
          ·
            refine ⟨7038479804168657769099155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4692319869445771846066103 7038479804168657769099155)
            ·
              refine ⟨10557719706252986653648733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7038479804168657769099155 10557719706252986653648733)
              ·
                refine ⟨3959144889844869995118275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10557719706252986653648733 3959144889844869995118275)
                ·
                  refine ⟨5938717334767304992677413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959144889844869995118275 5938717334767304992677413)
                  ·
                    refine ⟨1113509500268869686127015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5938717334767304992677413 1113509500268869686127015)
                    ·
                      rfl

theorem cell22_3252828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3252828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252828 prefixEnd_3252828 := by exact prefixLift 3252828
  have htrace : WordTrace (prefixWord ++ tailWord_3252828) baseStart_3252828 baseEnd_3252828 := by
    simpa [prefixWord, tailWord_3252828, baseEnd_3252828] using wordTrace_append hprefix tailTrace_3252828
  have hstable : (prefixWord ++ tailWord_3252828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252828).length < 2 ^ (prefixWord ++ tailWord_3252828).sum := by decide
  have hdescent : baseEnd_3252828 < baseStart_3252828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252839 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 4, 4]
def baseStart_3252839 : Nat := 118140960795 + 3252839 * 2 ^ 59
def prefixEnd_3252839 : Nat := 4983230072969 + 3 ^ 40 * 3252839 * 2
def baseEnd_3252839 : Nat := 1113513265793669324101981

theorem tailTrace_3252839 : CollatzResearch.WordTrace tailWord_3252839 prefixEnd_3252839 1113513265793669324101981 := by
  unfold tailWord_3252839
  simp only [CollatzResearch.WordTrace]
  refine ⟨118640785062527318517457571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79093856708351545678305047 118640785062527318517457571)
  ·
    refine ⟨177961177593790977776186357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118640785062527318517457571 177961177593790977776186357)
    ·
      refine ⟨16683860399417904166517471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177961177593790977776186357 16683860399417904166517471)
      ·
        refine ⟨25025790599126856249776207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16683860399417904166517471 25025790599126856249776207)
        ·
          refine ⟨37538685898690284374664311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25025790599126856249776207 37538685898690284374664311)
          ·
            refine ⟨56308028848035426561996467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37538685898690284374664311 56308028848035426561996467)
            ·
              refine ⟨84462043272053139842994701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56308028848035426561996467 84462043272053139842994701)
              ·
                refine ⟨31673266227019927441123013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84462043272053139842994701 31673266227019927441123013)
                ·
                  refine ⟨5938737417566236395210565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31673266227019927441123013 5938737417566236395210565)
                  ·
                    refine ⟨1113513265793669324101981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5938737417566236395210565 1113513265793669324101981)
                    ·
                      rfl

theorem cell22_3252839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_3252839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252839 prefixEnd_3252839 := by exact prefixLift 3252839
  have htrace : WordTrace (prefixWord ++ tailWord_3252839) baseStart_3252839 baseEnd_3252839 := by
    simpa [prefixWord, tailWord_3252839, baseEnd_3252839] using wordTrace_append hprefix tailTrace_3252839
  have hstable : (prefixWord ++ tailWord_3252839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252839).length < 2 ^ (prefixWord ++ tailWord_3252839).sum := by decide
  have hdescent : baseEnd_3252839 < baseStart_3252839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252914 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_3252914 : Nat := 118140960795 + 3252914 * 2 ^ 59
def prefixEnd_3252914 : Nat := 4983230072969 + 3 ^ 40 * 3252914 * 2
def baseEnd_3252914 : Nat := 1113538939826394128476751

theorem tailTrace_3252914 : CollatzResearch.WordTrace tailWord_3252914 prefixEnd_3252914 1113538939826394128476751 := by
  unfold tailWord_3252914
  simp only [CollatzResearch.WordTrace]
  refine ⟨29660880134313901581609449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79095680358170404217625197 29660880134313901581609449)
  ·
    refine ⟨22245660100735426186207087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29660880134313901581609449 22245660100735426186207087)
    ·
      refine ⟨33368490151103139279310631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22245660100735426186207087 33368490151103139279310631)
      ·
        refine ⟨50052735226654708918965947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33368490151103139279310631 50052735226654708918965947)
        ·
          refine ⟨75079102839982063378448921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50052735226654708918965947 75079102839982063378448921)
          ·
            refine ⟨56309327129986547533836691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75079102839982063378448921 56309327129986547533836691)
            ·
              refine ⟨84463990694979821300755037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56309327129986547533836691 84463990694979821300755037)
              ·
                refine ⟨31673996510617432987783139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84463990694979821300755037 31673996510617432987783139)
                ·
                  refine ⟨47510994765926149481674709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31673996510617432987783139 47510994765926149481674709)
                  ·
                    refine ⟨1113538939826394128476751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47510994765926149481674709 1113538939826394128476751)
                    ·
                      rfl

theorem cell22_3252914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_3252914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252914 prefixEnd_3252914 := by exact prefixLift 3252914
  have htrace : WordTrace (prefixWord ++ tailWord_3252914) baseStart_3252914 baseEnd_3252914 := by
    simpa [prefixWord, tailWord_3252914, baseEnd_3252914] using wordTrace_append hprefix tailTrace_3252914
  have hstable : (prefixWord ++ tailWord_3252914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252914).length < 2 ^ (prefixWord ++ tailWord_3252914).sum := by decide
  have hdescent : baseEnd_3252914 < baseStart_3252914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252976 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 1, 5]
def baseStart_3252976 : Nat := 118140960795 + 3252976 * 2 ^ 59
def prefixEnd_3252976 : Nat := 4983230072969 + 3 ^ 40 * 3252976 * 2
def baseEnd_3252976 : Nat := 1113560163693446633426561

theorem tailTrace_3252976 : CollatzResearch.WordTrace tailWord_3252976 prefixEnd_3252976 1113560163693446633426561 := by
  unfold tailWord_3252976
  simp only [CollatzResearch.WordTrace]
  refine ⟨59322890931515495457597391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79097187908687327276796521 59322890931515495457597391)
  ·
    refine ⟨88984336397273243186396087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59322890931515495457597391 88984336397273243186396087)
    ·
      refine ⟨133476504595909864779594131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88984336397273243186396087 133476504595909864779594131)
      ·
        refine ⟨200214756893864797169391197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133476504595909864779594131 200214756893864797169391197)
        ·
          refine ⟨75080533835199298938521699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200214756893864797169391197 75080533835199298938521699)
          ·
            refine ⟨112620800752798948407782549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75080533835199298938521699 112620800752798948407782549)
            ·
              refine ⟨5279100035287450706614807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112620800752798948407782549 5279100035287450706614807)
              ·
                refine ⟨7918650052931176059922211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5279100035287450706614807 7918650052931176059922211)
                ·
                  refine ⟨11877975079396764089883317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7918650052931176059922211 11877975079396764089883317)
                  ·
                    refine ⟨1113560163693446633426561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11877975079396764089883317 1113560163693446633426561)
                    ·
                      rfl

theorem cell22_3252976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_3252976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3252976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3252976 prefixEnd_3252976 := by exact prefixLift 3252976
  have htrace : WordTrace (prefixWord ++ tailWord_3252976) baseStart_3252976 baseEnd_3252976 := by
    simpa [prefixWord, tailWord_3252976, baseEnd_3252976] using wordTrace_append hprefix tailTrace_3252976
  have hstable : (prefixWord ++ tailWord_3252976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252976).length < 2 ^ (prefixWord ++ tailWord_3252976).sum := by decide
  have hdescent : baseEnd_3252976 < baseStart_3252976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253066 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_3253066 : Nat := 118140960795 + 3253066 * 2 ^ 59
def prefixEnd_3253066 : Nat := 4983230072969 + 3 ^ 40 * 3253066 * 2
def baseEnd_3253066 : Nat := 1113590972532716398676285

theorem tailTrace_3253066 : CollatzResearch.WordTrace tailWord_3253066 prefixEnd_3253066 1113590972532716398676285 := by
  unfold tailWord_3253066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29662266108176234071492763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79099376288469957523980701 29662266108176234071492763)
  ·
    refine ⟨44493399162264351107239145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29662266108176234071492763 44493399162264351107239145)
    ·
      refine ⟨33370049371698263330429359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44493399162264351107239145 33370049371698263330429359)
      ·
        refine ⟨50055074057547394995644039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33370049371698263330429359 50055074057547394995644039)
        ·
          refine ⟨75082611086321092493466059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50055074057547394995644039 75082611086321092493466059)
          ·
            refine ⟨112623916629481638740199089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75082611086321092493466059 112623916629481638740199089)
            ·
              refine ⟨84467937472111229055149317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112623916629481638740199089 84467937472111229055149317)
              ·
                refine ⟨15837738276020855447840497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84467937472111229055149317 15837738276020855447840497)
                ·
                  refine ⟨11878303707015641585880373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15837738276020855447840497 11878303707015641585880373)
                  ·
                    refine ⟨1113590972532716398676285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11878303707015641585880373 1113590972532716398676285)
                    ·
                      rfl

theorem cell22_3253066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_3253066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253066 prefixEnd_3253066 := by exact prefixLift 3253066
  have htrace : WordTrace (prefixWord ++ tailWord_3253066) baseStart_3253066 baseEnd_3253066 := by
    simpa [prefixWord, tailWord_3253066, baseEnd_3253066] using wordTrace_append hprefix tailTrace_3253066
  have hstable : (prefixWord ++ tailWord_3253066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253066).length < 2 ^ (prefixWord ++ tailWord_3253066).sum := by decide
  have hdescent : baseEnd_3253066 < baseStart_3253066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253171 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 1, 8]
def baseStart_3253171 : Nat := 118140960795 + 3253171 * 2 ^ 59
def prefixEnd_3253171 : Nat := 4983230072969 + 3 ^ 40 * 3253171 * 2
def baseEnd_3253171 : Nat := 1113626916178531124800963

theorem tailTrace_3253171 : CollatzResearch.WordTrace tailWord_3253171 prefixEnd_3253171 1113626916178531124800963 := by
  unfold tailWord_3253171
  simp only [CollatzResearch.WordTrace]
  refine ⟨118652894097324539218543367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79101929398216359479028911 118652894097324539218543367)
  ·
    refine ⟨177979341145986808827815051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118652894097324539218543367 177979341145986808827815051)
    ·
      refine ⟨266969011718980213241722577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177979341145986808827815051 266969011718980213241722577)
      ·
        refine ⟨200226758789235159931291933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266969011718980213241722577 200226758789235159931291933)
        ·
          refine ⟨75085034545963184974234475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200226758789235159931291933 75085034545963184974234475)
          ·
            refine ⟨112627551818944777461351713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75085034545963184974234475 112627551818944777461351713)
            ·
              refine ⟨84470663864208583096013785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112627551818944777461351713 84470663864208583096013785)
              ·
                refine ⟨63352997898156437322010339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84470663864208583096013785 63352997898156437322010339)
                ·
                  refine ⟨95029496847234655983015509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63352997898156437322010339 95029496847234655983015509)
                  ·
                    refine ⟨1113626916178531124800963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95029496847234655983015509 1113626916178531124800963)
                    ·
                      rfl

theorem cell22_3253171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_3253171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253171 prefixEnd_3253171 := by exact prefixLift 3253171
  have htrace : WordTrace (prefixWord ++ tailWord_3253171) baseStart_3253171 baseEnd_3253171 := by
    simpa [prefixWord, tailWord_3253171, baseEnd_3253171] using wordTrace_append hprefix tailTrace_3253171
  have hstable : (prefixWord ++ tailWord_3253171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253171).length < 2 ^ (prefixWord ++ tailWord_3253171).sum := by decide
  have hdescent : baseEnd_3253171 < baseStart_3253171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253284 : List Nat := [2, 3, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_3253284 : Nat := 118140960795 + 3253284 * 2 ^ 59
def prefixEnd_3253284 : Nat := 4983230072969 + 3 ^ 40 * 3253284 * 2
def baseEnd_3253284 : Nat := 1113665598387836496725617

theorem tailTrace_3253284 : CollatzResearch.WordTrace tailWord_3253284 prefixEnd_3253284 1113665598387836496725617 := by
  unfold tailWord_3253284
  simp only [CollatzResearch.WordTrace]
  refine ⟨59328507772957579758703453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79104677030610106344937937 59328507772957579758703453)
  ·
    refine ⟨22248190414859092409513795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59328507772957579758703453 22248190414859092409513795)
    ·
      refine ⟨33372285622288638614270693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22248190414859092409513795 33372285622288638614270693)
      ·
        refine ⟨6257303554179119740175755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33372285622288638614270693 6257303554179119740175755)
        ·
          refine ⟨9385955331268679610263633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6257303554179119740175755 9385955331268679610263633)
          ·
            refine ⟨7039466498451509707697725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9385955331268679610263633 7039466498451509707697725)
            ·
              refine ⟨2639799936919316140386647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7039466498451509707697725 2639799936919316140386647)
              ·
                refine ⟨3959699905378974210579971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639799936919316140386647 3959699905378974210579971)
                ·
                  refine ⟨5939549858068461315869957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959699905378974210579971 5939549858068461315869957)
                  ·
                    refine ⟨1113665598387836496725617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5939549858068461315869957 1113665598387836496725617)
                    ·
                      rfl

theorem cell22_3253284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_3253284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253284 prefixEnd_3253284 := by exact prefixLift 3253284
  have htrace : WordTrace (prefixWord ++ tailWord_3253284) baseStart_3253284 baseEnd_3253284 := by
    simpa [prefixWord, tailWord_3253284, baseEnd_3253284] using wordTrace_append hprefix tailTrace_3253284
  have hstable : (prefixWord ++ tailWord_3253284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253284).length < 2 ^ (prefixWord ++ tailWord_3253284).sum := by decide
  have hdescent : baseEnd_3253284 < baseStart_3253284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253297 : List Nat := [1, 2, 2, 3, 1, 2, 4, 2, 2, 3]
def baseStart_3253297 : Nat := 118140960795 + 3253297 * 2 ^ 59
def prefixEnd_3253297 : Nat := 4983230072969 + 3 ^ 40 * 3253297 * 2
def baseEnd_3253297 : Nat := 1113670048553508796150577

theorem tailTrace_3253297 : CollatzResearch.WordTrace tailWord_3253297 prefixEnd_3253297 1113670048553508796150577 := by
  unfold tailWord_3253297
  simp only [CollatzResearch.WordTrace]
  refine ⟨118657489694868062737630145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79104993129912041825086763 118657489694868062737630145)
  ·
    refine ⟨88993117271151047053222609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118657489694868062737630145 88993117271151047053222609)
    ·
      refine ⟨66744837953363285289916957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88993117271151047053222609 66744837953363285289916957)
      ·
        refine ⟨25029314232511231983718859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66744837953363285289916957 25029314232511231983718859)
        ·
          refine ⟨37543971348766847975578289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25029314232511231983718859 37543971348766847975578289)
          ·
            refine ⟨28157978511575135981683717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37543971348766847975578289 28157978511575135981683717)
            ·
              refine ⟨5279620970920337996565697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28157978511575135981683717 5279620970920337996565697)
              ·
                refine ⟨3959715728190253497424273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5279620970920337996565697 3959715728190253497424273)
                ·
                  refine ⟨2969786796142690123068205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3959715728190253497424273 2969786796142690123068205)
                  ·
                    refine ⟨1113670048553508796150577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2969786796142690123068205 1113670048553508796150577)
                    ·
                      rfl

theorem cell22_3253297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_3253297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253297 prefixEnd_3253297 := by exact prefixLift 3253297
  have htrace : WordTrace (prefixWord ++ tailWord_3253297) baseStart_3253297 baseEnd_3253297 := by
    simpa [prefixWord, tailWord_3253297, baseEnd_3253297] using wordTrace_append hprefix tailTrace_3253297
  have hstable : (prefixWord ++ tailWord_3253297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253297).length < 2 ^ (prefixWord ++ tailWord_3253297).sum := by decide
  have hdescent : baseEnd_3253297 < baseStart_3253297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253372 : List Nat := [2, 2, 2, 1, 1, 3, 5, 1, 5]
def baseStart_3253372 : Nat := 118140960795 + 3253372 * 2 ^ 59
def prefixEnd_3253372 : Nat := 4983230072969 + 3 ^ 40 * 3253372 * 2
def baseEnd_3253372 : Nat := 371231907528744533508449

theorem tailTrace_3253372 : CollatzResearch.WordTrace tailWord_3253372 prefixEnd_3253372 371231907528744533508449 := by
  unfold tailWord_3253372
  simp only [CollatzResearch.WordTrace]
  refine ⟨59330112584798175273305185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79106816779730900364406913 59330112584798175273305185)
  ·
    refine ⟨44497584438598631454978889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59330112584798175273305185 44497584438598631454978889)
    ·
      refine ⟨33373188328948973591234167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44497584438598631454978889 33373188328948973591234167)
      ·
        refine ⟨50059782493423460386851251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33373188328948973591234167 50059782493423460386851251)
        ·
          refine ⟨75089673740135190580276877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50059782493423460386851251 75089673740135190580276877)
          ·
            refine ⟨28158627652550696467603829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75089673740135190580276877 28158627652550696467603829)
            ·
              refine ⟨2639871342426627793837859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28158627652550696467603829 2639871342426627793837859)
              ·
                refine ⟨3959807013639941690756789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639871342426627793837859 3959807013639941690756789)
                ·
                  refine ⟨371231907528744533508449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3959807013639941690756789 371231907528744533508449)
                  ·
                    rfl

theorem cell22_3253372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_3253372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253372 prefixEnd_3253372 := by exact prefixLift 3253372
  have htrace : WordTrace (prefixWord ++ tailWord_3253372) baseStart_3253372 baseEnd_3253372 := by
    simpa [prefixWord, tailWord_3253372, baseEnd_3253372] using wordTrace_append hprefix tailTrace_3253372
  have hstable : (prefixWord ++ tailWord_3253372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253372).length < 2 ^ (prefixWord ++ tailWord_3253372).sum := by decide
  have hdescent : baseEnd_3253372 < baseStart_3253372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253462 : List Nat := [5, 2, 1, 2, 12]
def baseStart_3253462 : Nat := 118140960795 + 3253462 * 2 ^ 59
def prefixEnd_3253462 : Nat := 4983230072969 + 3 ^ 40 * 3253462 * 2
def baseEnd_3253462 : Nat := 4583236754837462410597

theorem tailTrace_3253462 : CollatzResearch.WordTrace tailWord_3253462 prefixEnd_3253462 4583236754837462410597 := by
  unfold tailWord_3253462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7416469233704393494836665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79109005159513530611591093 7416469233704393494836665)
  ·
    refine ⟨5562351925278295121127499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7416469233704393494836665 5562351925278295121127499)
    ·
      refine ⟨8343527887917442681691249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5562351925278295121127499 8343527887917442681691249)
      ·
        refine ⟨6257645915938082011268437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8343527887917442681691249 6257645915938082011268437)
        ·
          refine ⟨4583236754837462410597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6257645915938082011268437 4583236754837462410597)
          ·
            rfl

theorem cell22_3253462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 12].length) (baseStart_3253462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253462 prefixEnd_3253462 := by exact prefixLift 3253462
  have htrace : WordTrace (prefixWord ++ tailWord_3253462) baseStart_3253462 baseEnd_3253462 := by
    simpa [prefixWord, tailWord_3253462, baseEnd_3253462] using wordTrace_append hprefix tailTrace_3253462
  have hstable : (prefixWord ++ tailWord_3253462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253462).length < 2 ^ (prefixWord ++ tailWord_3253462).sum := by decide
  have hdescent : baseEnd_3253462 < baseStart_3253462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253479 : List Nat := [1, 1, 5, 3, 2, 2, 1, 7]
def baseStart_3253479 : Nat := 118140960795 + 3253479 * 2 ^ 59
def prefixEnd_3253479 : Nat := 4983230072969 + 3 ^ 40 * 3253479 * 2
def baseEnd_3253479 : Nat := 123748038985880109788891

theorem tailTrace_3253479 : CollatzResearch.WordTrace tailWord_3253479 prefixEnd_3253479 123748038985880109788891 := by
  unfold tailWord_3253479
  simp only [CollatzResearch.WordTrace]
  refine ⟨118664127780208707820755491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79109418520139138547170327 118664127780208707820755491)
  ·
    refine ⟨177996191670313061731133237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118664127780208707820755491 177996191670313061731133237)
    ·
      refine ⟨16687142969091849537293741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177996191670313061731133237 16687142969091849537293741)
      ·
        refine ⟨6257678613409443576485153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16687142969091849537293741 6257678613409443576485153)
        ·
          refine ⟨4693258960057082682363865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6257678613409443576485153 4693258960057082682363865)
          ·
            refine ⟨3519944220042812011772899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4693258960057082682363865 3519944220042812011772899)
            ·
              refine ⟨5279916330064218017659349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519944220042812011772899 5279916330064218017659349)
              ·
                refine ⟨123748038985880109788891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5279916330064218017659349 123748038985880109788891)
                ·
                  rfl

theorem cell22_3253479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 7].length) (baseStart_3253479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253479 prefixEnd_3253479 := by exact prefixLift 3253479
  have htrace : WordTrace (prefixWord ++ tailWord_3253479) baseStart_3253479 baseEnd_3253479 := by
    simpa [prefixWord, tailWord_3253479, baseEnd_3253479] using wordTrace_append hprefix tailTrace_3253479
  have hstable : (prefixWord ++ tailWord_3253479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253479).length < 2 ^ (prefixWord ++ tailWord_3253479).sum := by decide
  have hdescent : baseEnd_3253479 < baseStart_3253479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253554 : List Nat := [3, 2, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_3253554 : Nat := 118140960795 + 3253554 * 2 ^ 59
def prefixEnd_3253554 : Nat := 4983230072969 + 3 ^ 40 * 3253554 * 2
def baseEnd_3253554 : Nat := 1113758024905645792474789

theorem tailTrace_3253554 : CollatzResearch.WordTrace tailWord_3253554 prefixEnd_3253554 1113758024905645792474789 := by
  unfold tailWord_3253554
  simp only [CollatzResearch.WordTrace]
  refine ⟨29666715813734248907433929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79111242169957997086490477 29666715813734248907433929)
  ·
    refine ⟨22250036860300686680575447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29666715813734248907433929 22250036860300686680575447)
    ·
      refine ⟨33375055290451030020863171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22250036860300686680575447 33375055290451030020863171)
      ·
        refine ⟨50062582935676545031294757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33375055290451030020863171 50062582935676545031294757)
        ·
          refine ⟨9386734300439352193367767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50062582935676545031294757 9386734300439352193367767)
          ·
            refine ⟨14080101450659028290051651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9386734300439352193367767 14080101450659028290051651)
            ·
              refine ⟨21120152175988542435077477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14080101450659028290051651 21120152175988542435077477)
              ·
                refine ⟨3960028532997851706577027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21120152175988542435077477 3960028532997851706577027)
                ·
                  refine ⟨5940042799496777559865541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3960028532997851706577027 5940042799496777559865541)
                  ·
                    refine ⟨1113758024905645792474789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5940042799496777559865541 1113758024905645792474789)
                    ·
                      rfl

theorem cell22_3253554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_3253554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253554 prefixEnd_3253554 := by exact prefixLift 3253554
  have htrace : WordTrace (prefixWord ++ tailWord_3253554) baseStart_3253554 baseEnd_3253554 := by
    simpa [prefixWord, tailWord_3253554, baseEnd_3253554] using wordTrace_append hprefix tailTrace_3253554
  have hstable : (prefixWord ++ tailWord_3253554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253554).length < 2 ^ (prefixWord ++ tailWord_3253554).sum := by decide
  have hdescent : baseEnd_3253554 < baseStart_3253554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253584 : List Nat := [2, 1, 1, 1, 1, 5, 2, 4, 2, 3]
def baseStart_3253584 : Nat := 118140960795 + 3253584 * 2 ^ 59
def prefixEnd_3253584 : Nat := 4983230072969 + 3 ^ 40 * 3253584 * 2
def baseEnd_3253584 : Nat := 1113768294518735714224697

theorem tailTrace_3253584 : CollatzResearch.WordTrace tailWord_3253584 prefixEnd_3253584 1113768294518735714224697 := by
  unfold tailWord_3253584
  simp only [CollatzResearch.WordTrace]
  refine ⟨59333978722414155376663903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79111971629885540502218537 59333978722414155376663903)
  ·
    refine ⟨89000968083621233064995855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59333978722414155376663903 89000968083621233064995855)
    ·
      refine ⟨133501452125431849597493783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89000968083621233064995855 133501452125431849597493783)
      ·
        refine ⟨200252178188147774396240675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133501452125431849597493783 200252178188147774396240675)
        ·
          refine ⟨300378267282221661594361013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200252178188147774396240675 300378267282221661594361013)
          ·
            refine ⟨28160462557708280774471345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 300378267282221661594361013 28160462557708280774471345)
            ·
              refine ⟨21120346918281210580853509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28160462557708280774471345 21120346918281210580853509)
              ·
                refine ⟨3960065047177726983910033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21120346918281210580853509 3960065047177726983910033)
                ·
                  refine ⟨2970048785383295237932525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3960065047177726983910033 2970048785383295237932525)
                  ·
                    refine ⟨1113768294518735714224697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2970048785383295237932525 1113768294518735714224697)
                    ·
                      rfl

theorem cell22_3253584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 2, 3].length) (baseStart_3253584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253584 prefixEnd_3253584 := by exact prefixLift 3253584
  have htrace : WordTrace (prefixWord ++ tailWord_3253584) baseStart_3253584 baseEnd_3253584 := by
    simpa [prefixWord, tailWord_3253584, baseEnd_3253584] using wordTrace_append hprefix tailTrace_3253584
  have hstable : (prefixWord ++ tailWord_3253584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253584).length < 2 ^ (prefixWord ++ tailWord_3253584).sum := by decide
  have hdescent : baseEnd_3253584 < baseStart_3253584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253657 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 1, 7]
def baseStart_3253657 : Nat := 118140960795 + 3253657 * 2 ^ 59
def prefixEnd_3253657 : Nat := 4983230072969 + 3 ^ 40 * 3253657 * 2
def baseEnd_3253657 : Nat := 1113793283910587857149473

theorem tailTrace_3253657 : CollatzResearch.WordTrace tailWord_3253657 prefixEnd_3253657 1113793283910587857149473 := by
  unfold tailWord_3253657
  simp only [CollatzResearch.WordTrace]
  refine ⟨118670619973563844220735225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79113746649042562813823483 118670619973563844220735225)
  ·
    refine ⟨89002964980172883165551419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118670619973563844220735225 89002964980172883165551419)
    ·
      refine ⟨133504447470259324748327129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89002964980172883165551419 133504447470259324748327129)
      ·
        refine ⟨100128335602694493561245347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133504447470259324748327129 100128335602694493561245347)
        ·
          refine ⟨150192503404041740341868021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100128335602694493561245347 150192503404041740341868021)
          ·
            refine ⟨14080547194128913157050127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150192503404041740341868021 14080547194128913157050127)
            ·
              refine ⟨21120820791193369735575191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14080547194128913157050127 21120820791193369735575191)
              ·
                refine ⟨31681231186790054603362787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21120820791193369735575191 31681231186790054603362787)
                ·
                  refine ⟨47521846780185081905044181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31681231186790054603362787 47521846780185081905044181)
                  ·
                    refine ⟨1113793283910587857149473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47521846780185081905044181 1113793283910587857149473)
                    ·
                      rfl

theorem cell22_3253657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_3253657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253657 prefixEnd_3253657 := by exact prefixLift 3253657
  have htrace : WordTrace (prefixWord ++ tailWord_3253657) baseStart_3253657 baseEnd_3253657 := by
    simpa [prefixWord, tailWord_3253657, baseEnd_3253657] using wordTrace_append hprefix tailTrace_3253657
  have hstable : (prefixWord ++ tailWord_3253657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253657).length < 2 ^ (prefixWord ++ tailWord_3253657).sum := by decide
  have hdescent : baseEnd_3253657 < baseStart_3253657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253687 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 8]
def baseStart_3253687 : Nat := 118140960795 + 3253687 * 2 ^ 59
def prefixEnd_3253687 : Nat := 4983230072969 + 3 ^ 40 * 3253687 * 2
def baseEnd_3253687 : Nat := 371267851174559259633127

theorem tailTrace_3253687 : CollatzResearch.WordTrace tailWord_3253687 prefixEnd_3253687 371267851174559259633127 := by
  unfold tailWord_3253687
  simp only [CollatzResearch.WordTrace]
  refine ⟨118671714163455159344327315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79114476108970106229551543 118671714163455159344327315)
  ·
    refine ⟨178007571245182739016490973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118671714163455159344327315 178007571245182739016490973)
    ·
      refine ⟨66752839216943527131184115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178007571245182739016490973 66752839216943527131184115)
      ·
        refine ⟨100129258825415290696776173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66752839216943527131184115 100129258825415290696776173)
        ·
          refine ⟨37548472059530734011291065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100129258825415290696776173 37548472059530734011291065)
          ·
            refine ⟨28161354044648050508468299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37548472059530734011291065 28161354044648050508468299)
            ·
              refine ⟨42242031066972075762702449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28161354044648050508468299 42242031066972075762702449)
              ·
                refine ⟨31681523300229056822026837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42242031066972075762702449 31681523300229056822026837)
                ·
                  refine ⟨371267851174559259633127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31681523300229056822026837 371267851174559259633127)
                  ·
                    rfl

theorem cell22_3253687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 8].length) (baseStart_3253687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253687 prefixEnd_3253687 := by exact prefixLift 3253687
  have htrace : WordTrace (prefixWord ++ tailWord_3253687) baseStart_3253687 baseEnd_3253687 := by
    simpa [prefixWord, tailWord_3253687, baseEnd_3253687] using wordTrace_append hprefix tailTrace_3253687
  have hstable : (prefixWord ++ tailWord_3253687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253687).length < 2 ^ (prefixWord ++ tailWord_3253687).sum := by decide
  have hdescent : baseEnd_3253687 < baseStart_3253687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253704 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 6]
def baseStart_3253704 : Nat := 118140960795 + 3253704 * 2 ^ 59
def prefixEnd_3253704 : Nat := 4983230072969 + 3 ^ 40 * 3253704 * 2
def baseEnd_3253704 : Nat := 371269790990365133741443

theorem tailTrace_3253704 : CollatzResearch.WordTrace tailWord_3253704 prefixEnd_3253704 371269790990365133741443 := by
  unfold tailWord_3253704
  simp only [CollatzResearch.WordTrace]
  refine ⟨59336167102196785623848083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79114889469595714165130777 59336167102196785623848083)
  ·
    refine ⟨89004250653295178435772125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59336167102196785623848083 89004250653295178435772125)
    ·
      refine ⟨33376593994985691913414547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89004250653295178435772125 33376593994985691913414547)
      ·
        refine ⟨50064890992478537870121821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33376593994985691913414547 50064890992478537870121821)
        ·
          refine ⟨18774334122179451701295683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50064890992478537870121821 18774334122179451701295683)
          ·
            refine ⟨28161501183269177551943525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18774334122179451701295683 28161501183269177551943525)
            ·
              refine ⟨5280281471862970790989411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28161501183269177551943525 5280281471862970790989411)
              ·
                refine ⟨7920422207794456186484117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5280281471862970790989411 7920422207794456186484117)
                ·
                  refine ⟨371269790990365133741443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7920422207794456186484117 371269790990365133741443)
                  ·
                    rfl

theorem cell22_3253704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_3253704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253704 prefixEnd_3253704 := by exact prefixLift 3253704
  have htrace : WordTrace (prefixWord ++ tailWord_3253704) baseStart_3253704 baseEnd_3253704 := by
    simpa [prefixWord, tailWord_3253704, baseEnd_3253704] using wordTrace_append hprefix tailTrace_3253704
  have hstable : (prefixWord ++ tailWord_3253704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253704).length < 2 ^ (prefixWord ++ tailWord_3253704).sum := by decide
  have hdescent : baseEnd_3253704 < baseStart_3253704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253770 : List Nat := [3, 1, 2, 2, 2, 4, 2, 1, 2, 3]
def baseStart_3253770 : Nat := 118140960795 + 3253770 * 2 ^ 59
def prefixEnd_3253770 : Nat := 4983230072969 + 3 ^ 40 * 3253770 * 2
def baseEnd_3253770 : Nat := 1113831966119893229074127

theorem tailTrace_3253770 : CollatzResearch.WordTrace tailWord_3253770 prefixEnd_3253770 1113831966119893229074127 := by
  unfold tailWord_3253770
  simp only [CollatzResearch.WordTrace]
  refine ⟨29668685355538616129899691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79116494281436309679732509 29668685355538616129899691)
  ·
    refine ⟨44503028033307924194849537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29668685355538616129899691 44503028033307924194849537)
    ·
      refine ⟨33377271024980943146137153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44503028033307924194849537 33377271024980943146137153)
      ·
        refine ⟨25032953268735707359602865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33377271024980943146137153 25032953268735707359602865)
        ·
          refine ⟨18774714951551780519702149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25032953268735707359602865 18774714951551780519702149)
          ·
            refine ⟨3520259053415958847444153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18774714951551780519702149 3520259053415958847444153)
            ·
              refine ⟨2640194290061969135583115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3520259053415958847444153 2640194290061969135583115)
              ·
                refine ⟨3960291435092953703374673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2640194290061969135583115 3960291435092953703374673)
                ·
                  refine ⟨2970218576319715277531005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3960291435092953703374673 2970218576319715277531005)
                  ·
                    refine ⟨1113831966119893229074127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2970218576319715277531005 1113831966119893229074127)
                    ·
                      rfl

theorem cell22_3253770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_3253770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253770 prefixEnd_3253770 := by exact prefixLift 3253770
  have htrace : WordTrace (prefixWord ++ tailWord_3253770) baseStart_3253770 baseEnd_3253770 := by
    simpa [prefixWord, tailWord_3253770, baseEnd_3253770] using wordTrace_append hprefix tailTrace_3253770
  have hstable : (prefixWord ++ tailWord_3253770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253770).length < 2 ^ (prefixWord ++ tailWord_3253770).sum := by decide
  have hdescent : baseEnd_3253770 < baseStart_3253770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253794 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 9]
def baseStart_3253794 : Nat := 118140960795 + 3253794 * 2 ^ 59
def prefixEnd_3253794 : Nat := 4983230072969 + 3 ^ 40 * 3253794 * 2
def baseEnd_3253794 : Nat := 371280060603455055491351

theorem tailTrace_3253794 : CollatzResearch.WordTrace tailWord_3253794 prefixEnd_3253794 371280060603455055491351 := by
  unfold tailWord_3253794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29668904193516879154618109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79117077849378344412314957 29668904193516879154618109)
  ·
    refine ⟨11125839072568829682981791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29668904193516879154618109 11125839072568829682981791)
    ·
      refine ⟨16688758608853244524472687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11125839072568829682981791 16688758608853244524472687)
      ·
        refine ⟨25033137913279866786709031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16688758608853244524472687 25033137913279866786709031)
        ·
          refine ⟨37549706869919800180063547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25033137913279866786709031 37549706869919800180063547)
          ·
            refine ⟨56324560304879700270095321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37549706869919800180063547 56324560304879700270095321)
            ·
              refine ⟨42243420228659775202571491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56324560304879700270095321 42243420228659775202571491)
              ·
                refine ⟨63365130342989662803857237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42243420228659775202571491 63365130342989662803857237)
                ·
                  refine ⟨371280060603455055491351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63365130342989662803857237 371280060603455055491351)
                  ·
                    rfl

theorem cell22_3253794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_3253794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253794 prefixEnd_3253794 := by exact prefixLift 3253794
  have htrace : WordTrace (prefixWord ++ tailWord_3253794) baseStart_3253794 baseEnd_3253794 := by
    simpa [prefixWord, tailWord_3253794, baseEnd_3253794] using wordTrace_append hprefix tailTrace_3253794
  have hstable : (prefixWord ++ tailWord_3253794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253794).length < 2 ^ (prefixWord ++ tailWord_3253794).sum := by decide
  have hdescent : baseEnd_3253794 < baseStart_3253794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253809 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 2, 5]
def baseStart_3253809 : Nat := 118140960795 + 3253809 * 2 ^ 59
def prefixEnd_3253809 : Nat := 4983230072969 + 3 ^ 40 * 3253809 * 2
def baseEnd_3253809 : Nat := 1113845316616910127349007

theorem tailTrace_3253809 : CollatzResearch.WordTrace tailWord_3253809 prefixEnd_3253809 1113845316616910127349007 := by
  unfold tailWord_3253809
  simp only [CollatzResearch.WordTrace]
  refine ⟨118676163869013174180268481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79117442579342116120178987 118676163869013174180268481)
  ·
    refine ⟨89007122901759880635201361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118676163869013174180268481 89007122901759880635201361)
    ·
      refine ⟨66755342176319910476401021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89007122901759880635201361 66755342176319910476401021)
      ·
        refine ⟨25033253316119966428650383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66755342176319910476401021 25033253316119966428650383)
        ·
          refine ⟨37549879974179949642975575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25033253316119966428650383 37549879974179949642975575)
          ·
            refine ⟨56324819961269924464463363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37549879974179949642975575 56324819961269924464463363)
            ·
              refine ⟨84487229941904886696695045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56324819961269924464463363 84487229941904886696695045)
              ·
                refine ⟨15841355614107166255630321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84487229941904886696695045 15841355614107166255630321)
                ·
                  refine ⟨11881016710580374691722741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15841355614107166255630321 11881016710580374691722741)
                  ·
                    refine ⟨1113845316616910127349007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11881016710580374691722741 1113845316616910127349007)
                    ·
                      rfl

theorem cell22_3253809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_3253809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253809 prefixEnd_3253809 := by exact prefixLift 3253809
  have htrace : WordTrace (prefixWord ++ tailWord_3253809) baseStart_3253809 baseEnd_3253809 := by
    simpa [prefixWord, tailWord_3253809, baseEnd_3253809] using wordTrace_append hprefix tailTrace_3253809
  have hstable : (prefixWord ++ tailWord_3253809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253809).length < 2 ^ (prefixWord ++ tailWord_3253809).sum := by decide
  have hdescent : baseEnd_3253809 < baseStart_3253809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253811 : List Nat := [1, 1, 1, 2, 4, 4, 2, 2, 5]
def baseStart_3253811 : Nat := 118140960795 + 3253811 * 2 ^ 59
def prefixEnd_3253811 : Nat := 4983230072969 + 3 ^ 40 * 3253811 * 2
def baseEnd_3253811 : Nat := 371282000419260929599667

theorem tailTrace_3253811 : CollatzResearch.WordTrace tailWord_3253811 prefixEnd_3253811 371282000419260929599667 := by
  unfold tailWord_3253811
  simp only [CollatzResearch.WordTrace]
  refine ⟨118676236815005928521841287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79117491210003952347894191 118676236815005928521841287)
  ·
    refine ⟨178014355222508892782761931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118676236815005928521841287 178014355222508892782761931)
    ·
      refine ⟨267021532833763339174142897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178014355222508892782761931 267021532833763339174142897)
      ·
        refine ⟨200266149625322504380607173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267021532833763339174142897 200266149625322504380607173)
        ·
          refine ⟨37549903054747969571363845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200266149625322504380607173 37549903054747969571363845)
          ·
            refine ⟨7040606822765244294630721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37549903054747969571363845 7040606822765244294630721)
            ·
              refine ⟨5280455117073933220973041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7040606822765244294630721 5280455117073933220973041)
              ·
                refine ⟨3960341337805449915729781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5280455117073933220973041 3960341337805449915729781)
                ·
                  refine ⟨371282000419260929599667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3960341337805449915729781 371282000419260929599667)
                  ·
                    rfl

theorem cell22_3253811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 5].length) (baseStart_3253811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253811 prefixEnd_3253811 := by exact prefixLift 3253811
  have htrace : WordTrace (prefixWord ++ tailWord_3253811) baseStart_3253811 baseEnd_3253811 := by
    simpa [prefixWord, tailWord_3253811, baseEnd_3253811] using wordTrace_append hprefix tailTrace_3253811
  have hstable : (prefixWord ++ tailWord_3253811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253811).length < 2 ^ (prefixWord ++ tailWord_3253811).sum := by decide
  have hdescent : baseEnd_3253811 < baseStart_3253811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253815 : List Nat := [1, 1, 3, 1, 2, 4, 4, 2, 1, 3]
def baseStart_3253815 : Nat := 118140960795 + 3253815 * 2 ^ 59
def prefixEnd_3253815 : Nat := 4983230072969 + 3 ^ 40 * 3253815 * 2
def baseEnd_3253815 : Nat := 1113847370539528111698989

theorem tailTrace_3253815 : CollatzResearch.WordTrace tailWord_3253815 prefixEnd_3253815 1113847370539528111698989 := by
  unfold tailWord_3253815
  simp only [CollatzResearch.WordTrace]
  refine ⟨118676382706991437204986899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79117588471327624803324599 118676382706991437204986899)
  ·
    refine ⟨178014574060487155807480349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118676382706991437204986899 178014574060487155807480349)
    ·
      refine ⟨66755465272682683427805131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178014574060487155807480349 66755465272682683427805131)
      ·
        refine ⟨100133197909024025141707697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66755465272682683427805131 100133197909024025141707697)
        ·
          refine ⟨75099898431768018856280773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100133197909024025141707697 75099898431768018856280773)
          ·
            refine ⟨14081230955956503535552645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75099898431768018856280773 14081230955956503535552645)
            ·
              refine ⟨2640230804241844412916121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14081230955956503535552645 2640230804241844412916121)
              ·
                refine ⟨1980173103181383309687091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2640230804241844412916121 1980173103181383309687091)
                ·
                  refine ⟨2970259654772074964530637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980173103181383309687091 2970259654772074964530637)
                  ·
                    refine ⟨1113847370539528111698989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2970259654772074964530637 1113847370539528111698989)
                    ·
                      rfl

theorem cell22_3253815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_3253815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253815 prefixEnd_3253815 := by exact prefixLift 3253815
  have htrace : WordTrace (prefixWord ++ tailWord_3253815) baseStart_3253815 baseEnd_3253815 := by
    simpa [prefixWord, tailWord_3253815, baseEnd_3253815] using wordTrace_append hprefix tailTrace_3253815
  have hstable : (prefixWord ++ tailWord_3253815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253815).length < 2 ^ (prefixWord ++ tailWord_3253815).sum := by decide
  have hdescent : baseEnd_3253815 < baseStart_3253815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253841 : List Nat := [1, 2, 2, 1, 3, 2, 2, 4, 1, 4]
def baseStart_3253841 : Nat := 118140960795 + 3253841 * 2 ^ 59
def prefixEnd_3253841 : Nat := 4983230072969 + 3 ^ 40 * 3253841 * 2
def baseEnd_3253841 : Nat := 1113856270870872710548909

theorem tailTrace_3253841 : CollatzResearch.WordTrace tailWord_3253841 prefixEnd_3253841 1113856270870872710548909 := by
  unfold tailWord_3253841
  simp only [CollatzResearch.WordTrace]
  refine ⟨118677331004897243645433377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79118220669931495763622251 118677331004897243645433377)
  ·
    refine ⟨89007998253672932734075033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118677331004897243645433377 89007998253672932734075033)
    ·
      refine ⟨66755998690254699550556275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89007998253672932734075033 66755998690254699550556275)
      ·
        refine ⟨100133998035382049325834413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66755998690254699550556275 100133998035382049325834413)
        ·
          refine ⟨37550249263268268497187905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100133998035382049325834413 37550249263268268497187905)
          ·
            refine ⟨28162686947451201372890929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37550249263268268497187905 28162686947451201372890929)
            ·
              refine ⟨21122015210588401029668197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28162686947451201372890929 21122015210588401029668197)
              ·
                refine ⟨3960377851985325193062787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21122015210588401029668197 3960377851985325193062787)
                ·
                  refine ⟨5940566777977987789594181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3960377851985325193062787 5940566777977987789594181)
                  ·
                    refine ⟨1113856270870872710548909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5940566777977987789594181 1113856270870872710548909)
                    ·
                      rfl

theorem cell22_3253841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_3253841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253841 prefixEnd_3253841 := by exact prefixLift 3253841
  have htrace : WordTrace (prefixWord ++ tailWord_3253841) baseStart_3253841 baseEnd_3253841 := by
    simpa [prefixWord, tailWord_3253841, baseEnd_3253841] using wordTrace_append hprefix tailTrace_3253841
  have hstable : (prefixWord ++ tailWord_3253841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253841).length < 2 ^ (prefixWord ++ tailWord_3253841).sum := by decide
  have hdescent : baseEnd_3253841 < baseStart_3253841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253884 : List Nat := [2, 2, 2, 1, 1, 2, 1, 11]
def baseStart_3253884 : Nat := 118140960795 + 3253884 * 2 ^ 59
def prefixEnd_3253884 : Nat := 4983230072969 + 3 ^ 40 * 3253884 * 2
def baseEnd_3253884 : Nat := 123763443405514992413753

theorem tailTrace_3253884 : CollatzResearch.WordTrace tailWord_3253884 prefixEnd_3253884 123763443405514992413753 := by
  unfold tailWord_3253884
  simp only [CollatzResearch.WordTrace]
  refine ⟨59339449671870730994624353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79119266229160974659499137 59339449671870730994624353)
  ·
    refine ⟨44504587253903048245968265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59339449671870730994624353 44504587253903048245968265)
    ·
      refine ⟨33378440440427286184476199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44504587253903048245968265 33378440440427286184476199)
      ·
        refine ⟨50067660660640929276714299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33378440440427286184476199 50067660660640929276714299)
        ·
          refine ⟨75101490990961393915071449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50067660660640929276714299 75101490990961393915071449)
          ·
            refine ⟨56326118243221045436303587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75101490990961393915071449 56326118243221045436303587)
            ·
              refine ⟨84489177364831568154455381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56326118243221045436303587 84489177364831568154455381)
              ·
                refine ⟨123763443405514992413753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 84489177364831568154455381 123763443405514992413753)
                ·
                  rfl

theorem cell22_3253884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 11].length) (baseStart_3253884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253884 prefixEnd_3253884 := by exact prefixLift 3253884
  have htrace : WordTrace (prefixWord ++ tailWord_3253884) baseStart_3253884 baseEnd_3253884 := by
    simpa [prefixWord, tailWord_3253884, baseEnd_3253884] using wordTrace_append hprefix tailTrace_3253884
  have hstable : (prefixWord ++ tailWord_3253884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253884).length < 2 ^ (prefixWord ++ tailWord_3253884).sum := by decide
  have hdescent : baseEnd_3253884 < baseStart_3253884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253899 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 2, 7]
def baseStart_3253899 : Nat := 118140960795 + 3253899 * 2 ^ 59
def prefixEnd_3253899 : Nat := 4983230072969 + 3 ^ 40 * 3253899 * 2
def baseEnd_3253899 : Nat := 1113876125456179892598731

theorem tailTrace_3253899 : CollatzResearch.WordTrace tailWord_3253899 prefixEnd_3253899 1113876125456179892598731 := by
  unfold tailWord_3253899
  simp only [CollatzResearch.WordTrace]
  refine ⟨118679446438687119551044751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79119630959124746367363167 118679446438687119551044751)
  ·
    refine ⟨178019169658030679326567127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118679446438687119551044751 178019169658030679326567127)
    ·
      refine ⟨267028754487046018989850691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178019169658030679326567127 267028754487046018989850691)
      ·
        refine ⟨400543131730569028484776037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267028754487046018989850691 400543131730569028484776037)
        ·
          refine ⟨75101837199481692840895507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400543131730569028484776037 75101837199481692840895507)
          ·
            refine ⟨112652755799222539261343261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75101837199481692840895507 112652755799222539261343261)
            ·
              refine ⟨42244783424708452223003723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112652755799222539261343261 42244783424708452223003723)
              ·
                refine ⟨63367175137062678334505585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42244783424708452223003723 63367175137062678334505585)
                ·
                  refine ⟨47525381352797008750879189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63367175137062678334505585 47525381352797008750879189)
                  ·
                    refine ⟨1113876125456179892598731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47525381352797008750879189 1113876125456179892598731)
                    ·
                      rfl

theorem cell22_3253899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_3253899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253899 prefixEnd_3253899 := by exact prefixLift 3253899
  have htrace : WordTrace (prefixWord ++ tailWord_3253899) baseStart_3253899 baseEnd_3253899 := by
    simpa [prefixWord, tailWord_3253899, baseEnd_3253899] using wordTrace_append hprefix tailTrace_3253899
  have hstable : (prefixWord ++ tailWord_3253899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253899).length < 2 ^ (prefixWord ++ tailWord_3253899).sum := by decide
  have hdescent : baseEnd_3253899 < baseStart_3253899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253918 : List Nat := [4, 3, 1, 1, 1, 4, 8]
def baseStart_3253918 : Nat := 118140960795 + 3253918 * 2 ^ 59
def prefixEnd_3253918 : Nat := 4983230072969 + 3 ^ 40 * 3253918 * 2
def baseEnd_3253918 : Nat := 41254912205350747273099

theorem tailTrace_3253918 : CollatzResearch.WordTrace tailWord_3253918 prefixEnd_3253918 41254912205350747273099 := by
  unfold tailWord_3253918
  simp only [CollatzResearch.WordTrace]
  refine ⟨14835017428202285724498301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79120092950412190530657605 14835017428202285724498301)
  ·
    refine ⟨5563131535575857146686863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14835017428202285724498301 5563131535575857146686863)
    ·
      refine ⟨8344697303363785720030295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5563131535575857146686863 8344697303363785720030295)
      ·
        refine ⟨12517045955045678580045443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8344697303363785720030295 12517045955045678580045443)
        ·
          refine ⟨18775568932568517870068165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12517045955045678580045443 18775568932568517870068165)
          ·
            refine ⟨3520419174856597100637781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18775568932568517870068165 3520419174856597100637781)
            ·
              refine ⟨41254912205350747273099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3520419174856597100637781 41254912205350747273099)
              ·
                rfl

theorem cell22_3253918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 8].length) (baseStart_3253918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253918 prefixEnd_3253918 := by exact prefixLift 3253918
  have htrace : WordTrace (prefixWord ++ tailWord_3253918) baseStart_3253918 baseEnd_3253918 := by
    simpa [prefixWord, tailWord_3253918, baseEnd_3253918] using wordTrace_append hprefix tailTrace_3253918
  have hstable : (prefixWord ++ tailWord_3253918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253918).length < 2 ^ (prefixWord ++ tailWord_3253918).sum := by decide
  have hdescent : baseEnd_3253918 < baseStart_3253918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253929 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 11]
def baseStart_3253929 : Nat := 118140960795 + 3253929 * 2 ^ 59
def prefixEnd_3253929 : Nat := 4983230072969 + 3 ^ 40 * 3253929 * 2
def baseEnd_3253929 : Nat := 371295465023089938116213

theorem tailTrace_3253929 : CollatzResearch.WordTrace tailWord_3253929 prefixEnd_3253929 371295465023089938116213 := by
  unfold tailWord_3253929
  simp only [CollatzResearch.WordTrace]
  refine ⟨118680540628578434674636841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79120360419052289783091227 118680540628578434674636841)
  ·
    refine ⟨89010405471433826005977631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118680540628578434674636841 89010405471433826005977631)
    ·
      refine ⟨133515608207150739008966447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89010405471433826005977631 133515608207150739008966447)
      ·
        refine ⟨200273412310726108513449671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133515608207150739008966447 200273412310726108513449671)
        ·
          refine ⟨300410118466089162770174507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200273412310726108513449671 300410118466089162770174507)
          ·
            refine ⟨450615177699133744155261761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300410118466089162770174507 450615177699133744155261761)
            ·
              refine ⟨337961383274350308116446321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450615177699133744155261761 337961383274350308116446321)
              ·
                refine ⟨253471037455762731087334741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337961383274350308116446321 253471037455762731087334741)
                ·
                  refine ⟨371295465023089938116213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 253471037455762731087334741 371295465023089938116213)
                  ·
                    rfl

theorem cell22_3253929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_3253929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253929 prefixEnd_3253929 := by exact prefixLift 3253929
  have htrace : WordTrace (prefixWord ++ tailWord_3253929) baseStart_3253929 baseEnd_3253929 := by
    simpa [prefixWord, tailWord_3253929, baseEnd_3253929] using wordTrace_append hprefix tailTrace_3253929
  have hstable : (prefixWord ++ tailWord_3253929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253929).length < 2 ^ (prefixWord ++ tailWord_3253929).sum := by decide
  have hdescent : baseEnd_3253929 < baseStart_3253929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253954 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3253954 : Nat := 118140960795 + 3253954 * 2 ^ 59
def prefixEnd_3253954 : Nat := 4983230072969 + 3 ^ 40 * 3253954 * 2
def baseEnd_3253954 : Nat := 1113894953080178082473563

theorem tailTrace_3253954 : CollatzResearch.WordTrace tailWord_3253954 prefixEnd_3253954 1113894953080178082473563 := by
  unfold tailWord_3253954
  simp only [CollatzResearch.WordTrace]
  refine ⟨29670363113371965986074229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79120968302325242629531277 29670363113371965986074229)
  ·
    refine ⟨2781596541878621811194459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29670363113371965986074229 2781596541878621811194459)
    ·
      refine ⟨4172394812817932716791689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2781596541878621811194459 4172394812817932716791689)
      ·
        refine ⟨3129296109613449537593767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4172394812817932716791689 3129296109613449537593767)
        ·
          refine ⟨4693944164420174306390651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3129296109613449537593767 4693944164420174306390651)
          ·
            refine ⟨7040916246630261459585977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4693944164420174306390651 7040916246630261459585977)
            ·
              refine ⟨5280687184972696094689483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7040916246630261459585977 5280687184972696094689483)
              ·
                refine ⟨7921030777459044142034225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5280687184972696094689483 7921030777459044142034225)
                ·
                  refine ⟨5940773083094283106525669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7921030777459044142034225 5940773083094283106525669)
                  ·
                    refine ⟨1113894953080178082473563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5940773083094283106525669 1113894953080178082473563)
                    ·
                      rfl

theorem cell22_3253954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3253954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3253954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3253954 prefixEnd_3253954 := by exact prefixLift 3253954
  have htrace : WordTrace (prefixWord ++ tailWord_3253954) baseStart_3253954 baseEnd_3253954 := by
    simpa [prefixWord, tailWord_3253954, baseEnd_3253954] using wordTrace_append hprefix tailTrace_3253954
  have hstable : (prefixWord ++ tailWord_3253954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253954).length < 2 ^ (prefixWord ++ tailWord_3253954).sum := by decide
  have hdescent : baseEnd_3253954 < baseStart_3253954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254040 : List Nat := [2, 1, 2, 3, 1, 1, 5, 2, 2, 3]
def baseStart_3254040 : Nat := 118140960795 + 3254040 * 2 ^ 59
def prefixEnd_3254040 : Nat := 4983230072969 + 3 ^ 40 * 3254040 * 2
def baseEnd_3254040 : Nat := 1113924392637702524823299

theorem tailTrace_3254040 : CollatzResearch.WordTrace tailWord_3254040 prefixEnd_3254040 1113924392637702524823299 := by
  unfold tailWord_3254040
  simp only [CollatzResearch.WordTrace]
  refine ⟨59342294565588150315963787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79123059420784200421285049 59342294565588150315963787)
  ·
    refine ⟨89013441848382225473945681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59342294565588150315963787 89013441848382225473945681)
    ·
      refine ⟨66760081386286669105459261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89013441848382225473945681 66760081386286669105459261)
      ·
        refine ⟨25035030519857500914547223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66760081386286669105459261 25035030519857500914547223)
        ·
          refine ⟨37552545779786251371820835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25035030519857500914547223 37552545779786251371820835)
          ·
            refine ⟨56328818669679377057731253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37552545779786251371820835 56328818669679377057731253)
            ·
              refine ⟨5280826750282441599162305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56328818669679377057731253 5280826750282441599162305)
              ·
                refine ⟨3960620062711831199371729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5280826750282441599162305 3960620062711831199371729)
                ·
                  refine ⟨2970465047033873399528797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3960620062711831199371729 2970465047033873399528797)
                  ·
                    refine ⟨1113924392637702524823299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2970465047033873399528797 1113924392637702524823299)
                    ·
                      rfl

theorem cell22_3254040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_3254040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254040 prefixEnd_3254040 := by exact prefixLift 3254040
  have htrace : WordTrace (prefixWord ++ tailWord_3254040) baseStart_3254040 baseEnd_3254040 := by
    simpa [prefixWord, tailWord_3254040, baseEnd_3254040] using wordTrace_append hprefix tailTrace_3254040
  have hstable : (prefixWord ++ tailWord_3254040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254040).length < 2 ^ (prefixWord ++ tailWord_3254040).sum := by decide
  have hdescent : baseEnd_3254040 < baseStart_3254040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254070 : List Nat := [5, 1, 2, 2, 1, 2, 1, 8]
def baseStart_3254070 : Nat := 118140960795 + 3254070 * 2 ^ 59
def prefixEnd_3254070 : Nat := 4983230072969 + 3 ^ 40 * 3254070 * 2
def baseEnd_3254070 : Nat := 123770518027865827397023

theorem tailTrace_3254070 : CollatzResearch.WordTrace tailWord_3254070 prefixEnd_3254070 123770518027865827397023 := by
  unfold tailWord_3254070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7417855207566725984719979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79123788880711743837013109 7417855207566725984719979)
  ·
    refine ⟨11126782811350088977079969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7417855207566725984719979 11126782811350088977079969)
    ·
      refine ⟨8345087108512566732809977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11126782811350088977079969 8345087108512566732809977)
      ·
        refine ⟨6258815331384425049607483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8345087108512566732809977 6258815331384425049607483)
        ·
          refine ⟨9388222997076637574411225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6258815331384425049607483 9388222997076637574411225)
          ·
            refine ⟨7041167247807478180808419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9388222997076637574411225 7041167247807478180808419)
            ·
              refine ⟨10561750871711217271212629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7041167247807478180808419 10561750871711217271212629)
              ·
                refine ⟨123770518027865827397023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10561750871711217271212629 123770518027865827397023)
                ·
                  rfl

theorem cell22_3254070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_3254070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254070 prefixEnd_3254070 := by exact prefixLift 3254070
  have htrace : WordTrace (prefixWord ++ tailWord_3254070) baseStart_3254070 baseEnd_3254070 := by
    simpa [prefixWord, tailWord_3254070, baseEnd_3254070] using wordTrace_append hprefix tailTrace_3254070
  have hstable : (prefixWord ++ tailWord_3254070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254070).length < 2 ^ (prefixWord ++ tailWord_3254070).sum := by decide
  have hdescent : baseEnd_3254070 < baseStart_3254070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254098 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 7]
def baseStart_3254098 : Nat := 118140960795 + 3254098 * 2 ^ 59
def prefixEnd_3254098 : Nat := 4983230072969 + 3 ^ 40 * 3254098 * 2
def baseEnd_3254098 : Nat := 371314749074336568957707

theorem tailTrace_3254098 : CollatzResearch.WordTrace tailWord_3254098 prefixEnd_3254098 371314749074336568957707 := by
  unfold tailWord_3254098
  simp only [CollatzResearch.WordTrace]
  refine ⟨29671676141241544134384737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79124469709977451025025965 29671676141241544134384737)
  ·
    refine ⟨22253757105931158100788553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29671676141241544134384737 22253757105931158100788553)
    ·
      refine ⟨16690317829448368575591415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22253757105931158100788553 16690317829448368575591415)
      ·
        refine ⟨25035476744172552863387123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16690317829448368575591415 25035476744172552863387123)
        ·
          refine ⟨37553215116258829295080685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25035476744172552863387123 37553215116258829295080685)
          ·
            refine ⟨14082455668597060985655257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37553215116258829295080685 14082455668597060985655257)
            ·
              refine ⟨10561841751447795739241443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14082455668597060985655257 10561841751447795739241443)
              ·
                refine ⟨15842762627171693608862165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10561841751447795739241443 15842762627171693608862165)
                ·
                  refine ⟨371314749074336568957707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15842762627171693608862165 371314749074336568957707)
                  ·
                    rfl

theorem cell22_3254098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_3254098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254098 prefixEnd_3254098 := by exact prefixLift 3254098
  have htrace : WordTrace (prefixWord ++ tailWord_3254098) baseStart_3254098 baseEnd_3254098 := by
    simpa [prefixWord, tailWord_3254098, baseEnd_3254098] using wordTrace_append hprefix tailTrace_3254098
  have hstable : (prefixWord ++ tailWord_3254098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254098).length < 2 ^ (prefixWord ++ tailWord_3254098).sum := by decide
  have hdescent : baseEnd_3254098 < baseStart_3254098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254115 : List Nat := [1, 1, 1, 5, 4, 1, 1, 3, 5]
def baseStart_3254115 : Nat := 118140960795 + 3254115 * 2 ^ 59
def prefixEnd_3254115 : Nat := 4983230072969 + 3 ^ 40 * 3254115 * 2
def baseEnd_3254115 : Nat := 371316688890142443066023

theorem tailTrace_3254115 : CollatzResearch.WordTrace tailWord_3254115 prefixEnd_3254115 371316688890142443066023 := by
  unfold tailWord_3254115
  simp only [CollatzResearch.WordTrace]
  refine ⟨118687324605904588440907799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79124883070603058960605199 118687324605904588440907799)
  ·
    refine ⟨178030986908856882661361699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118687324605904588440907799 178030986908856882661361699)
    ·
      refine ⟨267046480363285323992042549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178030986908856882661361699 267046480363285323992042549)
      ·
        refine ⟨25035607534057999124253989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 267046480363285323992042549 25035607534057999124253989)
        ·
          refine ⟨4694176412635874835797623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25035607534057999124253989 4694176412635874835797623)
          ·
            refine ⟨7041264618953812253696435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4694176412635874835797623 7041264618953812253696435)
            ·
              refine ⟨10561896928430718380544653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7041264618953812253696435 10561896928430718380544653)
              ·
                refine ⟨3960711348161519392704245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10561896928430718380544653 3960711348161519392704245)
                ·
                  refine ⟨371316688890142443066023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3960711348161519392704245 371316688890142443066023)
                  ·
                    rfl

theorem cell22_3254115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 5].length) (baseStart_3254115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254115 prefixEnd_3254115 := by exact prefixLift 3254115
  have htrace : WordTrace (prefixWord ++ tailWord_3254115) baseStart_3254115 baseEnd_3254115 := by
    simpa [prefixWord, tailWord_3254115, baseEnd_3254115] using wordTrace_append hprefix tailTrace_3254115
  have hstable : (prefixWord ++ tailWord_3254115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254115).length < 2 ^ (prefixWord ++ tailWord_3254115).sum := by decide
  have hdescent : baseEnd_3254115 < baseStart_3254115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254218 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_3254218 : Nat := 118140960795 + 3254218 * 2 ^ 59
def prefixEnd_3254218 : Nat := 4983230072969 + 3 ^ 40 * 3254218 * 2
def baseEnd_3254218 : Nat := 1113985325675369393872753

theorem tailTrace_3254218 : CollatzResearch.WordTrace tailWord_3254218 prefixEnd_3254218 1113985325675369393872753 := by
  unfold tailWord_3254218
  simp only [CollatzResearch.WordTrace]
  refine ⟨29672770331132859257976827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79127387549687624687938205 29672770331132859257976827)
  ·
    refine ⟨44509155496699288886965241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29672770331132859257976827 44509155496699288886965241)
    ·
      refine ⟨33381866622524466665223931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44509155496699288886965241 33381866622524466665223931)
      ·
        refine ⟨50072799933786699997835897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33381866622524466665223931 50072799933786699997835897)
        ·
          refine ⟨37554599950340024998376923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50072799933786699997835897 37554599950340024998376923)
          ·
            refine ⟨56331899925510037497565385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37554599950340024998376923 56331899925510037497565385)
            ·
              refine ⟨42248924944132528123174039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56331899925510037497565385 42248924944132528123174039)
              ·
                refine ⟨63373387416198792184761059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42248924944132528123174039 63373387416198792184761059)
                ·
                  refine ⟨95060081124298188277141589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63373387416198792184761059 95060081124298188277141589)
                  ·
                    refine ⟨1113985325675369393872753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95060081124298188277141589 1113985325675369393872753)
                    ·
                      rfl

theorem cell22_3254218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_3254218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254218 prefixEnd_3254218 := by exact prefixLift 3254218
  have htrace : WordTrace (prefixWord ++ tailWord_3254218) baseStart_3254218 baseEnd_3254218 := by
    simpa [prefixWord, tailWord_3254218, baseEnd_3254218] using wordTrace_append hprefix tailTrace_3254218
  have hstable : (prefixWord ++ tailWord_3254218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254218).length < 2 ^ (prefixWord ++ tailWord_3254218).sum := by decide
  have hdescent : baseEnd_3254218 < baseStart_3254218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254226 : List Nat := [3, 2, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_3254226 : Nat := 118140960795 + 3254226 * 2 ^ 59
def prefixEnd_3254226 : Nat := 4983230072969 + 3 ^ 40 * 3254226 * 2
def baseEnd_3254226 : Nat := 1113988064238860039672729

theorem tailTrace_3254226 : CollatzResearch.WordTrace tailWord_3254226 prefixEnd_3254226 1113988064238860039672729 := by
  unfold tailWord_3254226
  simp only [CollatzResearch.WordTrace]
  refine ⟨29672843277125613599549633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79127582072334969598799021 29672843277125613599549633)
  ·
    refine ⟨22254632457844210199662225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29672843277125613599549633 22254632457844210199662225)
    ·
      refine ⟨16690974343383157649746669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22254632457844210199662225 16690974343383157649746669)
      ·
        refine ⟨6259115378768684118655001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16690974343383157649746669 6259115378768684118655001)
        ·
          refine ⟨4694336534076513088991251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6259115378768684118655001 4694336534076513088991251)
          ·
            refine ⟨7041504801114769633486877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4694336534076513088991251 7041504801114769633486877)
            ·
              refine ⟨2640564300418038612557579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7041504801114769633486877 2640564300418038612557579)
              ·
                refine ⟨3960846450627057918836369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2640564300418038612557579 3960846450627057918836369)
                ·
                  refine ⟨2970634837970293439127277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3960846450627057918836369 2970634837970293439127277)
                  ·
                    refine ⟨1113988064238860039672729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2970634837970293439127277 1113988064238860039672729)
                    ·
                      rfl

theorem cell22_3254226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_3254226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254226 prefixEnd_3254226 := by exact prefixLift 3254226
  have htrace : WordTrace (prefixWord ++ tailWord_3254226) baseStart_3254226 baseEnd_3254226 := by
    simpa [prefixWord, tailWord_3254226, baseEnd_3254226] using wordTrace_append hprefix tailTrace_3254226
  have hstable : (prefixWord ++ tailWord_3254226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254226).length < 2 ^ (prefixWord ++ tailWord_3254226).sum := by decide
  have hdescent : baseEnd_3254226 < baseStart_3254226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254280 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 3, 4]
def baseStart_3254280 : Nat := 118140960795 + 3254280 * 2 ^ 59
def prefixEnd_3254280 : Nat := 4983230072969 + 3 ^ 40 * 3254280 * 2
def baseEnd_3254280 : Nat := 1114006549542421898822563

theorem tailTrace_3254280 : CollatzResearch.WordTrace tailWord_3254280 prefixEnd_3254280 1114006549542421898822563 := by
  unfold tailWord_3254280
  simp only [CollatzResearch.WordTrace]
  refine ⟨59346671325153410810332147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79128895100204547747109529 59346671325153410810332147)
  ·
    refine ⟨89020006987730116215498221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59346671325153410810332147 89020006987730116215498221)
    ·
      refine ⟨33382502620398793580811833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89020006987730116215498221 33382502620398793580811833)
      ·
        refine ⟨25036876965299095185608875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33382502620398793580811833 25036876965299095185608875)
        ·
          refine ⟨37555315447948642778413313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25036876965299095185608875 37555315447948642778413313)
          ·
            refine ⟨28166486585961482083809985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37555315447948642778413313 28166486585961482083809985)
            ·
              refine ⟨21124864939471111562857489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28166486585961482083809985 21124864939471111562857489)
              ·
                refine ⟨15843648704603333672143117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21124864939471111562857489 15843648704603333672143117)
                ·
                  refine ⟨5941368264226250127053669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15843648704603333672143117 5941368264226250127053669)
                  ·
                    refine ⟨1114006549542421898822563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5941368264226250127053669 1114006549542421898822563)
                    ·
                      rfl

theorem cell22_3254280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_3254280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254280 prefixEnd_3254280 := by exact prefixLift 3254280
  have htrace : WordTrace (prefixWord ++ tailWord_3254280) baseStart_3254280 baseEnd_3254280 := by
    simpa [prefixWord, tailWord_3254280, baseEnd_3254280] using wordTrace_append hprefix tailTrace_3254280
  have hstable : (prefixWord ++ tailWord_3254280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254280).length < 2 ^ (prefixWord ++ tailWord_3254280).sum := by decide
  have hdescent : baseEnd_3254280 < baseStart_3254280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254327 : List Nat := [1, 1, 3, 1, 2, 2, 3, 4, 2, 3]
def baseStart_3254327 : Nat := 118140960795 + 3254327 * 2 ^ 59
def prefixEnd_3254327 : Nat := 4983230072969 + 3 ^ 40 * 3254327 * 2
def baseEnd_3254327 : Nat := 1114022638602929442897419

theorem tailTrace_3254327 : CollatzResearch.WordTrace tailWord_3254327 prefixEnd_3254327 1114022638602929442897419 := by
  unfold tailWord_3254327
  simp only [CollatzResearch.WordTrace]
  refine ⟨118695056881136548647625235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79130037920757699098416823 118695056881136548647625235)
  ·
    refine ⟨178042585321704822971437853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118695056881136548647625235 178042585321704822971437853)
    ·
      refine ⟨66765969495639308614289195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178042585321704822971437853 66765969495639308614289195)
      ·
        refine ⟨100148954243458962921433793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66765969495639308614289195 100148954243458962921433793)
        ·
          refine ⟨75111715682594222191075345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100148954243458962921433793 75111715682594222191075345)
          ·
            refine ⟨56333786761945666643306509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75111715682594222191075345 56333786761945666643306509)
            ·
              refine ⟨21125170035729624991239941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56333786761945666643306509 21125170035729624991239941)
              ·
                refine ⟨3960969381699304685857489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21125170035729624991239941 3960969381699304685857489)
                ·
                  refine ⟨2970727036274478514393117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3960969381699304685857489 2970727036274478514393117)
                  ·
                    refine ⟨1114022638602929442897419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2970727036274478514393117 1114022638602929442897419)
                    ·
                      rfl

theorem cell22_3254327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_3254327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254327 prefixEnd_3254327 := by exact prefixLift 3254327
  have htrace : WordTrace (prefixWord ++ tailWord_3254327) baseStart_3254327 baseEnd_3254327 := by
    simpa [prefixWord, tailWord_3254327, baseEnd_3254327] using wordTrace_append hprefix tailTrace_3254327
  have hstable : (prefixWord ++ tailWord_3254327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254327).length < 2 ^ (prefixWord ++ tailWord_3254327).sum := by decide
  have hdescent : baseEnd_3254327 < baseStart_3254327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254329 : List Nat := [1, 2, 1, 5, 3, 1, 1, 4, 4]
def baseStart_3254329 : Nat := 118140960795 + 3254329 * 2 ^ 59
def prefixEnd_3254329 : Nat := 4983230072969 + 3 ^ 40 * 3254329 * 2
def baseEnd_3254329 : Nat := 371341107747934034782471

theorem tailTrace_3254329 : CollatzResearch.WordTrace tailWord_3254329 prefixEnd_3254329 371341107747934034782471 := by
  unfold tailWord_3254329
  simp only [CollatzResearch.WordTrace]
  refine ⟨118695129827129302989198041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79130086551419535326132027 118695129827129302989198041)
  ·
    refine ⟨89021347370346977241898531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118695129827129302989198041 89021347370346977241898531)
    ·
      refine ⟨133532021055520465862847797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89021347370346977241898531 133532021055520465862847797)
      ·
        refine ⟨12518626973955043674641981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133532021055520465862847797 12518626973955043674641981)
        ·
          refine ⟨4694485115233141377990743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12518626973955043674641981 4694485115233141377990743)
          ·
            refine ⟨7041727672849712066986115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4694485115233141377990743 7041727672849712066986115)
            ·
              refine ⟨10562591509274568100479173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7041727672849712066986115 10562591509274568100479173)
              ·
                refine ⟨1980485907988981518839845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10562591509274568100479173 1980485907988981518839845)
                ·
                  refine ⟨371341107747934034782471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1980485907988981518839845 371341107747934034782471)
                  ·
                    rfl

theorem cell22_3254329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 4].length) (baseStart_3254329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254329 prefixEnd_3254329 := by exact prefixLift 3254329
  have htrace : WordTrace (prefixWord ++ tailWord_3254329) baseStart_3254329 baseEnd_3254329 := by
    simpa [prefixWord, tailWord_3254329, baseEnd_3254329] using wordTrace_append hprefix tailTrace_3254329
  have hstable : (prefixWord ++ tailWord_3254329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254329).length < 2 ^ (prefixWord ++ tailWord_3254329).sum := by decide
  have hdescent : baseEnd_3254329 < baseStart_3254329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254357 : List Nat := [1, 3, 2, 2, 1, 4, 3, 6]
def baseStart_3254357 : Nat := 118140960795 + 3254357 * 2 ^ 59
def prefixEnd_3254357 : Nat := 4983230072969 + 3 ^ 40 * 3254357 * 2
def baseEnd_3254357 : Nat := 123781434246224373849703

theorem tailTrace_3254357 : CollatzResearch.WordTrace tailWord_3254357 prefixEnd_3254357 123781434246224373849703 := by
  unfold tailWord_3254357
  simp only [CollatzResearch.WordTrace]
  refine ⟨118696151071027863771217325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79130767380685242514144883 118696151071027863771217325)
  ·
    refine ⟨44511056651635448914206497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118696151071027863771217325 44511056651635448914206497)
    ·
      refine ⟨33383292488726586685654873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44511056651635448914206497 33383292488726586685654873)
      ·
        refine ⟨25037469366544940014241155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33383292488726586685654873 25037469366544940014241155)
        ·
          refine ⟨37556204049817410021361733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25037469366544940014241155 37556204049817410021361733)
          ·
            refine ⟨7041788259340764379005325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37556204049817410021361733 7041788259340764379005325)
            ·
              refine ⟨2640670597252786642126997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7041788259340764379005325 2640670597252786642126997)
              ·
                refine ⟨123781434246224373849703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2640670597252786642126997 123781434246224373849703)
                ·
                  rfl

theorem cell22_3254357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 6].length) (baseStart_3254357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254357 prefixEnd_3254357 := by exact prefixLift 3254357
  have htrace : WordTrace (prefixWord ++ tailWord_3254357) baseStart_3254357 baseEnd_3254357 := by
    simpa [prefixWord, tailWord_3254357, baseEnd_3254357] using wordTrace_append hprefix tailTrace_3254357
  have hstable : (prefixWord ++ tailWord_3254357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254357).length < 2 ^ (prefixWord ++ tailWord_3254357).sum := by decide
  have hdescent : baseEnd_3254357 < baseStart_3254357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254378 : List Nat := [3, 1, 3, 2, 4, 1, 1, 2, 2, 3]
def baseStart_3254378 : Nat := 118140960795 + 3254378 * 2 ^ 59
def prefixEnd_3254378 : Nat := 4983230072969 + 3 ^ 40 * 3254378 * 2
def baseEnd_3254378 : Nat := 1114040096945182309872263

theorem tailTrace_3254378 : CollatzResearch.WordTrace tailWord_3254378 prefixEnd_3254378 1114040096945182309872263 := by
  unfold tailWord_3254378
  simp only [CollatzResearch.WordTrace]
  refine ⟨29674229250987946089432947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79131278002634522905154525 29674229250987946089432947)
  ·
    refine ⟨44511343876481919134149421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29674229250987946089432947 44511343876481919134149421)
    ·
      refine ⟨16691753953680719675306033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44511343876481919134149421 16691753953680719675306033)
      ·
        refine ⟨12518815465260539756479525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16691753953680719675306033 12518815465260539756479525)
        ·
          refine ⟨2347277899736351204339911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12518815465260539756479525 2347277899736351204339911)
          ·
            refine ⟨3520916849604526806509867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347277899736351204339911 3520916849604526806509867)
            ·
              refine ⟨5281375274406790209764801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3520916849604526806509867 5281375274406790209764801)
              ·
                refine ⟨3961031455805092657323601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5281375274406790209764801 3961031455805092657323601)
                ·
                  refine ⟨2970773591853819492992701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3961031455805092657323601 2970773591853819492992701)
                  ·
                    refine ⟨1114040096945182309872263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2970773591853819492992701 1114040096945182309872263)
                    ·
                      rfl

theorem cell22_3254378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_3254378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254378 prefixEnd_3254378 := by exact prefixLift 3254378
  have htrace : WordTrace (prefixWord ++ tailWord_3254378) baseStart_3254378 baseEnd_3254378 := by
    simpa [prefixWord, tailWord_3254378, baseEnd_3254378] using wordTrace_append hprefix tailTrace_3254378
  have hstable : (prefixWord ++ tailWord_3254378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254378).length < 2 ^ (prefixWord ++ tailWord_3254378).sum := by decide
  have hdescent : baseEnd_3254378 < baseStart_3254378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254385 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 7]
def baseStart_3254385 : Nat := 118140960795 + 3254385 * 2 ^ 59
def prefixEnd_3254385 : Nat := 4983230072969 + 3 ^ 40 * 3254385 * 2
def baseEnd_3254385 : Nat := 371347497729412208315747

theorem tailTrace_3254385 : CollatzResearch.WordTrace tailWord_3254385 prefixEnd_3254385 371347497729412208315747 := by
  unfold tailWord_3254385
  simp only [CollatzResearch.WordTrace]
  refine ⟨118697172314926424553236609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79131448209950949702157739 118697172314926424553236609)
  ·
    refine ⟨89022879236194818414927457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118697172314926424553236609 89022879236194818414927457)
    ·
      refine ⟨66767159427146113811195593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89022879236194818414927457 66767159427146113811195593)
      ·
        refine ⟨50075369570359585358396695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66767159427146113811195593 50075369570359585358396695)
        ·
          refine ⟨75113054355539378037595043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50075369570359585358396695 75113054355539378037595043)
          ·
            refine ⟨112669581533309067056392565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75113054355539378037595043 112669581533309067056392565)
            ·
              refine ⟨10562773268747725036536803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112669581533309067056392565 10562773268747725036536803)
              ·
                refine ⟨15844159903121587554805205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10562773268747725036536803 15844159903121587554805205)
                ·
                  refine ⟨371347497729412208315747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15844159903121587554805205 371347497729412208315747)
                  ·
                    rfl

theorem cell22_3254385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_3254385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254385 prefixEnd_3254385 := by exact prefixLift 3254385
  have htrace : WordTrace (prefixWord ++ tailWord_3254385) baseStart_3254385 baseEnd_3254385 := by
    simpa [prefixWord, tailWord_3254385, baseEnd_3254385] using wordTrace_append hprefix tailTrace_3254385
  have hstable : (prefixWord ++ tailWord_3254385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254385).length < 2 ^ (prefixWord ++ tailWord_3254385).sum := by decide
  have hdescent : baseEnd_3254385 < baseStart_3254385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254423 : List Nat := [1, 1, 3, 3, 4, 2, 1, 3, 1, 3]
def baseStart_3254423 : Nat := 118140960795 + 3254423 * 2 ^ 59
def prefixEnd_3254423 : Nat := 4983230072969 + 3 ^ 40 * 3254423 * 2
def baseEnd_3254423 : Nat := 1114055501364817192497125

theorem tailTrace_3254423 : CollatzResearch.WordTrace tailWord_3254423 prefixEnd_3254423 1114055501364817192497125 := by
  unfold tailWord_3254423
  simp only [CollatzResearch.WordTrace]
  refine ⟨118698558288788757043119923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79132372192525838028746615 118698558288788757043119923)
  ·
    refine ⟨178047837433183135564679885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118698558288788757043119923 178047837433183135564679885)
    ·
      refine ⟨66767939037443675836754957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178047837433183135564679885 66767939037443675836754957)
      ·
        refine ⟨25037977139041378438783109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66767939037443675836754957 25037977139041378438783109)
        ·
          refine ⟨4694620713570258457271833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25037977139041378438783109 4694620713570258457271833)
          ·
            refine ⟨3520965535177693842953875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4694620713570258457271833 3520965535177693842953875)
            ·
              refine ⟨5281448302766540764430813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3520965535177693842953875 5281448302766540764430813)
              ·
                refine ⟨1980543113537452786661555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5281448302766540764430813 1980543113537452786661555)
                ·
                  refine ⟨2970814670306179179992333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980543113537452786661555 2970814670306179179992333)
                  ·
                    refine ⟨1114055501364817192497125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2970814670306179179992333 1114055501364817192497125)
                    ·
                      rfl

theorem cell22_3254423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_3254423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254423 prefixEnd_3254423 := by exact prefixLift 3254423
  have htrace : WordTrace (prefixWord ++ tailWord_3254423) baseStart_3254423 baseEnd_3254423 := by
    simpa [prefixWord, tailWord_3254423, baseEnd_3254423] using wordTrace_append hprefix tailTrace_3254423
  have hstable : (prefixWord ++ tailWord_3254423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254423).length < 2 ^ (prefixWord ++ tailWord_3254423).sum := by decide
  have hdescent : baseEnd_3254423 < baseStart_3254423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254453 : List Nat := [1, 3, 3, 4, 1, 2, 2, 1, 5]
def baseStart_3254453 : Nat := 118140960795 + 3254453 * 2 ^ 59
def prefixEnd_3254453 : Nat := 4983230072969 + 3 ^ 40 * 3254453 * 2
def baseEnd_3254453 : Nat := 371355256992635704749011

theorem tailTrace_3254453 : CollatzResearch.WordTrace tailWord_3254453 prefixEnd_3254453 371355256992635704749011 := by
  unfold tailWord_3254453
  simp only [CollatzResearch.WordTrace]
  refine ⟨118699652478680072166712013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79133101652453381444474675 118699652478680072166712013)
  ·
    refine ⟨44512369679505027062517005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118699652478680072166712013 44512369679505027062517005)
    ·
      refine ⟨16692138629814385148443877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44512369679505027062517005 16692138629814385148443877)
      ·
        refine ⟨3129775993090197215333227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16692138629814385148443877 3129775993090197215333227)
        ·
          refine ⟨4694663989635295822999841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3129775993090197215333227 4694663989635295822999841)
          ·
            refine ⟨3520997992226471867249881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4694663989635295822999841 3520997992226471867249881)
            ·
              refine ⟨2640748494169853900437411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3520997992226471867249881 2640748494169853900437411)
              ·
                refine ⟨3961122741254780850656117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2640748494169853900437411 3961122741254780850656117)
                ·
                  refine ⟨371355256992635704749011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3961122741254780850656117 371355256992635704749011)
                  ·
                    rfl

theorem cell22_3254453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_3254453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254453 prefixEnd_3254453 := by exact prefixLift 3254453
  have htrace : WordTrace (prefixWord ++ tailWord_3254453) baseStart_3254453 baseEnd_3254453 := by
    simpa [prefixWord, tailWord_3254453, baseEnd_3254453] using wordTrace_append hprefix tailTrace_3254453
  have hstable : (prefixWord ++ tailWord_3254453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254453).length < 2 ^ (prefixWord ++ tailWord_3254453).sum := by decide
  have hdescent : baseEnd_3254453 < baseStart_3254453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254475 : List Nat := [1, 1, 1, 1, 3, 2, 3, 10]
def baseStart_3254475 : Nat := 118140960795 + 3254475 * 2 ^ 59
def prefixEnd_3254475 : Nat := 4983230072969 + 3 ^ 40 * 3254475 * 2
def baseEnd_3254475 : Nat := 123785922447500710021885

theorem tailTrace_3254475 : CollatzResearch.WordTrace tailWord_3254475 prefixEnd_3254475 123785922447500710021885 := by
  unfold tailWord_3254475
  simp only [CollatzResearch.WordTrace]
  refine ⟨118700454884600369924012879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79133636589733579949341919 118700454884600369924012879)
  ·
    refine ⟨178050682326900554886019319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118700454884600369924012879 178050682326900554886019319)
    ·
      refine ⟨267076023490350832329028979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178050682326900554886019319 267076023490350832329028979)
      ·
        refine ⟨400614035235526248493543469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267076023490350832329028979 400614035235526248493543469)
        ·
          refine ⟨150230263213322343185078801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400614035235526248493543469 150230263213322343185078801)
          ·
            refine ⟨112672697409991757388809101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150230263213322343185078801 112672697409991757388809101)
            ·
              refine ⟨42252261528746909020803413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112672697409991757388809101 42252261528746909020803413)
              ·
                refine ⟨123785922447500710021885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42252261528746909020803413 123785922447500710021885)
                ·
                  rfl

theorem cell22_3254475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 10].length) (baseStart_3254475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254475 prefixEnd_3254475 := by exact prefixLift 3254475
  have htrace : WordTrace (prefixWord ++ tailWord_3254475) baseStart_3254475 baseEnd_3254475 := by
    simpa [prefixWord, tailWord_3254475, baseEnd_3254475] using wordTrace_append hprefix tailTrace_3254475
  have hstable : (prefixWord ++ tailWord_3254475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254475).length < 2 ^ (prefixWord ++ tailWord_3254475).sum := by decide
  have hdescent : baseEnd_3254475 < baseStart_3254475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254524 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 5, 3]
def baseStart_3254524 : Nat := 118140960795 + 3254524 * 2 ^ 59
def prefixEnd_3254524 : Nat := 4983230072969 + 3 ^ 40 * 3254524 * 2
def baseEnd_3254524 : Nat := 1114090075728886595721815

theorem tailTrace_3254524 : CollatzResearch.WordTrace tailWord_3254524 prefixEnd_3254524 1114090075728886595721815 := by
  unfold tailWord_3254524
  simp only [CollatzResearch.WordTrace]
  refine ⟨59351121030711425646273313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79134828040948567528364417 59351121030711425646273313)
  ·
    refine ⟨44513340773033569234704985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59351121030711425646273313 44513340773033569234704985)
    ·
      refine ⟨33385005579775176926028739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44513340773033569234704985 33385005579775176926028739)
      ·
        refine ⟨50077508369662765389043109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33385005579775176926028739 50077508369662765389043109)
        ·
          refine ⟨9389532819311768510445583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50077508369662765389043109 9389532819311768510445583)
          ·
            refine ⟨14084299228967652765668375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9389532819311768510445583 14084299228967652765668375)
            ·
              refine ⟨21126448843451479148502563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14084299228967652765668375 21126448843451479148502563)
              ·
                refine ⟨31689673265177218722753845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21126448843451479148502563 31689673265177218722753845)
                ·
                  refine ⟨2970906868610364255258173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31689673265177218722753845 2970906868610364255258173)
                  ·
                    refine ⟨1114090075728886595721815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2970906868610364255258173 1114090075728886595721815)
                    ·
                      rfl

theorem cell22_3254524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_3254524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254524 prefixEnd_3254524 := by exact prefixLift 3254524
  have htrace : WordTrace (prefixWord ++ tailWord_3254524) baseStart_3254524 baseEnd_3254524 := by
    simpa [prefixWord, tailWord_3254524, baseEnd_3254524] using wordTrace_append hprefix tailTrace_3254524
  have hstable : (prefixWord ++ tailWord_3254524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254524).length < 2 ^ (prefixWord ++ tailWord_3254524).sum := by decide
  have hdescent : baseEnd_3254524 < baseStart_3254524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254552 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 4, 5]
def baseStart_3254552 : Nat := 118140960795 + 3254552 * 2 ^ 59
def prefixEnd_3254552 : Nat := 4983230072969 + 3 ^ 40 * 3254552 * 2
def baseEnd_3254552 : Nat := 1114099660701103856021729

theorem tailTrace_3254552 : CollatzResearch.WordTrace tailWord_3254552 prefixEnd_3254552 1114099660701103856021729 := by
  unfold tailWord_3254552
  simp only [CollatzResearch.WordTrace]
  refine ⟨59351631652660706037282955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79135508870214274716377273 59351631652660706037282955)
  ·
    refine ⟨89027447478991059055924433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59351631652660706037282955 89027447478991059055924433)
    ·
      refine ⟨66770585609243294291943325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89027447478991059055924433 66770585609243294291943325)
      ·
        refine ⟨25038969603466235359478747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66770585609243294291943325 25038969603466235359478747)
        ·
          refine ⟨37558454405199353039218121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25038969603466235359478747 37558454405199353039218121)
          ·
            refine ⟨28168840803899514779413591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37558454405199353039218121 28168840803899514779413591)
            ·
              refine ⟨42253261205849272169120387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28168840803899514779413591 42253261205849272169120387)
              ·
                refine ⟨63379891808773908253680581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42253261205849272169120387 63379891808773908253680581)
                ·
                  refine ⟨11883729714145107797565109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63379891808773908253680581 11883729714145107797565109)
                  ·
                    refine ⟨1114099660701103856021729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11883729714145107797565109 1114099660701103856021729)
                    ·
                      rfl

theorem cell22_3254552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_3254552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254552 prefixEnd_3254552 := by exact prefixLift 3254552
  have htrace : WordTrace (prefixWord ++ tailWord_3254552) baseStart_3254552 baseEnd_3254552 := by
    simpa [prefixWord, tailWord_3254552, baseEnd_3254552] using wordTrace_append hprefix tailTrace_3254552
  have hstable : (prefixWord ++ tailWord_3254552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254552).length < 2 ^ (prefixWord ++ tailWord_3254552).sum := by decide
  have hdescent : baseEnd_3254552 < baseStart_3254552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254554 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 7]
def baseStart_3254554 : Nat := 118140960795 + 3254554 * 2 ^ 59
def prefixEnd_3254554 : Nat := 4983230072969 + 3 ^ 40 * 3254554 * 2
def baseEnd_3254554 : Nat := 371366781780658839157241

theorem tailTrace_3254554 : CollatzResearch.WordTrace tailWord_3254554 prefixEnd_3254554 371366781780658839157241 := by
  unfold tailWord_3254554
  simp only [CollatzResearch.WordTrace]
  refine ⟨29675834062828541604034679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79135557500876110944092477 29675834062828541604034679)
  ·
    refine ⟨44513751094242812406052019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29675834062828541604034679 44513751094242812406052019)
    ·
      refine ⟨66770626641364218609078029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44513751094242812406052019 66770626641364218609078029)
      ·
        refine ⟨25038984990511581978404261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66770626641364218609078029 25038984990511581978404261)
        ·
          refine ⟨4694809685720921620950799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25038984990511581978404261 4694809685720921620950799)
          ·
            refine ⟨7042214528581382431426199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4694809685720921620950799 7042214528581382431426199)
            ·
              refine ⟨10563321792872073647139299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7042214528581382431426199 10563321792872073647139299)
              ·
                refine ⟨15844982689308110470708949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10563321792872073647139299 15844982689308110470708949)
                ·
                  refine ⟨371366781780658839157241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15844982689308110470708949 371366781780658839157241)
                  ·
                    rfl

theorem cell22_3254554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_3254554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254554 prefixEnd_3254554 := by exact prefixLift 3254554
  have htrace : WordTrace (prefixWord ++ tailWord_3254554) baseStart_3254554 baseEnd_3254554 := by
    simpa [prefixWord, tailWord_3254554, baseEnd_3254554] using wordTrace_append hprefix tailTrace_3254554
  have hstable : (prefixWord ++ tailWord_3254554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254554).length < 2 ^ (prefixWord ++ tailWord_3254554).sum := by decide
  have hdescent : baseEnd_3254554 < baseStart_3254554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254558 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3254558 : Nat := 118140960795 + 3254558 * 2 ^ 59
def prefixEnd_3254558 : Nat := 4983230072969 + 3 ^ 40 * 3254558 * 2
def baseEnd_3254558 : Nat := 1114101714623721840371711

theorem tailTrace_3254558 : CollatzResearch.WordTrace tailWord_3254558 prefixEnd_3254558 1114101714623721840371711 := by
  unfold tailWord_3254558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14837935267912459387410541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79135654762199783399522885 14837935267912459387410541)
  ·
    refine ⟨5564225725467172270278953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14837935267912459387410541 5564225725467172270278953)
    ·
      refine ⟨4173169294100379202709215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5564225725467172270278953 4173169294100379202709215)
      ·
        refine ⟨6259753941150568804063823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4173169294100379202709215 6259753941150568804063823)
        ·
          refine ⟨9389630911725853206095735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6259753941150568804063823 9389630911725853206095735)
          ·
            refine ⟨14084446367588779809143603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9389630911725853206095735 14084446367588779809143603)
            ·
              refine ⟨21126669551383169713715405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14084446367588779809143603 21126669551383169713715405)
              ·
                refine ⟨7922501081768688642643277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21126669551383169713715405 7922501081768688642643277)
                ·
                  refine ⟨2970937905663258240991229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7922501081768688642643277 2970937905663258240991229)
                  ·
                    refine ⟨1114101714623721840371711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2970937905663258240991229 1114101714623721840371711)
                    ·
                      rfl

theorem cell22_3254558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3254558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254558 prefixEnd_3254558 := by exact prefixLift 3254558
  have htrace : WordTrace (prefixWord ++ tailWord_3254558) baseStart_3254558 baseEnd_3254558 := by
    simpa [prefixWord, tailWord_3254558, baseEnd_3254558] using wordTrace_append hprefix tailTrace_3254558
  have hstable : (prefixWord ++ tailWord_3254558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254558).length < 2 ^ (prefixWord ++ tailWord_3254558).sum := by decide
  have hdescent : baseEnd_3254558 < baseStart_3254558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254584 : List Nat := [2, 1, 2, 1, 3, 1, 3, 4, 1, 4]
def baseStart_3254584 : Nat := 118140960795 + 3254584 * 2 ^ 59
def prefixEnd_3254584 : Nat := 4983230072969 + 3 ^ 40 * 3254584 * 2
def baseEnd_3254584 : Nat := 1114110614955066439221631

theorem tailTrace_3254584 : CollatzResearch.WordTrace tailWord_3254584 prefixEnd_3254584 1114110614955066439221631 := by
  unfold tailWord_3254584
  simp only [CollatzResearch.WordTrace]
  refine ⟨59352215220602740769865403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79136286960803654359820537 59352215220602740769865403)
  ·
    refine ⟨89028322830904111154798105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59352215220602740769865403 89028322830904111154798105)
    ·
      refine ⟨66771242123178083366098579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89028322830904111154798105 66771242123178083366098579)
      ·
        refine ⟨100156863184767125049147869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66771242123178083366098579 100156863184767125049147869)
        ·
          refine ⟨37558823694287671893430451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100156863184767125049147869 37558823694287671893430451)
          ·
            refine ⟨56338235541431507840145677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37558823694287671893430451 56338235541431507840145677)
            ·
              refine ⟨21126838328036815440054629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56338235541431507840145677 21126838328036815440054629)
              ·
                refine ⟨3961282186506902895010243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21126838328036815440054629 3961282186506902895010243)
                ·
                  refine ⟨5941923279760354342515365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3961282186506902895010243 5941923279760354342515365)
                  ·
                    refine ⟨1114110614955066439221631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5941923279760354342515365 1114110614955066439221631)
                    ·
                      rfl

theorem cell22_3254584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_3254584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254584 prefixEnd_3254584 := by exact prefixLift 3254584
  have htrace : WordTrace (prefixWord ++ tailWord_3254584) baseStart_3254584 baseEnd_3254584 := by
    simpa [prefixWord, tailWord_3254584, baseEnd_3254584] using wordTrace_append hprefix tailTrace_3254584
  have hstable : (prefixWord ++ tailWord_3254584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254584).length < 2 ^ (prefixWord ++ tailWord_3254584).sum := by decide
  have hdescent : baseEnd_3254584 < baseStart_3254584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254622 : List Nat := [4, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3254622 : Nat := 118140960795 + 3254622 * 2 ^ 59
def prefixEnd_3254622 : Nat := 4983230072969 + 3 ^ 40 * 3254622 * 2
def baseEnd_3254622 : Nat := 371374541043882335590505

theorem tailTrace_3254622 : CollatzResearch.WordTrace tailWord_3254622 prefixEnd_3254622 371374541043882335590505 := by
  unfold tailWord_3254622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14838227051883476753701765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79137210943378542686409413 14838227051883476753701765)
  ·
    refine ⟨2782167572228151891319081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14838227051883476753701765 2782167572228151891319081)
    ·
      refine ⟨2086625679171113918489311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2782167572228151891319081 2086625679171113918489311)
      ·
        refine ⟨3129938518756670877733967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2086625679171113918489311 3129938518756670877733967)
        ·
          refine ⟨4694907778135006316600951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3129938518756670877733967 4694907778135006316600951)
          ·
            refine ⟨7042361667202509474901427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4694907778135006316600951 7042361667202509474901427)
            ·
              refine ⟨10563542500803764212352141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7042361667202509474901427 10563542500803764212352141)
              ·
                refine ⟨3961328437801411579632053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10563542500803764212352141 3961328437801411579632053)
                ·
                  refine ⟨371374541043882335590505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3961328437801411579632053 371374541043882335590505)
                  ·
                    rfl

theorem cell22_3254622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3254622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254622 prefixEnd_3254622 := by exact prefixLift 3254622
  have htrace : WordTrace (prefixWord ++ tailWord_3254622) baseStart_3254622 baseEnd_3254622 := by
    simpa [prefixWord, tailWord_3254622, baseEnd_3254622] using wordTrace_append hprefix tailTrace_3254622
  have hstable : (prefixWord ++ tailWord_3254622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254622).length < 2 ^ (prefixWord ++ tailWord_3254622).sum := by decide
  have hdescent : baseEnd_3254622 < baseStart_3254622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254764 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_3254764 : Nat := 118140960795 + 3254764 * 2 ^ 59
def prefixEnd_3254764 : Nat := 4983230072969 + 3 ^ 40 * 3254764 * 2
def baseEnd_3254764 : Nat := 1114172232633605969721079

theorem tailTrace_3254764 : CollatzResearch.WordTrace tailWord_3254764 prefixEnd_3254764 1114172232633605969721079 := by
  unfold tailWord_3254764
  simp only [CollatzResearch.WordTrace]
  refine ⟨59355497790276686140641673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79140663720368914854188897 59355497790276686140641673)
  ·
    refine ⟨44516623342707514605481255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59355497790276686140641673 44516623342707514605481255)
    ·
      refine ⟨66774935014061271908221883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44516623342707514605481255 66774935014061271908221883)
      ·
        refine ⟨100162402521091907862332825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66774935014061271908221883 100162402521091907862332825)
        ·
          refine ⟨75121801890818930896749619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100162402521091907862332825 75121801890818930896749619)
          ·
            refine ⟨112682702836228396345124429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75121801890818930896749619 112682702836228396345124429)
            ·
              refine ⟨42256013563585648629421661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112682702836228396345124429 42256013563585648629421661)
              ·
                refine ⟨15846005086344618236033123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42256013563585648629421661 15846005086344618236033123)
                ·
                  refine ⟨23769007629516927354049685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15846005086344618236033123 23769007629516927354049685)
                  ·
                    refine ⟨1114172232633605969721079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23769007629516927354049685 1114172232633605969721079)
                    ·
                      rfl

theorem cell22_3254764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_3254764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254764 prefixEnd_3254764 := by exact prefixLift 3254764
  have htrace : WordTrace (prefixWord ++ tailWord_3254764) baseStart_3254764 baseEnd_3254764 := by
    simpa [prefixWord, tailWord_3254764, baseEnd_3254764] using wordTrace_append hprefix tailTrace_3254764
  have hstable : (prefixWord ++ tailWord_3254764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254764).length < 2 ^ (prefixWord ++ tailWord_3254764).sum := by decide
  have hdescent : baseEnd_3254764 < baseStart_3254764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254781 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_3254781 : Nat := 118140960795 + 3254781 * 2 ^ 59
def prefixEnd_3254781 : Nat := 4983230072969 + 3 ^ 40 * 3254781 * 2
def baseEnd_3254781 : Nat := 1114178052081023592046027

theorem tailTrace_3254781 : CollatzResearch.WordTrace tailWord_3254781 prefixEnd_3254781 1114178052081023592046027 := by
  unfold tailWord_3254781
  simp only [CollatzResearch.WordTrace]
  refine ⟨118711615621491784184652197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79141077080994522789768131 118711615621491784184652197)
  ·
    refine ⟨22258427929029709534622287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118711615621491784184652197 22258427929029709534622287)
    ·
      refine ⟨33387641893544564301933431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22258427929029709534622287 33387641893544564301933431)
      ·
        refine ⟨50081462840316846452900147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33387641893544564301933431 50081462840316846452900147)
        ·
          refine ⟨75122194260475269679350221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50081462840316846452900147 75122194260475269679350221)
          ·
            refine ⟨28170822847678226129756333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75122194260475269679350221 28170822847678226129756333)
            ·
              refine ⟨10564058567879334798658625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28170822847678226129756333 10564058567879334798658625)
              ·
                refine ⟨7923043925909501098993969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10564058567879334798658625 7923043925909501098993969)
                ·
                  refine ⟨5942282944432125824245477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7923043925909501098993969 5942282944432125824245477)
                  ·
                    refine ⟨1114178052081023592046027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5942282944432125824245477 1114178052081023592046027)
                    ·
                      rfl

theorem cell22_3254781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_3254781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254781 prefixEnd_3254781 := by exact prefixLift 3254781
  have htrace : WordTrace (prefixWord ++ tailWord_3254781) baseStart_3254781 baseEnd_3254781 := by
    simpa [prefixWord, tailWord_3254781, baseEnd_3254781] using wordTrace_append hprefix tailTrace_3254781
  have hstable : (prefixWord ++ tailWord_3254781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254781).length < 2 ^ (prefixWord ++ tailWord_3254781).sum := by decide
  have hdescent : baseEnd_3254781 < baseStart_3254781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254785 : List Nat := [1, 2, 4, 1, 3, 2, 3, 2, 4]
def baseStart_3254785 : Nat := 118140960795 + 3254785 * 2 ^ 59
def prefixEnd_3254785 : Nat := 4983230072969 + 3 ^ 40 * 3254785 * 2
def baseEnd_3254785 : Nat := 371393140454256304982005

theorem tailTrace_3254785 : CollatzResearch.WordTrace tailWord_3254785 prefixEnd_3254785 371393140454256304982005 := by
  unfold tailWord_3254785
  simp only [CollatzResearch.WordTrace]
  refine ⟨118711761513477292867797809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79141174342318195245198539 118711761513477292867797809)
  ·
    refine ⟨89033821135107969650848357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118711761513477292867797809 89033821135107969650848357)
    ·
      refine ⟨16693841462832744309534067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89033821135107969650848357 16693841462832744309534067)
      ·
        refine ⟨25040762194249116464301101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16693841462832744309534067 25040762194249116464301101)
        ·
          refine ⟨9390285822843418674112913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25040762194249116464301101 9390285822843418674112913)
          ·
            refine ⟨7042714367132564005584685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9390285822843418674112913 7042714367132564005584685)
            ·
              refine ⟨2641017887674711502094257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7042714367132564005584685 2641017887674711502094257)
              ·
                refine ⟨1980763415756033626570693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641017887674711502094257 1980763415756033626570693)
                ·
                  refine ⟨371393140454256304982005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1980763415756033626570693 371393140454256304982005)
                  ·
                    rfl

theorem cell22_3254785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 4].length) (baseStart_3254785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254785 prefixEnd_3254785 := by exact prefixLift 3254785
  have htrace : WordTrace (prefixWord ++ tailWord_3254785) baseStart_3254785 baseEnd_3254785 := by
    simpa [prefixWord, tailWord_3254785, baseEnd_3254785] using wordTrace_append hprefix tailTrace_3254785
  have hstable : (prefixWord ++ tailWord_3254785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254785).length < 2 ^ (prefixWord ++ tailWord_3254785).sum := by decide
  have hdescent : baseEnd_3254785 < baseStart_3254785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254796 : List Nat := [2, 2, 1, 2, 4, 2, 2, 7]
def baseStart_3254796 : Nat := 118140960795 + 3254796 * 2 ^ 59
def prefixEnd_3254796 : Nat := 4983230072969 + 3 ^ 40 * 3254796 * 2
def baseEnd_3254796 : Nat := 123798131876396505880109

theorem tailTrace_3254796 : CollatzResearch.WordTrace tailWord_3254796 prefixEnd_3254796 123798131876396505880109 := by
  unfold tailWord_3254796
  simp only [CollatzResearch.WordTrace]
  refine ⟨59356081358218720873224121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79141441810958294497632161 59356081358218720873224121)
  ·
    refine ⟨44517061018664040654918091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59356081358218720873224121 44517061018664040654918091)
    ·
      refine ⟨66775591527996060982377137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44517061018664040654918091 66775591527996060982377137)
      ·
        refine ⟨50081693645997045736782853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66775591527996060982377137 50081693645997045736782853)
        ·
          refine ⟨9390317558624446075646785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50081693645997045736782853 9390317558624446075646785)
          ·
            refine ⟨7042738168968334556735089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9390317558624446075646785 7042738168968334556735089)
            ·
              refine ⟨5282053626726250917551317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7042738168968334556735089 5282053626726250917551317)
              ·
                refine ⟨123798131876396505880109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5282053626726250917551317 123798131876396505880109)
                ·
                  rfl

theorem cell22_3254796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 7].length) (baseStart_3254796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254796 prefixEnd_3254796 := by exact prefixLift 3254796
  have htrace : WordTrace (prefixWord ++ tailWord_3254796) baseStart_3254796 baseEnd_3254796 := by
    simpa [prefixWord, tailWord_3254796, baseEnd_3254796] using wordTrace_append hprefix tailTrace_3254796
  have hstable : (prefixWord ++ tailWord_3254796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254796).length < 2 ^ (prefixWord ++ tailWord_3254796).sum := by decide
  have hdescent : baseEnd_3254796 < baseStart_3254796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254809 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 2, 6]
def baseStart_3254809 : Nat := 118140960795 + 3254809 * 2 ^ 59
def prefixEnd_3254809 : Nat := 4983230072969 + 3 ^ 40 * 3254809 * 2
def baseEnd_3254809 : Nat := 1114187637053240852345941

theorem tailTrace_3254809 : CollatzResearch.WordTrace tailWord_3254809 prefixEnd_3254809 1114187637053240852345941 := by
  unfold tailWord_3254809
  simp only [CollatzResearch.WordTrace]
  refine ⟨118712636865390344966671481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79141757910260229977780987 118712636865390344966671481)
  ·
    refine ⟨89034477649042758725003611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118712636865390344966671481 89034477649042758725003611)
    ·
      refine ⟨133551716473564138087505417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89034477649042758725003611 133551716473564138087505417)
      ·
        refine ⟨100163787355173103565629063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133551716473564138087505417 100163787355173103565629063)
        ·
          refine ⟨150245681032759655348443595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100163787355173103565629063 150245681032759655348443595)
          ·
            refine ⟨225368521549139483022665393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150245681032759655348443595 225368521549139483022665393)
            ·
              refine ⟨169026391161854612266999045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225368521549139483022665393 169026391161854612266999045)
              ·
                refine ⟨31692448342847739800062321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169026391161854612266999045 31692448342847739800062321)
                ·
                  refine ⟨23769336257135804850046741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31692448342847739800062321 23769336257135804850046741)
                  ·
                    refine ⟨1114187637053240852345941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23769336257135804850046741 1114187637053240852345941)
                    ·
                      rfl

theorem cell22_3254809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_3254809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254809 prefixEnd_3254809 := by exact prefixLift 3254809
  have htrace : WordTrace (prefixWord ++ tailWord_3254809) baseStart_3254809 baseEnd_3254809 := by
    simpa [prefixWord, tailWord_3254809, baseEnd_3254809] using wordTrace_append hprefix tailTrace_3254809
  have hstable : (prefixWord ++ tailWord_3254809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254809).length < 2 ^ (prefixWord ++ tailWord_3254809).sum := by decide
  have hdescent : baseEnd_3254809 < baseStart_3254809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254836 : List Nat := [2, 5, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3254836 : Nat := 118140960795 + 3254836 * 2 ^ 59
def prefixEnd_3254836 : Nat := 4983230072969 + 3 ^ 40 * 3254836 * 2
def baseEnd_3254836 : Nat := 371398959901673927306953

theorem tailTrace_3254836 : CollatzResearch.WordTrace tailWord_3254836 prefixEnd_3254836 371398959901673927306953 := by
  unfold tailWord_3254836
  simp only [CollatzResearch.WordTrace]
  refine ⟨59356810818146264288952181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79142414424195019051936241 59356810818146264288952181)
  ·
    refine ⟨5564701014201212277089267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59356810818146264288952181 5564701014201212277089267)
    ·
      refine ⟨8347051521301818415633901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5564701014201212277089267 8347051521301818415633901)
      ·
        refine ⟨3130144320488181905862713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8347051521301818415633901 3130144320488181905862713)
        ·
          refine ⟨2347608240366136429397035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3130144320488181905862713 2347608240366136429397035)
          ·
            refine ⟨3521412360549204644095553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347608240366136429397035 3521412360549204644095553)
            ·
              refine ⟨2641059270411903483071665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3521412360549204644095553 2641059270411903483071665)
              ·
                refine ⟨1980794452808927612303749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641059270411903483071665 1980794452808927612303749)
                ·
                  refine ⟨371398959901673927306953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1980794452808927612303749 371398959901673927306953)
                  ·
                    rfl

theorem cell22_3254836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3254836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254836 prefixEnd_3254836 := by exact prefixLift 3254836
  have htrace : WordTrace (prefixWord ++ tailWord_3254836) baseStart_3254836 baseEnd_3254836 := by
    simpa [prefixWord, tailWord_3254836, baseEnd_3254836] using wordTrace_append hprefix tailTrace_3254836
  have hstable : (prefixWord ++ tailWord_3254836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254836).length < 2 ^ (prefixWord ++ tailWord_3254836).sum := by decide
  have hdescent : baseEnd_3254836 < baseStart_3254836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254871 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 3, 4]
def baseStart_3254871 : Nat := 118140960795 + 3254871 * 2 ^ 59
def prefixEnd_3254871 : Nat := 4983230072969 + 3 ^ 40 * 3254871 * 2
def baseEnd_3254871 : Nat := 1114208860920293357295751

theorem tailTrace_3254871 : CollatzResearch.WordTrace tailWord_3254871 prefixEnd_3254871 1114208860920293357295751 := by
  unfold tailWord_3254871
  simp only [CollatzResearch.WordTrace]
  refine ⟨118714898191165729555428467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79143265460777153036952311 118714898191165729555428467)
  ·
    refine ⟨178072347286748594333142701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118714898191165729555428467 178072347286748594333142701)
    ·
      refine ⟨66777130232530722874928513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178072347286748594333142701 66777130232530722874928513)
      ·
        refine ⟨50082847674398042156196385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66777130232530722874928513 50082847674398042156196385)
        ·
          refine ⟨37562135755798531617147289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50082847674398042156196385 37562135755798531617147289)
          ·
            refine ⟨28171601816848898712860467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37562135755798531617147289 28171601816848898712860467)
            ·
              refine ⟨42257402725273348069290701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28171601816848898712860467 42257402725273348069290701)
              ·
                refine ⟨15846526021977505525984013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42257402725273348069290701 15846526021977505525984013)
                ·
                  refine ⟨5942447258241564572244005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15846526021977505525984013 5942447258241564572244005)
                  ·
                    refine ⟨1114208860920293357295751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5942447258241564572244005 1114208860920293357295751)
                    ·
                      rfl

theorem cell22_3254871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_3254871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254871 prefixEnd_3254871 := by exact prefixLift 3254871
  have htrace : WordTrace (prefixWord ++ tailWord_3254871) baseStart_3254871 baseEnd_3254871 := by
    simpa [prefixWord, tailWord_3254871, baseEnd_3254871] using wordTrace_append hprefix tailTrace_3254871
  have hstable : (prefixWord ++ tailWord_3254871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254871).length < 2 ^ (prefixWord ++ tailWord_3254871).sum := by decide
  have hdescent : baseEnd_3254871 < baseStart_3254871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254903 : List Nat := [1, 1, 3, 1, 1, 3, 4, 4, 4]
def baseStart_3254903 : Nat := 118140960795 + 3254903 * 2 ^ 59
def prefixEnd_3254903 : Nat := 4983230072969 + 3 ^ 40 * 3254903 * 2
def baseEnd_3254903 : Nat := 371406605058085313498551

theorem tailTrace_3254903 : CollatzResearch.WordTrace tailWord_3254903 prefixEnd_3254903 371406605058085313498551 := by
  unfold tailWord_3254903
  simp only [CollatzResearch.WordTrace]
  refine ⟨118716065327049799020593363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79144043551366532680395575 118716065327049799020593363)
  ·
    refine ⟨178074097990574698530890045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118716065327049799020593363 178074097990574698530890045)
    ·
      refine ⟨66777786746465511949083767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178074097990574698530890045 66777786746465511949083767)
      ·
        refine ⟨100166680119698267923625651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66777786746465511949083767 100166680119698267923625651)
        ·
          refine ⟨150250020179547401885438477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100166680119698267923625651 150250020179547401885438477)
          ·
            refine ⟨56343757567330275707039429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150250020179547401885438477 56343757567330275707039429)
            ·
              refine ⟨10564454543874426695069893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56343757567330275707039429 10564454543874426695069893)
              ·
                refine ⟨1980835226976455005325605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10564454543874426695069893 1980835226976455005325605)
                ·
                  refine ⟨371406605058085313498551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1980835226976455005325605 371406605058085313498551)
                  ·
                    rfl

theorem cell22_3254903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 4].length) (baseStart_3254903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254903 prefixEnd_3254903 := by exact prefixLift 3254903
  have htrace : WordTrace (prefixWord ++ tailWord_3254903) baseStart_3254903 baseEnd_3254903 := by
    simpa [prefixWord, tailWord_3254903, baseEnd_3254903] using wordTrace_append hprefix tailTrace_3254903
  have hstable : (prefixWord ++ tailWord_3254903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254903).length < 2 ^ (prefixWord ++ tailWord_3254903).sum := by decide
  have hdescent : baseEnd_3254903 < baseStart_3254903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254954 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 6]
def baseStart_3254954 : Nat := 118140960795 + 3254954 * 2 ^ 59
def prefixEnd_3254954 : Nat := 4983230072969 + 3 ^ 40 * 3254954 * 2
def baseEnd_3254954 : Nat := 371412424505502935823499

theorem tailTrace_3254954 : CollatzResearch.WordTrace tailWord_3254954 prefixEnd_3254954 371412424505502935823499 := by
  unfold tailWord_3254954
  simp only [CollatzResearch.WordTrace]
  refine ⟨29679481362466258682674979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79145283633243356487133277 29679481362466258682674979)
  ·
    refine ⟨44519222043699388024012469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29679481362466258682674979 44519222043699388024012469)
    ·
      refine ⟨4173677066596817627251169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44519222043699388024012469 4173677066596817627251169)
      ·
        refine ⟨3130257799947613220438377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4173677066596817627251169 3130257799947613220438377)
        ·
          refine ⟨2347693349960709915328783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3130257799947613220438377 2347693349960709915328783)
          ·
            refine ⟨3521540024941064872993175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347693349960709915328783 3521540024941064872993175)
            ·
              refine ⟨5282310037411597309489763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3521540024941064872993175 5282310037411597309489763)
              ·
                refine ⟨7923465056117395964234645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5282310037411597309489763 7923465056117395964234645)
                ·
                  refine ⟨371412424505502935823499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7923465056117395964234645 371412424505502935823499)
                  ·
                    rfl

theorem cell22_3254954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_3254954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254954 prefixEnd_3254954 := by exact prefixLift 3254954
  have htrace : WordTrace (prefixWord ++ tailWord_3254954) baseStart_3254954 baseEnd_3254954 := by
    simpa [prefixWord, tailWord_3254954, baseEnd_3254954] using wordTrace_append hprefix tailTrace_3254954
  have hstable : (prefixWord ++ tailWord_3254954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254954).length < 2 ^ (prefixWord ++ tailWord_3254954).sum := by decide
  have hdescent : baseEnd_3254954 < baseStart_3254954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254991 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 6, 5]
def baseStart_3254991 : Nat := 118140960795 + 3254991 * 2 ^ 59
def prefixEnd_3254991 : Nat := 4983230072969 + 3 ^ 40 * 3254991 * 2
def baseEnd_3254991 : Nat := 1114249939372653044295383

theorem tailTrace_3254991 : CollatzResearch.WordTrace tailWord_3254991 prefixEnd_3254991 1114249939372653044295383 := by
  unfold tailWord_3254991
  simp only [CollatzResearch.WordTrace]
  refine ⟨118719274950730990049796827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79146183300487326699864551 118719274950730990049796827)
  ·
    refine ⟨178078912426096485074695241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118719274950730990049796827 178078912426096485074695241)
    ·
      refine ⟨133559184319572363806021431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178078912426096485074695241 133559184319572363806021431)
      ·
        refine ⟨200338776479358545709032147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133559184319572363806021431 200338776479358545709032147)
        ·
          refine ⟨300508164719037818563548221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200338776479358545709032147 300508164719037818563548221)
          ·
            refine ⟨112690561769639181961330583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300508164719037818563548221 112690561769639181961330583)
            ·
              refine ⟨169035842654458772941995875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112690561769639181961330583 169035842654458772941995875)
              ·
                refine ⟨253553763981688159412993813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169035842654458772941995875 253553763981688159412993813)
                ·
                  refine ⟨11885332686641632472484085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 253553763981688159412993813 11885332686641632472484085)
                  ·
                    refine ⟨1114249939372653044295383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11885332686641632472484085 1114249939372653044295383)
                    ·
                      rfl

theorem cell22_3254991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_3254991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3254991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3254991 prefixEnd_3254991 := by exact prefixLift 3254991
  have htrace : WordTrace (prefixWord ++ tailWord_3254991) baseStart_3254991 baseEnd_3254991 := by
    simpa [prefixWord, tailWord_3254991, baseEnd_3254991] using wordTrace_append hprefix tailTrace_3254991
  have hstable : (prefixWord ++ tailWord_3254991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254991).length < 2 ^ (prefixWord ++ tailWord_3254991).sum := by decide
  have hdescent : baseEnd_3254991 < baseStart_3254991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255023 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 3, 4]
def baseStart_3255023 : Nat := 118140960795 + 3255023 * 2 ^ 59
def prefixEnd_3255023 : Nat := 4983230072969 + 3 ^ 40 * 3255023 * 2
def baseEnd_3255023 : Nat := 1114260893626615627495285

theorem tailTrace_3255023 : CollatzResearch.WordTrace tailWord_3255023 prefixEnd_3255023 1114260893626615627495285 := by
  unfold tailWord_3255023
  simp only [CollatzResearch.WordTrace]
  refine ⟨118720442086615059514961723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79146961391076706343307815 118720442086615059514961723)
  ·
    refine ⟨178080663129922589272442585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118720442086615059514961723 178080663129922589272442585)
    ·
      refine ⟨133560497347441941954331939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178080663129922589272442585 133560497347441941954331939)
      ·
        refine ⟨200340746021162912931497909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133560497347441941954331939 200340746021162912931497909)
        ·
          refine ⟨18781944939484023087327929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200340746021162912931497909 18781944939484023087327929)
          ·
            refine ⟨14086458704613017315495947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18781944939484023087327929 14086458704613017315495947)
            ·
              refine ⟨21129688056919525973243921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14086458704613017315495947 21129688056919525973243921)
              ·
                refine ⟨15847266042689644479932941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21129688056919525973243921 15847266042689644479932941)
                ·
                  refine ⟨5942724766008616679974853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15847266042689644479932941 5942724766008616679974853)
                  ·
                    refine ⟨1114260893626615627495285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5942724766008616679974853 1114260893626615627495285)
                    ·
                      rfl

theorem cell22_3255023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_3255023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255023 prefixEnd_3255023 := by exact prefixLift 3255023
  have htrace : WordTrace (prefixWord ++ tailWord_3255023) baseStart_3255023 baseEnd_3255023 := by
    simpa [prefixWord, tailWord_3255023, baseEnd_3255023] using wordTrace_append hprefix tailTrace_3255023
  have hstable : (prefixWord ++ tailWord_3255023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255023).length < 2 ^ (prefixWord ++ tailWord_3255023).sum := by decide
  have hdescent : baseEnd_3255023 < baseStart_3255023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255055 : List Nat := [1, 1, 2, 1, 1, 1, 8, 3, 4]
def baseStart_3255055 : Nat := 118140960795 + 3255055 * 2 ^ 59
def prefixEnd_3255055 : Nat := 4983230072969 + 3 ^ 40 * 3255055 * 2
def baseEnd_3255055 : Nat := 371423949293526070231729

theorem tailTrace_3255055 : CollatzResearch.WordTrace tailWord_3255055 prefixEnd_3255055 371423949293526070231729 := by
  unfold tailWord_3255055
  simp only [CollatzResearch.WordTrace]
  refine ⟨118721609222499128980126619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79147739481666085986751079 118721609222499128980126619)
  ·
    refine ⟨178082413833748693470189929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118721609222499128980126619 178082413833748693470189929)
    ·
      refine ⟨133561810375311520102642447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178082413833748693470189929 133561810375311520102642447)
      ·
        refine ⟨200342715562967280153963671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133561810375311520102642447 200342715562967280153963671)
        ·
          refine ⟨300514073344450920230945507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200342715562967280153963671 300514073344450920230945507)
          ·
            refine ⟨450771110016676380346418261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300514073344450920230945507 450771110016676380346418261)
            ·
              refine ⟨5282473945507926332184589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 450771110016676380346418261 5282473945507926332184589)
              ·
                refine ⟨1980927729565472374569221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5282473945507926332184589 1980927729565472374569221)
                ·
                  refine ⟨371423949293526070231729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1980927729565472374569221 371423949293526070231729)
                  ·
                    rfl

theorem cell22_3255055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 4].length) (baseStart_3255055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255055 prefixEnd_3255055 := by exact prefixLift 3255055
  have htrace : WordTrace (prefixWord ++ tailWord_3255055) baseStart_3255055 baseEnd_3255055 := by
    simpa [prefixWord, tailWord_3255055, baseEnd_3255055] using wordTrace_append hprefix tailTrace_3255055
  have hstable : (prefixWord ++ tailWord_3255055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255055).length < 2 ^ (prefixWord ++ tailWord_3255055).sum := by decide
  have hdescent : baseEnd_3255055 < baseStart_3255055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255117 : List Nat := [1, 6, 1, 2, 2, 2, 8]
def baseStart_3255117 : Nat := 118140960795 + 3255117 * 2 ^ 59
def prefixEnd_3255117 : Nat := 4983230072969 + 3 ^ 40 * 3255117 * 2
def baseEnd_3255117 : Nat := 41270113768430767246111

theorem tailTrace_3255117 : CollatzResearch.WordTrace tailWord_3255117 prefixEnd_3255117 41270113768430767246111 := by
  unfold tailWord_3255117
  simp only [CollatzResearch.WordTrace]
  refine ⟨118723870548274513568883605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79149247032183009045922403 118723870548274513568883605)
  ·
    refine ⟨5565181431950367823541419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118723870548274513568883605 5565181431950367823541419)
    ·
      refine ⟨8347772147925551735312129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5565181431950367823541419 8347772147925551735312129)
      ·
        refine ⟨6260829110944163801484097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8347772147925551735312129 6260829110944163801484097)
        ·
          refine ⟨4695621833208122851113073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6260829110944163801484097 4695621833208122851113073)
          ·
            refine ⟨3521716374906092138334805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4695621833208122851113073 3521716374906092138334805)
            ·
              refine ⟨41270113768430767246111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3521716374906092138334805 41270113768430767246111)
              ·
                rfl

theorem cell22_3255117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 8].length) (baseStart_3255117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255117 prefixEnd_3255117 := by exact prefixLift 3255117
  have htrace : WordTrace (prefixWord ++ tailWord_3255117) baseStart_3255117 baseEnd_3255117 := by
    simpa [prefixWord, tailWord_3255117, baseEnd_3255117] using wordTrace_append hprefix tailTrace_3255117
  have hstable : (prefixWord ++ tailWord_3255117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255117).length < 2 ^ (prefixWord ++ tailWord_3255117).sum := by decide
  have hdescent : baseEnd_3255117 < baseStart_3255117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255138 : List Nat := [3, 3, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_3255138 : Nat := 118140960795 + 3255138 * 2 ^ 59
def prefixEnd_3255138 : Nat := 4983230072969 + 3 ^ 40 * 3255138 * 2
def baseEnd_3255138 : Nat := 1114300260476793660869933

theorem tailTrace_3255138 : CollatzResearch.WordTrace tailWord_3255138 prefixEnd_3255138 1114300260476793660869933 := by
  unfold tailWord_3255138
  simp only [CollatzResearch.WordTrace]
  refine ⟨29681159120299608538849517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79149757654132289436932045 29681159120299608538849517)
  ·
    refine ⟨11130434670112353202068569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29681159120299608538849517 11130434670112353202068569)
    ·
      refine ⟨8347826002584264901551427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11130434670112353202068569 8347826002584264901551427)
      ·
        refine ⟨12521739003876397352327141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8347826002584264901551427 12521739003876397352327141)
        ·
          refine ⟨2347826063226824503561339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12521739003876397352327141 2347826063226824503561339)
          ·
            refine ⟨3521739094840236755342009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347826063226824503561339 3521739094840236755342009)
            ·
              refine ⟨2641304321130177566506507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3521739094840236755342009 2641304321130177566506507)
              ·
                refine ⟨3961956481695266349759761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641304321130177566506507 3961956481695266349759761)
                ·
                  refine ⟨2971467361271449762319821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3961956481695266349759761 2971467361271449762319821)
                  ·
                    refine ⟨1114300260476793660869933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2971467361271449762319821 1114300260476793660869933)
                    ·
                      rfl

theorem cell22_3255138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_3255138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255138 prefixEnd_3255138 := by exact prefixLift 3255138
  have htrace : WordTrace (prefixWord ++ tailWord_3255138) baseStart_3255138 baseEnd_3255138 := by
    simpa [prefixWord, tailWord_3255138, baseEnd_3255138] using wordTrace_append hprefix tailTrace_3255138
  have hstable : (prefixWord ++ tailWord_3255138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255138).length < 2 ^ (prefixWord ++ tailWord_3255138).sum := by decide
  have hdescent : baseEnd_3255138 < baseStart_3255138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255205 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 8, 3]
def baseStart_3255205 : Nat := 118140960795 + 3255205 * 2 ^ 59
def prefixEnd_3255205 : Nat := 4983230072969 + 3 ^ 40 * 3255205 * 2
def baseEnd_3255205 : Nat := 1114323195946027819444727

theorem tailTrace_3255205 : CollatzResearch.WordTrace tailWord_3255205 prefixEnd_3255205 1114323195946027819444727 := by
  unfold tailWord_3255205
  simp only [CollatzResearch.WordTrace]
  refine ⟨118727080171955704598087069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79151386781303803065391379 118727080171955704598087069)
  ·
    refine ⟨44522655064483389224282651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118727080171955704598087069 44522655064483389224282651)
    ·
      refine ⟨66783982596725083836423977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44522655064483389224282651 66783982596725083836423977)
      ·
        refine ⟨50087986947543812877317983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66783982596725083836423977 50087986947543812877317983)
        ·
          refine ⟨75131980421315719315976975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50087986947543812877317983 75131980421315719315976975)
          ·
            refine ⟨112697970631973578973965463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75131980421315719315976975 112697970631973578973965463)
            ·
              refine ⟨169046955947960368460948195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112697970631973578973965463 169046955947960368460948195)
              ·
                refine ⟨253570433921940552691422293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169046955947960368460948195 253570433921940552691422293)
                ·
                  refine ⟨2971528522522740851852605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 253570433921940552691422293 2971528522522740851852605)
                  ·
                    refine ⟨1114323195946027819444727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2971528522522740851852605 1114323195946027819444727)
                    ·
                      rfl

theorem cell22_3255205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_3255205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255205 prefixEnd_3255205 := by exact prefixLift 3255205
  have htrace : WordTrace (prefixWord ++ tailWord_3255205) baseStart_3255205 baseEnd_3255205 := by
    simpa [prefixWord, tailWord_3255205, baseEnd_3255205] using wordTrace_append hprefix tailTrace_3255205
  have hstable : (prefixWord ++ tailWord_3255205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255205).length < 2 ^ (prefixWord ++ tailWord_3255205).sum := by decide
  have hdescent : baseEnd_3255205 < baseStart_3255205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255207 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 6]
def baseStart_3255207 : Nat := 118140960795 + 3255207 * 2 ^ 59
def prefixEnd_3255207 : Nat := 4983230072969 + 3 ^ 40 * 3255207 * 2
def baseEnd_3255207 : Nat := 371441293528966826964907

theorem tailTrace_3255207 : CollatzResearch.WordTrace tailWord_3255207 prefixEnd_3255207 371441293528966826964907 := by
  unfold tailWord_3255207
  simp only [CollatzResearch.WordTrace]
  refine ⟨118727153117948458939659875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79151435411965639293106583 118727153117948458939659875)
  ·
    refine ⟨178090729676922688409489813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118727153117948458939659875 178090729676922688409489813)
    ·
      refine ⟨8348002953605751019194835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 178090729676922688409489813 8348002953605751019194835)
      ·
        refine ⟨12522004430408626528792253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8348002953605751019194835 12522004430408626528792253)
        ·
          refine ⟨4695751661403234948297095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12522004430408626528792253 4695751661403234948297095)
          ·
            refine ⟨7043627492104852422445643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4695751661403234948297095 7043627492104852422445643)
            ·
              refine ⟨10565441238157278633668465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7043627492104852422445643 10565441238157278633668465)
              ·
                refine ⟨7924080928617958975251349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10565441238157278633668465 7924080928617958975251349)
                ·
                  refine ⟨371441293528966826964907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7924080928617958975251349 371441293528966826964907)
                  ·
                    rfl

theorem cell22_3255207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 6].length) (baseStart_3255207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255207 prefixEnd_3255207 := by exact prefixLift 3255207
  have htrace : WordTrace (prefixWord ++ tailWord_3255207) baseStart_3255207 baseEnd_3255207 := by
    simpa [prefixWord, tailWord_3255207, baseEnd_3255207] using wordTrace_append hprefix tailTrace_3255207
  have hstable : (prefixWord ++ tailWord_3255207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255207).length < 2 ^ (prefixWord ++ tailWord_3255207).sum := by decide
  have hdescent : baseEnd_3255207 < baseStart_3255207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255267 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 3, 3]
def baseStart_3255267 : Nat := 118140960795 + 3255267 * 2 ^ 59
def prefixEnd_3255267 : Nat := 4983230072969 + 3 ^ 40 * 3255267 * 2
def baseEnd_3255267 : Nat := 1114344419813080324394537

theorem tailTrace_3255267 : CollatzResearch.WordTrace tailWord_3255267 prefixEnd_3255267 1114344419813080324394537 := by
  unfold tailWord_3255267
  simp only [CollatzResearch.WordTrace]
  refine ⟨118729341497731089186844055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79152894331820726124562703 118729341497731089186844055)
  ·
    refine ⟨178094012246596633780266083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118729341497731089186844055 178094012246596633780266083)
    ·
      refine ⟨267141018369894950670399125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178094012246596633780266083 267141018369894950670399125)
      ·
        refine ⟨12522235236088825812674959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 267141018369894950670399125 12522235236088825812674959)
        ·
          refine ⟨18783352854133238719012439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12522235236088825812674959 18783352854133238719012439)
          ·
            refine ⟨28175029281199858078518659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18783352854133238719012439 28175029281199858078518659)
            ·
              refine ⟨42262543921799787117777989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28175029281199858078518659 42262543921799787117777989)
              ·
                refine ⟨7924226985337460084583373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42262543921799787117777989 7924226985337460084583373)
                ·
                  refine ⟨2971585119501547531718765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7924226985337460084583373 2971585119501547531718765)
                  ·
                    refine ⟨1114344419813080324394537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2971585119501547531718765 1114344419813080324394537)
                    ·
                      rfl

theorem cell22_3255267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 3].length) (baseStart_3255267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255267 prefixEnd_3255267 := by exact prefixLift 3255267
  have htrace : WordTrace (prefixWord ++ tailWord_3255267) baseStart_3255267 baseEnd_3255267 := by
    simpa [prefixWord, tailWord_3255267, baseEnd_3255267] using wordTrace_append hprefix tailTrace_3255267
  have hstable : (prefixWord ++ tailWord_3255267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255267).length < 2 ^ (prefixWord ++ tailWord_3255267).sum := by decide
  have hdescent : baseEnd_3255267 < baseStart_3255267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255301 : List Nat := [1, 3, 1, 1, 2, 3, 5, 2, 1, 3]
def baseStart_3255301 : Nat := 118140960795 + 3255301 * 2 ^ 59
def prefixEnd_3255301 : Nat := 4983230072969 + 3 ^ 40 * 3255301 * 2
def baseEnd_3255301 : Nat := 1114356058707915569044433

theorem tailTrace_3255301 : CollatzResearch.WordTrace tailWord_3255301 prefixEnd_3255301 1114356058707915569044433 := by
  unfold tailWord_3255301
  simp only [CollatzResearch.WordTrace]
  refine ⟨118730581579607912993581757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79153721053071941995721171 118730581579607912993581757)
  ·
    refine ⟨44523968092352967372593159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118730581579607912993581757 44523968092352967372593159)
    ·
      refine ⟨66785952138529451058889739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44523968092352967372593159 66785952138529451058889739)
      ·
        refine ⟨100178928207794176588334609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66785952138529451058889739 100178928207794176588334609)
        ·
          refine ⟨75134196155845632441250957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100178928207794176588334609 75134196155845632441250957)
          ·
            refine ⟨28175323558442112165469109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75134196155845632441250957 28175323558442112165469109)
            ·
              refine ⟨2641436583603948015512729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28175323558442112165469109 2641436583603948015512729)
              ·
                refine ⟨1981077437702961011634547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641436583603948015512729 1981077437702961011634547)
                ·
                  refine ⟨2971616156554441517451821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981077437702961011634547 2971616156554441517451821)
                  ·
                    refine ⟨1114356058707915569044433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2971616156554441517451821 1114356058707915569044433)
                    ·
                      rfl

theorem cell22_3255301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_3255301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255301 prefixEnd_3255301 := by exact prefixLift 3255301
  have htrace : WordTrace (prefixWord ++ tailWord_3255301) baseStart_3255301 baseEnd_3255301 := by
    simpa [prefixWord, tailWord_3255301, baseEnd_3255301] using wordTrace_append hprefix tailTrace_3255301
  have hstable : (prefixWord ++ tailWord_3255301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255301).length < 2 ^ (prefixWord ++ tailWord_3255301).sum := by decide
  have hdescent : baseEnd_3255301 < baseStart_3255301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255327 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 3, 4]
def baseStart_3255327 : Nat := 118140960795 + 3255327 * 2 ^ 59
def prefixEnd_3255327 : Nat := 4983230072969 + 3 ^ 40 * 3255327 * 2
def baseEnd_3255327 : Nat := 1114364959039260167894353

theorem tailTrace_3255327 : CollatzResearch.WordTrace tailWord_3255327 prefixEnd_3255327 1114364959039260167894353 := by
  unfold tailWord_3255327
  simp only [CollatzResearch.WordTrace]
  refine ⟨118731529877513719434028235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79154353251675812956018823 118731529877513719434028235)
  ·
    refine ⟨178097294816270579151042353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118731529877513719434028235 178097294816270579151042353)
    ·
      refine ⟨133572971112202934363281765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178097294816270579151042353 133572971112202934363281765)
      ·
        refine ⟨25044932083538050193115331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133572971112202934363281765 25044932083538050193115331)
        ·
          refine ⟨37567398125307075289672997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25044932083538050193115331 37567398125307075289672997)
          ·
            refine ⟨7043887148495076616813687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37567398125307075289672997 7043887148495076616813687)
            ·
              refine ⟨10565830722742614925220531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7043887148495076616813687 10565830722742614925220531)
              ·
                refine ⟨15848746084113922387830797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10565830722742614925220531 15848746084113922387830797)
                ·
                  refine ⟨5943279781542720895436549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15848746084113922387830797 5943279781542720895436549)
                  ·
                    refine ⟨1114364959039260167894353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5943279781542720895436549 1114364959039260167894353)
                    ·
                      rfl

theorem cell22_3255327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_3255327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255327 prefixEnd_3255327 := by exact prefixLift 3255327
  have htrace : WordTrace (prefixWord ++ tailWord_3255327) baseStart_3255327 baseEnd_3255327 := by
    simpa [prefixWord, tailWord_3255327, baseEnd_3255327] using wordTrace_append hprefix tailTrace_3255327
  have hstable : (prefixWord ++ tailWord_3255327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255327).length < 2 ^ (prefixWord ++ tailWord_3255327).sum := by decide
  have hdescent : baseEnd_3255327 < baseStart_3255327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255344 : List Nat := [2, 1, 1, 1, 2, 4, 5, 1, 1, 4]
def baseStart_3255344 : Nat := 118140960795 + 3255344 * 2 ^ 59
def prefixEnd_3255344 : Nat := 4983230072969 + 3 ^ 40 * 3255344 * 2
def baseEnd_3255344 : Nat := 1114370778486677790219301

theorem tailTrace_3255344 : CollatzResearch.WordTrace tailWord_3255344 prefixEnd_3255344 1114370778486677790219301 := by
  unfold tailWord_3255344
  simp only [CollatzResearch.WordTrace]
  refine ⟨59366074959226065668698543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79154766612301420891598057 59366074959226065668698543)
  ·
    refine ⟨89049112438839098503047815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59366074959226065668698543 89049112438839098503047815)
    ·
      refine ⟨133573668658258647754571723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89049112438839098503047815 133573668658258647754571723)
      ·
        refine ⟨200360502987387971631857585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133573668658258647754571723 200360502987387971631857585)
        ·
          refine ⟨150270377240540978723893189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200360502987387971631857585 150270377240540978723893189)
          ·
            refine ⟨28175695732601433510729973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150270377240540978723893189 28175695732601433510729973)
            ·
              refine ⟨2641471474931384391630935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28175695732601433510729973 2641471474931384391630935)
              ·
                refine ⟨3962207212397076587446403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641471474931384391630935 3962207212397076587446403)
                ·
                  refine ⟨5943310818595614881169605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962207212397076587446403 5943310818595614881169605)
                  ·
                    refine ⟨1114370778486677790219301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5943310818595614881169605 1114370778486677790219301)
                    ·
                      rfl

theorem cell22_3255344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 1, 4].length) (baseStart_3255344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255344 prefixEnd_3255344 := by exact prefixLift 3255344
  have htrace : WordTrace (prefixWord ++ tailWord_3255344) baseStart_3255344 baseEnd_3255344 := by
    simpa [prefixWord, tailWord_3255344, baseEnd_3255344] using wordTrace_append hprefix tailTrace_3255344
  have hstable : (prefixWord ++ tailWord_3255344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255344).length < 2 ^ (prefixWord ++ tailWord_3255344).sum := by decide
  have hdescent : baseEnd_3255344 < baseStart_3255344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255374 : List Nat := [4, 1, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_3255374 : Nat := 118140960795 + 3255374 * 2 ^ 59
def prefixEnd_3255374 : Nat := 4983230072969 + 3 ^ 40 * 3255374 * 2
def baseEnd_3255374 : Nat := 1114381048099767711969209

theorem tailTrace_3255374 : CollatzResearch.WordTrace tailWord_3255374 prefixEnd_3255374 1114381048099767711969209 := by
  unfold tailWord_3255374
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841655513542930807623647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79155496072228964307326117 14841655513542930807623647)
  ·
    refine ⟨22262483270314396211435471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14841655513542930807623647 22262483270314396211435471)
    ·
      refine ⟨33393724905471594317153207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22262483270314396211435471 33393724905471594317153207)
      ·
        refine ⟨50090587358207391475729811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33393724905471594317153207 50090587358207391475729811)
        ·
          refine ⟨75135881037311087213594717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50090587358207391475729811 75135881037311087213594717)
          ·
            refine ⟨28175955388991657705098019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75135881037311087213594717 28175955388991657705098019)
            ·
              refine ⟨42263933083487486557647029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28175955388991657705098019 42263933083487486557647029)
              ·
                refine ⟨3962243726576951864779409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42263933083487486557647029 3962243726576951864779409)
                ·
                  refine ⟨2971682794932713898584557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3962243726576951864779409 2971682794932713898584557)
                  ·
                    refine ⟨1114381048099767711969209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2971682794932713898584557 1114381048099767711969209)
                    ·
                      rfl

theorem cell22_3255374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_3255374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255374 prefixEnd_3255374 := by exact prefixLift 3255374
  have htrace : WordTrace (prefixWord ++ tailWord_3255374) baseStart_3255374 baseEnd_3255374 := by
    simpa [prefixWord, tailWord_3255374, baseEnd_3255374] using wordTrace_append hprefix tailTrace_3255374
  have hstable : (prefixWord ++ tailWord_3255374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255374).length < 2 ^ (prefixWord ++ tailWord_3255374).sum := by decide
  have hdescent : baseEnd_3255374 < baseStart_3255374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255385 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 1, 9]
def baseStart_3255385 : Nat := 118140960795 + 3255385 * 2 ^ 59
def prefixEnd_3255385 : Nat := 4983230072969 + 3 ^ 40 * 3255385 * 2
def baseEnd_3255385 : Nat := 1114384813624567349944175

theorem tailTrace_3255385 : CollatzResearch.WordTrace tailWord_3255385 prefixEnd_3255385 1114384813624567349944175 := by
  unfold tailWord_3255385
  simp only [CollatzResearch.WordTrace]
  refine ⟨118733645311303595339639609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79155763540869063559759739 118733645311303595339639609)
  ·
    refine ⟨89050233983477696504729707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118733645311303595339639609 89050233983477696504729707)
    ·
      refine ⟨133575350975216544757094561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89050233983477696504729707 133575350975216544757094561)
      ·
        refine ⟨100181513231412408567820921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133575350975216544757094561 100181513231412408567820921)
        ·
          refine ⟨75136134923559306425865691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100181513231412408567820921 75136134923559306425865691)
          ·
            refine ⟨112704202385338959638798537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75136134923559306425865691 112704202385338959638798537)
            ·
              refine ⟨84528151789004219729098903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112704202385338959638798537 84528151789004219729098903)
              ·
                refine ⟨126792227683506329593648355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84528151789004219729098903 126792227683506329593648355)
                ·
                  refine ⟨190188341525259494390472533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126792227683506329593648355 190188341525259494390472533)
                  ·
                    refine ⟨1114384813624567349944175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 190188341525259494390472533 1114384813624567349944175)
                    ·
                      rfl

theorem cell22_3255385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_3255385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3255385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3255385 prefixEnd_3255385 := by exact prefixLift 3255385
  have htrace : WordTrace (prefixWord ++ tailWord_3255385) baseStart_3255385 baseEnd_3255385 := by
    simpa [prefixWord, tailWord_3255385, baseEnd_3255385] using wordTrace_append hprefix tailTrace_3255385
  have hstable : (prefixWord ++ tailWord_3255385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255385).length < 2 ^ (prefixWord ++ tailWord_3255385).sum := by decide
  have hdescent : baseEnd_3255385 < baseStart_3255385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
