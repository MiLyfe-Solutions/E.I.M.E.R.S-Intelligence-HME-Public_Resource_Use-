import V185TrunkScan23Chunk0993

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5885331 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 5]
def baseStart_5885331 : Nat := 118140960795 + 5885331 * 2 ^ 59
def prefixEnd_5885331 : Nat := 4983230072969 + 3 ^ 40 * 5885331 * 2
def baseEnd_5885331 : Nat := 3022003613806218349096361

theorem tailTrace_5885331 : CollatzResearch.WordTrace tailWord_5885331 prefixEnd_5885331 3022003613806218349096361 := by
  unfold tailWord_5885331
  simp only [CollatzResearch.WordTrace]
  refine ⟨214655656241458396357063847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143103770827638930904709231 214655656241458396357063847)
  ·
    refine ⟨321983484362187594535595771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214655656241458396357063847 321983484362187594535595771)
    ·
      refine ⟨482975226543281391803393657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321983484362187594535595771 482975226543281391803393657)
      ·
        refine ⟨362231419907461043852545243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482975226543281391803393657 362231419907461043852545243)
        ·
          refine ⟨543347129861191565778817865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362231419907461043852545243 543347129861191565778817865)
          ·
            refine ⟨407510347395893674334113399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543347129861191565778817865 407510347395893674334113399)
            ·
              refine ⟨611265521093840511501170099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407510347395893674334113399 611265521093840511501170099)
              ·
                refine ⟨916898281640760767251755149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611265521093840511501170099 916898281640760767251755149)
                ·
                  refine ⟨343836855615285287719408181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916898281640760767251755149 343836855615285287719408181)
                  ·
                    refine ⟨32234705213932995723694517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 343836855615285287719408181 32234705213932995723694517)
                    ·
                      refine ⟨3022003613806218349096361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32234705213932995723694517 3022003613806218349096361)
                      ·
                        rfl

theorem cell23_5885331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_5885331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885331 prefixEnd_5885331 := by exact prefixLift 5885331
  have htrace : WordTrace (prefixWord ++ tailWord_5885331) baseStart_5885331 baseEnd_5885331 := by
    simpa [prefixWord, tailWord_5885331, baseEnd_5885331] using wordTrace_append hprefix tailTrace_5885331
  have hstable : (prefixWord ++ tailWord_5885331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885331).length < 2 ^ (prefixWord ++ tailWord_5885331).sum := by decide
  have hdescent : baseEnd_5885331 < baseStart_5885331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885368 : List Nat := [2, 1, 2, 1, 2, 2, 3, 4, 6]
def baseStart_5885368 : Nat := 118140960795 + 5885368 * 2 ^ 59
def prefixEnd_5885368 : Nat := 4983230072969 + 3 ^ 40 * 5885368 * 2
def baseEnd_5885368 : Nat := 335780290287826078259299

theorem tailTrace_5885368 : CollatzResearch.WordTrace tailWord_5885368 prefixEnd_5885368 335780290287826078259299 := by
  unfold tailWord_5885368
  simp only [CollatzResearch.WordTrace]
  refine ⟨107328502871162175838080379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143104670494882901117440505 107328502871162175838080379)
  ·
    refine ⟨160992754306743263757120569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107328502871162175838080379 160992754306743263757120569)
    ·
      refine ⟨120744565730057447817840427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160992754306743263757120569 120744565730057447817840427)
      ·
        refine ⟨181116848595086171726760641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120744565730057447817840427 181116848595086171726760641)
        ·
          refine ⟨135837636446314628795070481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181116848595086171726760641 135837636446314628795070481)
          ·
            refine ⟨101878227334735971596302861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135837636446314628795070481 101878227334735971596302861)
            ·
              refine ⟨38204335250525989348613573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101878227334735971596302861 38204335250525989348613573)
              ·
                refine ⟨7163312859473623002865045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38204335250525989348613573 7163312859473623002865045)
                ·
                  refine ⟨335780290287826078259299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7163312859473623002865045 335780290287826078259299)
                  ·
                    rfl

theorem cell23_5885368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 6].length) (baseStart_5885368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885368 prefixEnd_5885368 := by exact prefixLift 5885368
  have htrace : WordTrace (prefixWord ++ tailWord_5885368) baseStart_5885368 baseEnd_5885368 := by
    simpa [prefixWord, tailWord_5885368, baseEnd_5885368] using wordTrace_append hprefix tailTrace_5885368
  have hstable : (prefixWord ++ tailWord_5885368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885368).length < 2 ^ (prefixWord ++ tailWord_5885368).sum := by decide
  have hdescent : baseEnd_5885368 < baseStart_5885368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885422 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_5885422 : Nat := 118140960795 + 5885422 * 2 ^ 59
def prefixEnd_5885422 : Nat := 4983230072969 + 3 ^ 40 * 5885422 * 2
def baseEnd_5885422 : Nat := 3022050340545777493058443

theorem tailTrace_5885422 : CollatzResearch.WordTrace tailWord_5885422 prefixEnd_5885422 3022050340545777493058443 := by
  unfold tailWord_5885422
  simp only [CollatzResearch.WordTrace]
  refine ⟨26832371910516089862328315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143105983522752479265751013 26832371910516089862328315)
  ·
    refine ⟨40248557865774134793492473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26832371910516089862328315 40248557865774134793492473)
    ·
      refine ⟨30186418399330601095119355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40248557865774134793492473 30186418399330601095119355)
      ·
        refine ⟨45279627598995901642679033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30186418399330601095119355 45279627598995901642679033)
        ·
          refine ⟨33959720699246926232009275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45279627598995901642679033 33959720699246926232009275)
          ·
            refine ⟨50939581048870389348013913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33959720699246926232009275 50939581048870389348013913)
            ·
              refine ⟨38204685786652792011010435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50939581048870389348013913 38204685786652792011010435)
              ·
                refine ⟨57307028679979188016515653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38204685786652792011010435 57307028679979188016515653)
                ·
                  refine ⟨10745067877496097753096685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57307028679979188016515653 10745067877496097753096685)
                  ·
                    refine ⟨4029400454061036657411257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10745067877496097753096685 4029400454061036657411257)
                    ·
                      refine ⟨3022050340545777493058443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029400454061036657411257 3022050340545777493058443)
                      ·
                        rfl

theorem cell23_5885422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_5885422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885422 prefixEnd_5885422 := by exact prefixLift 5885422
  have htrace : WordTrace (prefixWord ++ tailWord_5885422) baseStart_5885422 baseEnd_5885422 := by
    simpa [prefixWord, tailWord_5885422, baseEnd_5885422] using wordTrace_append hprefix tailTrace_5885422
  have hstable : (prefixWord ++ tailWord_5885422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885422).length < 2 ^ (prefixWord ++ tailWord_5885422).sum := by decide
  have hdescent : baseEnd_5885422 < baseStart_5885422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885429 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_5885429 : Nat := 118140960795 + 5885429 * 2 ^ 59
def prefixEnd_5885429 : Nat := 4983230072969 + 3 ^ 40 * 5885429 * 2
def baseEnd_5885429 : Nat := 3022053934910358965670911

theorem tailTrace_5885429 : CollatzResearch.WordTrace tailWord_5885429 prefixEnd_5885429 3022053934910358965670911 := by
  unfold tailWord_5885429
  simp only [CollatzResearch.WordTrace]
  refine ⟨214659230595103359094131341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143106153730068906062754227 214659230595103359094131341)
  ·
    refine ⟨80497211473163759660299253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214659230595103359094131341 80497211473163759660299253)
    ·
      refine ⟨7546613575609102468153055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80497211473163759660299253 7546613575609102468153055)
      ·
        refine ⟨11319920363413653702229583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7546613575609102468153055 11319920363413653702229583)
        ·
          refine ⟨16979880545120480553344375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11319920363413653702229583 16979880545120480553344375)
          ·
            refine ⟨25469820817680720830016563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16979880545120480553344375 25469820817680720830016563)
            ·
              refine ⟨38204731226521081245024845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25469820817680720830016563 38204731226521081245024845)
              ·
                refine ⟨14326774209945405466884317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38204731226521081245024845 14326774209945405466884317)
                ·
                  refine ⟨5372540328729527050081619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14326774209945405466884317 5372540328729527050081619)
                  ·
                    refine ⟨8058810493094290575122429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5372540328729527050081619 8058810493094290575122429)
                    ·
                      refine ⟨3022053934910358965670911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8058810493094290575122429 3022053934910358965670911)
                      ·
                        rfl

theorem cell23_5885429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_5885429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885429 prefixEnd_5885429 := by exact prefixLift 5885429
  have htrace : WordTrace (prefixWord ++ tailWord_5885429) baseStart_5885429 baseEnd_5885429 := by
    simpa [prefixWord, tailWord_5885429, baseEnd_5885429] using wordTrace_append hprefix tailTrace_5885429
  have hstable : (prefixWord ++ tailWord_5885429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885429).length < 2 ^ (prefixWord ++ tailWord_5885429).sum := by decide
  have hdescent : baseEnd_5885429 < baseStart_5885429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885472 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5885472 : Nat := 118140960795 + 5885472 * 2 ^ 59
def prefixEnd_5885472 : Nat := 4983230072969 + 3 ^ 40 * 5885472 * 2
def baseEnd_5885472 : Nat := 3022076014578502297433213

theorem tailTrace_5885472 : CollatzResearch.WordTrace tailWord_5885472 prefixEnd_5885472 3022076014578502297433213 := by
  unfold tailWord_5885472
  simp only [CollatzResearch.WordTrace]
  refine ⟨107330399466973788718973335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143107199289298384958631113 107330399466973788718973335)
  ·
    refine ⟨160995599200460683078460003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107330399466973788718973335 160995599200460683078460003)
    ·
      refine ⟨241493398800691024617690005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160995599200460683078460003 241493398800691024617690005)
      ·
        refine ⟨11320003068782391778954219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 241493398800691024617690005 11320003068782391778954219)
        ·
          refine ⟨16980004603173587668431329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11320003068782391778954219 16980004603173587668431329)
          ·
            refine ⟨12735003452380190751323497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16980004603173587668431329 12735003452380190751323497)
            ·
              refine ⟨9551252589285143063492623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12735003452380190751323497 9551252589285143063492623)
              ·
                refine ⟨14326878883927714595238935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9551252589285143063492623 14326878883927714595238935)
                ·
                  refine ⟨21490318325891571892858403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14326878883927714595238935 21490318325891571892858403)
                  ·
                    refine ⟨32235477488837357839287605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21490318325891571892858403 32235477488837357839287605)
                    ·
                      refine ⟨3022076014578502297433213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32235477488837357839287605 3022076014578502297433213)
                      ·
                        rfl

theorem cell23_5885472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5885472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885472 prefixEnd_5885472 := by exact prefixLift 5885472
  have htrace : WordTrace (prefixWord ++ tailWord_5885472) baseStart_5885472 baseEnd_5885472 := by
    simpa [prefixWord, tailWord_5885472, baseEnd_5885472] using wordTrace_append hprefix tailTrace_5885472
  have hstable : (prefixWord ++ tailWord_5885472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885472).length < 2 ^ (prefixWord ++ tailWord_5885472).sum := by decide
  have hdescent : baseEnd_5885472 < baseStart_5885472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885475 : List Nat := [1, 1, 1, 4, 5, 2, 9]
def baseStart_5885475 : Nat := 118140960795 + 5885475 * 2 ^ 59
def prefixEnd_5885475 : Nat := 4983230072969 + 3 ^ 40 * 5885475 * 2
def baseEnd_5885475 : Nat := 37309599444697108465379

theorem tailTrace_5885475 : CollatzResearch.WordTrace tailWord_5885475 prefixEnd_5885475 37309599444697108465379 := by
  unfold tailWord_5885475
  simp only [CollatzResearch.WordTrace]
  refine ⟨214660908352936708950305879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143107272235291139300203919 214660908352936708950305879)
  ·
    refine ⟨321991362529405063425458819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214660908352936708950305879 321991362529405063425458819)
    ·
      refine ⟨482987043794107595138188229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321991362529405063425458819 482987043794107595138188229)
      ·
        refine ⟨90560070711395174088410293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 482987043794107595138188229 90560070711395174088410293)
        ·
          refine ⟨8490006629193297570788465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90560070711395174088410293 8490006629193297570788465)
          ·
            refine ⟨6367504971894973178091349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8490006629193297570788465 6367504971894973178091349)
            ·
              refine ⟨37309599444697108465379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6367504971894973178091349 37309599444697108465379)
              ·
                rfl

theorem cell23_5885475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 9].length) (baseStart_5885475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885475 prefixEnd_5885475 := by exact prefixLift 5885475
  have htrace : WordTrace (prefixWord ++ tailWord_5885475) baseStart_5885475 baseEnd_5885475 := by
    simpa [prefixWord, tailWord_5885475, baseEnd_5885475] using wordTrace_append hprefix tailTrace_5885475
  have hstable : (prefixWord ++ tailWord_5885475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885475).length < 2 ^ (prefixWord ++ tailWord_5885475).sum := by decide
  have hdescent : baseEnd_5885475 < baseStart_5885475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885486 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_5885486 : Nat := 118140960795 + 5885486 * 2 ^ 59
def prefixEnd_5885486 : Nat := 4983230072969 + 3 ^ 40 * 5885486 * 2
def baseEnd_5885486 : Nat := 3022083203307665242658149

theorem tailTrace_5885486 : CollatzResearch.WordTrace tailWord_5885486 prefixEnd_5885486 3022083203307665242658149 := by
  unfold tailWord_5885486
  simp only [CollatzResearch.WordTrace]
  refine ⟨26832663694487107228619539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143107539703931238552637541 26832663694487107228619539)
  ·
    refine ⟨40248995541730660842929309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26832663694487107228619539 40248995541730660842929309)
    ·
      refine ⟨15093373328148997816098491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40248995541730660842929309 15093373328148997816098491)
      ·
        refine ⟨22640059992223496724147737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15093373328148997816098491 22640059992223496724147737)
        ·
          refine ⟨16980044994167622543110803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22640059992223496724147737 16980044994167622543110803)
          ·
            refine ⟨25470067491251433814666205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16980044994167622543110803 25470067491251433814666205)
            ·
              refine ⟨9551275309219287680499827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25470067491251433814666205 9551275309219287680499827)
              ·
                refine ⟨14326912963828931520749741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9551275309219287680499827 14326912963828931520749741)
                ·
                  refine ⟨5372592361435849320281153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14326912963828931520749741 5372592361435849320281153)
                  ·
                    refine ⟨4029444271076886990210865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5372592361435849320281153 4029444271076886990210865)
                    ·
                      refine ⟨3022083203307665242658149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029444271076886990210865 3022083203307665242658149)
                      ·
                        rfl

theorem cell23_5885486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_5885486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885486 prefixEnd_5885486 := by exact prefixLift 5885486
  have htrace : WordTrace (prefixWord ++ tailWord_5885486) baseStart_5885486 baseEnd_5885486 := by
    simpa [prefixWord, tailWord_5885486, baseEnd_5885486] using wordTrace_append hprefix tailTrace_5885486
  have hstable : (prefixWord ++ tailWord_5885486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885486).length < 2 ^ (prefixWord ++ tailWord_5885486).sum := by decide
  have hdescent : baseEnd_5885486 < baseStart_5885486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885488 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 2, 7]
def baseStart_5885488 : Nat := 118140960795 + 5885488 * 2 ^ 59
def prefixEnd_5885488 : Nat := 4983230072969 + 3 ^ 40 * 5885488 * 2
def baseEnd_5885488 : Nat := 1007361410089658078277713

theorem tailTrace_5885488 : CollatzResearch.WordTrace tailWord_5885488 prefixEnd_5885488 1007361410089658078277713 := by
  unfold tailWord_5885488
  simp only [CollatzResearch.WordTrace]
  refine ⟨107330691250944806085264559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143107588334593074780352745 107330691250944806085264559)
  ·
    refine ⟨160996036876417209127896839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107330691250944806085264559 160996036876417209127896839)
    ·
      refine ⟨241494055314625813691845259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160996036876417209127896839 241494055314625813691845259)
      ·
        refine ⟨362241082971938720537767889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241494055314625813691845259 362241082971938720537767889)
        ·
          refine ⟨271680812228954040403325917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362241082971938720537767889 271680812228954040403325917)
          ·
            refine ⟨101880304585857765151247219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271680812228954040403325917 101880304585857765151247219)
            ·
              refine ⟨152820456878786647726870829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101880304585857765151247219 152820456878786647726870829)
              ·
                refine ⟨57307671329544992897576561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152820456878786647726870829 57307671329544992897576561)
                ·
                  refine ⟨42980753497158744673182421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57307671329544992897576561 42980753497158744673182421)
                  ·
                    refine ⟨1007361410089658078277713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42980753497158744673182421 1007361410089658078277713)
                    ·
                      rfl

theorem cell23_5885488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_5885488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885488 prefixEnd_5885488 := by exact prefixLift 5885488
  have htrace : WordTrace (prefixWord ++ tailWord_5885488) baseStart_5885488 baseEnd_5885488 := by
    simpa [prefixWord, tailWord_5885488, baseEnd_5885488] using wordTrace_append hprefix tailTrace_5885488
  have hstable : (prefixWord ++ tailWord_5885488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885488).length < 2 ^ (prefixWord ++ tailWord_5885488).sum := by decide
  have hdescent : baseEnd_5885488 < baseStart_5885488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885545 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 2, 4, 3]
def baseStart_5885545 : Nat := 118140960795 + 5885545 * 2 ^ 59
def prefixEnd_5885545 : Nat := 4983230072969 + 3 ^ 40 * 5885545 * 2
def baseEnd_5885545 : Nat := 3022113498666280511820377

theorem tailTrace_5885545 : CollatzResearch.WordTrace tailWord_5885545 prefixEnd_5885545 3022113498666280511820377 := by
  unfold tailWord_5885545
  simp only [CollatzResearch.WordTrace]
  refine ⟨214663461462683110905354089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143108974308455407270236059 214663461462683110905354089)
  ·
    refine ⟨160997596097012333179015567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214663461462683110905354089 160997596097012333179015567)
    ·
      refine ⟨241496394145518499768523351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160997596097012333179015567 241496394145518499768523351)
      ·
        refine ⟨362244591218277749652785027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241496394145518499768523351 362244591218277749652785027)
        ·
          refine ⟨543366886827416624479177541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362244591218277749652785027 543366886827416624479177541)
          ·
            refine ⟨101881291280140617089845789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 543366886827416624479177541 101881291280140617089845789)
            ·
              refine ⟨38205484230052731408692171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101881291280140617089845789 38205484230052731408692171)
              ·
                refine ⟨57308226345079097113038257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38205484230052731408692171 57308226345079097113038257)
                ·
                  refine ⟨42981169758809322834778693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57308226345079097113038257 42981169758809322834778693)
                  ·
                    refine ⟨8058969329776748031521005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42981169758809322834778693 8058969329776748031521005)
                    ·
                      refine ⟨3022113498666280511820377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8058969329776748031521005 3022113498666280511820377)
                      ·
                        rfl

theorem cell23_5885545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 4, 3].length) (baseStart_5885545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885545 prefixEnd_5885545 := by exact prefixLift 5885545
  have htrace : WordTrace (prefixWord ++ tailWord_5885545) baseStart_5885545 baseEnd_5885545 := by
    simpa [prefixWord, tailWord_5885545, baseEnd_5885545] using wordTrace_append hprefix tailTrace_5885545
  have hstable : (prefixWord ++ tailWord_5885545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885545).length < 2 ^ (prefixWord ++ tailWord_5885545).sum := by decide
  have hdescent : baseEnd_5885545 < baseStart_5885545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885565 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 9]
def baseStart_5885565 : Nat := 118140960795 + 5885565 * 2 ^ 59
def prefixEnd_5885565 : Nat := 4983230072969 + 3 ^ 40 * 5885565 * 2
def baseEnd_5885565 : Nat := 335791529808818937063365

theorem tailTrace_5885565 : CollatzResearch.WordTrace tailWord_5885565 prefixEnd_5885565 335791529808818937063365 := by
  unfold tailWord_5885565
  simp only [CollatzResearch.WordTrace]
  refine ⟨214664190922610654321082149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143109460615073769547388099 214664190922610654321082149)
  ·
    refine ⟨40249535797989497685202903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214664190922610654321082149 40249535797989497685202903)
    ·
      refine ⟨60374303696984246527804355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40249535797989497685202903 60374303696984246527804355)
      ·
        refine ⟨90561455545476369791706533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60374303696984246527804355 90561455545476369791706533)
        ·
          refine ⟨16980272914776819335944975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90561455545476369791706533 16980272914776819335944975)
          ·
            refine ⟨25470409372165229003917463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16980272914776819335944975 25470409372165229003917463)
            ·
              refine ⟨38205614058247843505876195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25470409372165229003917463 38205614058247843505876195)
              ·
                refine ⟨57308421087371765258814293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38205614058247843505876195 57308421087371765258814293)
                ·
                  refine ⟨335791529808818937063365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57308421087371765258814293 335791529808818937063365)
                  ·
                    rfl

theorem cell23_5885565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_5885565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885565 prefixEnd_5885565 := by exact prefixLift 5885565
  have htrace : WordTrace (prefixWord ++ tailWord_5885565) baseStart_5885565 baseEnd_5885565 := by
    simpa [prefixWord, tailWord_5885565, baseEnd_5885565] using wordTrace_append hprefix tailTrace_5885565
  have hstable : (prefixWord ++ tailWord_5885565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885565).length < 2 ^ (prefixWord ++ tailWord_5885565).sum := by decide
  have hdescent : baseEnd_5885565 < baseStart_5885565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885592 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 2, 3, 3]
def baseStart_5885592 : Nat := 118140960795 + 5885592 * 2 ^ 59
def prefixEnd_5885592 : Nat := 4983230072969 + 3 ^ 40 * 5885592 * 2
def baseEnd_5885592 : Nat := 3022137632257041827932661

theorem tailTrace_5885592 : CollatzResearch.WordTrace tailWord_5885592 prefixEnd_5885592 3022137632257041827932661 := by
  unfold tailWord_5885592
  simp only [CollatzResearch.WordTrace]
  refine ⟨107332587846756418966157515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143110117129008558621543353 107332587846756418966157515)
  ·
    refine ⟨160998881770134628449236273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107332587846756418966157515 160998881770134628449236273)
    ·
      refine ⟨120749161327600971336927205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160998881770134628449236273 120749161327600971336927205)
      ·
        refine ⟨22640467748925182125673851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120749161327600971336927205 22640467748925182125673851)
        ·
          refine ⟨33960701623387773188510777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22640467748925182125673851 33960701623387773188510777)
          ·
            refine ⟨25470526217540829891383083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33960701623387773188510777 25470526217540829891383083)
            ·
              refine ⟨38205789326311244837074625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25470526217540829891383083 38205789326311244837074625)
              ·
                refine ⟨28654341994733433627805969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38205789326311244837074625 28654341994733433627805969)
                ·
                  refine ⟨21490756496050075220854477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28654341994733433627805969 21490756496050075220854477)
                  ·
                    refine ⟨8059033686018778207820429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21490756496050075220854477 8059033686018778207820429)
                    ·
                      refine ⟨3022137632257041827932661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8059033686018778207820429 3022137632257041827932661)
                      ·
                        rfl

theorem cell23_5885592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_5885592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885592 prefixEnd_5885592 := by exact prefixLift 5885592
  have htrace : WordTrace (prefixWord ++ tailWord_5885592) baseStart_5885592 baseEnd_5885592 := by
    simpa [prefixWord, tailWord_5885592, baseEnd_5885592] using wordTrace_append hprefix tailTrace_5885592
  have hstable : (prefixWord ++ tailWord_5885592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885592).length < 2 ^ (prefixWord ++ tailWord_5885592).sum := by decide
  have hdescent : baseEnd_5885592 < baseStart_5885592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885599 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 7]
def baseStart_5885599 : Nat := 118140960795 + 5885599 * 2 ^ 59
def prefixEnd_5885599 : Nat := 4983230072969 + 3 ^ 40 * 5885599 * 2
def baseEnd_5885599 : Nat := 335793469624624811171681

theorem tailTrace_5885599 : CollatzResearch.WordTrace tailWord_5885599 prefixEnd_5885599 335793469624624811171681 := by
  unfold tailWord_5885599
  simp only [CollatzResearch.WordTrace]
  refine ⟨214665431004487478127819851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143110287336324985418546567 214665431004487478127819851)
  ·
    refine ⟨321998146506731217191729777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214665431004487478127819851 321998146506731217191729777)
    ·
      refine ⟨241498609880048412893797333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321998146506731217191729777 241498609880048412893797333)
      ·
        refine ⟨5660123669063634677198375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 241498609880048412893797333 5660123669063634677198375)
        ·
          refine ⟨8490185503595452015797563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5660123669063634677198375 8490185503595452015797563)
          ·
            refine ⟨12735278255393178023696345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8490185503595452015797563 12735278255393178023696345)
            ·
              refine ⟨9551458691544883517772259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12735278255393178023696345 9551458691544883517772259)
              ·
                refine ⟨14327188037317325276658389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9551458691544883517772259 14327188037317325276658389)
                ·
                  refine ⟨335793469624624811171681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14327188037317325276658389 335793469624624811171681)
                  ·
                    rfl

theorem cell23_5885599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 7].length) (baseStart_5885599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885599 prefixEnd_5885599 := by exact prefixLift 5885599
  have htrace : WordTrace (prefixWord ++ tailWord_5885599) baseStart_5885599 baseEnd_5885599 := by
    simpa [prefixWord, tailWord_5885599, baseEnd_5885599] using wordTrace_append hprefix tailTrace_5885599
  have hstable : (prefixWord ++ tailWord_5885599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885599).length < 2 ^ (prefixWord ++ tailWord_5885599).sum := by decide
  have hdescent : baseEnd_5885599 < baseStart_5885599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885605 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_5885605 : Nat := 118140960795 + 5885605 * 2 ^ 59
def prefixEnd_5885605 : Nat := 4983230072969 + 3 ^ 40 * 5885605 * 2
def baseEnd_5885605 : Nat := 3022144307505550277070101

theorem tailTrace_5885605 : CollatzResearch.WordTrace tailWord_5885605 prefixEnd_5885605 3022144307505550277070101 := by
  unfold tailWord_5885605
  simp only [CollatzResearch.WordTrace]
  refine ⟨214665649842465741152538269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143110433228310494101692179 214665649842465741152538269)
  ·
    refine ⟨80499618690924652932201851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214665649842465741152538269 80499618690924652932201851)
    ·
      refine ⟨120749428036386979398302777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80499618690924652932201851 120749428036386979398302777)
      ·
        refine ⟨90562071027290234548727083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120749428036386979398302777 90562071027290234548727083)
        ·
          refine ⟨135843106540935351823090625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90562071027290234548727083 135843106540935351823090625)
          ·
            refine ⟨101882329905701513867317969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135843106540935351823090625 101882329905701513867317969)
            ·
              refine ⟨76411747429276135400488477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101882329905701513867317969 76411747429276135400488477)
              ·
                refine ⟨28654405285978550775183179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76411747429276135400488477 28654405285978550775183179)
                ·
                  refine ⟨42981607928967826162774769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28654405285978550775183179 42981607928967826162774769)
                  ·
                    refine ⟨32236205946725869622081077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42981607928967826162774769 32236205946725869622081077)
                    ·
                      refine ⟨3022144307505550277070101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32236205946725869622081077 3022144307505550277070101)
                      ·
                        rfl

theorem cell23_5885605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_5885605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885605 prefixEnd_5885605 := by exact prefixLift 5885605
  have htrace : WordTrace (prefixWord ++ tailWord_5885605) baseStart_5885605 baseEnd_5885605 := by
    simpa [prefixWord, tailWord_5885605, baseEnd_5885605] using wordTrace_append hprefix tailTrace_5885605
  have hstable : (prefixWord ++ tailWord_5885605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885605).length < 2 ^ (prefixWord ++ tailWord_5885605).sum := by decide
  have hdescent : baseEnd_5885605 < baseStart_5885605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885615 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 4]
def baseStart_5885615 : Nat := 118140960795 + 5885615 * 2 ^ 59
def prefixEnd_5885615 : Nat := 4983230072969 + 3 ^ 40 * 5885615 * 2
def baseEnd_5885615 : Nat := 3022149442312095237945055

theorem tailTrace_5885615 : CollatzResearch.WordTrace tailWord_5885615 prefixEnd_5885615 3022149442312095237945055 := by
  unfold tailWord_5885615
  simp only [CollatzResearch.WordTrace]
  refine ⟨214666014572429512860402299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143110676381619675240268199 214666014572429512860402299)
  ·
    refine ⟨321999021858644269290603449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214666014572429512860402299 321999021858644269290603449)
    ·
      refine ⟨241499266393983201967952587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321999021858644269290603449 241499266393983201967952587)
      ·
        refine ⟨362248899590974802951928881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241499266393983201967952587 362248899590974802951928881)
        ·
          refine ⟨271686674693231102213946661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362248899590974802951928881 271686674693231102213946661)
          ·
            refine ⟨50941251504980831665114999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271686674693231102213946661 50941251504980831665114999)
            ·
              refine ⟨76411877257471247497672499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50941251504980831665114999 76411877257471247497672499)
              ·
                refine ⟨114617815886206871246508749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76411877257471247497672499 114617815886206871246508749)
                ·
                  refine ⟨42981680957327576717440781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114617815886206871246508749 42981680957327576717440781)
                  ·
                    refine ⟨16118130358997841269040293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42981680957327576717440781 16118130358997841269040293)
                    ·
                      refine ⟨3022149442312095237945055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16118130358997841269040293 3022149442312095237945055)
                      ·
                        rfl

theorem cell23_5885615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_5885615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885615 prefixEnd_5885615 := by exact prefixLift 5885615
  have htrace : WordTrace (prefixWord ++ tailWord_5885615) baseStart_5885615 baseEnd_5885615 := by
    simpa [prefixWord, tailWord_5885615, baseEnd_5885615] using wordTrace_append hprefix tailTrace_5885615
  have hstable : (prefixWord ++ tailWord_5885615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885615).length < 2 ^ (prefixWord ++ tailWord_5885615).sum := by decide
  have hdescent : baseEnd_5885615 < baseStart_5885615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885632 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 4]
def baseStart_5885632 : Nat := 118140960795 + 5885632 * 2 ^ 59
def prefixEnd_5885632 : Nat := 4983230072969 + 3 ^ 40 * 5885632 * 2
def baseEnd_5885632 : Nat := 3022158171483221671432477

theorem tailTrace_5885632 : CollatzResearch.WordTrace tailWord_5885632 prefixEnd_5885632 3022158171483221671432477 := by
  unfold tailWord_5885632
  simp only [CollatzResearch.WordTrace]
  refine ⟨107333317306683962381885575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143111089742245283175847433 107333317306683962381885575)
  ·
    refine ⟨160999975960025943572828363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107333317306683962381885575 160999975960025943572828363)
    ·
      refine ⟨241499963940038915359242545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160999975960025943572828363 241499963940038915359242545)
      ·
        refine ⟨181124972955029186519431909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241499963940038915359242545 181124972955029186519431909)
        ·
          refine ⟨33960932429067972472393483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181124972955029186519431909 33960932429067972472393483)
          ·
            refine ⟨50941398643601958708590225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33960932429067972472393483 50941398643601958708590225)
            ·
              refine ⟨38206048982701469031442669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50941398643601958708590225 38206048982701469031442669)
              ·
                refine ⟨14327268368513050886791001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38206048982701469031442669 14327268368513050886791001)
                ·
                  refine ⟨10745451276384788165093251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14327268368513050886791001 10745451276384788165093251)
                  ·
                    refine ⟨16118176914577182247639877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10745451276384788165093251 16118176914577182247639877)
                    ·
                      refine ⟨3022158171483221671432477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16118176914577182247639877 3022158171483221671432477)
                      ·
                        rfl

theorem cell23_5885632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_5885632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885632 prefixEnd_5885632 := by exact prefixLift 5885632
  have htrace : WordTrace (prefixWord ++ tailWord_5885632) baseStart_5885632 baseEnd_5885632 := by
    simpa [prefixWord, tailWord_5885632, baseEnd_5885632] using wordTrace_append hprefix tailTrace_5885632
  have hstable : (prefixWord ++ tailWord_5885632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885632).length < 2 ^ (prefixWord ++ tailWord_5885632).sum := by decide
  have hdescent : baseEnd_5885632 < baseStart_5885632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885655 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 8]
def baseStart_5885655 : Nat := 118140960795 + 5885655 * 2 ^ 59
def prefixEnd_5885655 : Nat := 4983230072969 + 3 ^ 40 * 5885655 * 2
def baseEnd_5885655 : Nat := 335796664615363897938319

theorem tailTrace_5885655 : CollatzResearch.WordTrace tailWord_5885655 prefixEnd_5885655 335796664615363897938319 := by
  unfold tailWord_5885655
  simp only [CollatzResearch.WordTrace]
  refine ⟨214667473492284599691858419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143111648994856399794572279 214667473492284599691858419)
  ·
    refine ⟨322001210238426899537787629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214667473492284599691858419 322001210238426899537787629)
    ·
      refine ⟨120750453839410087326670361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322001210238426899537787629 120750453839410087326670361)
      ·
        refine ⟨90562840379557565495002771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120750453839410087326670361 90562840379557565495002771)
        ·
          refine ⟨135844260569336348242504157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90562840379557565495002771 135844260569336348242504157)
          ·
            refine ⟨50941597713501130590939059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135844260569336348242504157 50941597713501130590939059)
            ·
              refine ⟨76412396570251695886408589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50941597713501130590939059 76412396570251695886408589)
              ·
                refine ⟨28654648713844385957403221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76412396570251695886408589 28654648713844385957403221)
                ·
                  refine ⟨335796664615363897938319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28654648713844385957403221 335796664615363897938319)
                  ·
                    rfl

theorem cell23_5885655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 8].length) (baseStart_5885655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885655 prefixEnd_5885655 := by exact prefixLift 5885655
  have htrace : WordTrace (prefixWord ++ tailWord_5885655) baseStart_5885655 baseEnd_5885655 := by
    simpa [prefixWord, tailWord_5885655, baseEnd_5885655] using wordTrace_append hprefix tailTrace_5885655
  have hstable : (prefixWord ++ tailWord_5885655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885655).length < 2 ^ (prefixWord ++ tailWord_5885655).sum := by decide
  have hdescent : baseEnd_5885655 < baseStart_5885655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885675 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 6]
def baseStart_5885675 : Nat := 118140960795 + 5885675 * 2 ^ 59
def prefixEnd_5885675 : Nat := 4983230072969 + 3 ^ 40 * 5885675 * 2
def baseEnd_5885675 : Nat := 3022180251151365003194779

theorem tailTrace_5885675 : CollatzResearch.WordTrace tailWord_5885675 prefixEnd_5885675 3022180251151365003194779 := by
  unfold tailWord_5885675
  simp only [CollatzResearch.WordTrace]
  refine ⟨214668202952212143107586479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143112135301474762071724319 214668202952212143107586479)
  ·
    refine ⟨322002304428318214661379719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214668202952212143107586479 322002304428318214661379719)
    ·
      refine ⟨483003456642477321992069579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322002304428318214661379719 483003456642477321992069579)
      ·
        refine ⟨724505184963715982988104369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483003456642477321992069579 724505184963715982988104369)
        ·
          refine ⟨543378888722786987241078277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724505184963715982988104369 543378888722786987241078277)
          ·
            refine ⟨101883541635522560107702177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 543378888722786987241078277 101883541635522560107702177)
            ·
              refine ⟨76412656226641920080776633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101883541635522560107702177 76412656226641920080776633)
              ·
                refine ⟨57309492169981440060582475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76412656226641920080776633 57309492169981440060582475)
                ·
                  refine ⟨85964238254972160090873713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57309492169981440060582475 85964238254972160090873713)
                  ·
                    refine ⟨64473178691229120068155285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85964238254972160090873713 64473178691229120068155285)
                    ·
                      refine ⟨3022180251151365003194779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64473178691229120068155285 3022180251151365003194779)
                      ·
                        rfl

theorem cell23_5885675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_5885675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885675 prefixEnd_5885675 := by exact prefixLift 5885675
  have htrace : WordTrace (prefixWord ++ tailWord_5885675) baseStart_5885675 baseEnd_5885675 := by
    simpa [prefixWord, tailWord_5885675, baseEnd_5885675] using wordTrace_append hprefix tailTrace_5885675
  have hstable : (prefixWord ++ tailWord_5885675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885675).length < 2 ^ (prefixWord ++ tailWord_5885675).sum := by decide
  have hdescent : baseEnd_5885675 < baseStart_5885675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885686 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_5885686 : Nat := 118140960795 + 5885686 * 2 ^ 59
def prefixEnd_5885686 : Nat := 4983230072969 + 3 ^ 40 * 5885686 * 2
def baseEnd_5885686 : Nat := 3022185899438564460157229

theorem tailTrace_5885686 : CollatzResearch.WordTrace tailWord_5885686 prefixEnd_5885686 3022185899438564460157229 := by
  unfold tailWord_5885686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13416787759698268249139807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143112402770114861324157941 13416787759698268249139807)
  ·
    refine ⟨20125181639547402373709711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13416787759698268249139807 20125181639547402373709711)
    ·
      refine ⟨30187772459321103560564567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20125181639547402373709711 30187772459321103560564567)
      ·
        refine ⟨45281658688981655340846851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30187772459321103560564567 45281658688981655340846851)
        ·
          refine ⟨67922488033472483011270277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45281658688981655340846851 67922488033472483011270277)
          ·
            refine ⟨12735466506276090564613177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67922488033472483011270277 12735466506276090564613177)
            ·
              refine ⟨9551599879707067923459883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12735466506276090564613177 9551599879707067923459883)
              ·
                refine ⟨14327399819560601885189825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9551599879707067923459883 14327399819560601885189825)
                ·
                  refine ⟨10745549864670451413892369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14327399819560601885189825 10745549864670451413892369)
                  ·
                    refine ⟨8059162398502838560419277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10745549864670451413892369 8059162398502838560419277)
                    ·
                      refine ⟨3022185899438564460157229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8059162398502838560419277 3022185899438564460157229)
                      ·
                        rfl

theorem cell23_5885686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_5885686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885686 prefixEnd_5885686 := by exact prefixLift 5885686
  have htrace : WordTrace (prefixWord ++ tailWord_5885686) baseStart_5885686 baseEnd_5885686 := by
    simpa [prefixWord, tailWord_5885686, baseEnd_5885686] using wordTrace_append hprefix tailTrace_5885686
  have hstable : (prefixWord ++ tailWord_5885686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885686).length < 2 ^ (prefixWord ++ tailWord_5885686).sum := by decide
  have hdescent : baseEnd_5885686 < baseStart_5885686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885750 : List Nat := [5, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_5885750 : Nat := 118140960795 + 5885750 * 2 ^ 59
def prefixEnd_5885750 : Nat := 4983230072969 + 3 ^ 40 * 5885750 * 2
def baseEnd_5885750 : Nat := 3022218762200452209756935

theorem tailTrace_5885750 : CollatzResearch.WordTrace tailWord_5885750 prefixEnd_5885750 3022218762200452209756935 := by
  unfold tailWord_5885750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13416933651683776932285419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143113958951293620611044469 13416933651683776932285419)
  ·
    refine ⟨20125400477525665398428129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13416933651683776932285419 20125400477525665398428129)
    ·
      refine ⟨15094050358144249048821097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20125400477525665398428129 15094050358144249048821097)
      ·
        refine ⟨11320537768608186786615823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15094050358144249048821097 11320537768608186786615823)
        ·
          refine ⟨16980806652912280179923735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11320537768608186786615823 16980806652912280179923735)
          ·
            refine ⟨25471209979368420269885603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16980806652912280179923735 25471209979368420269885603)
            ·
              refine ⟨38206814969052630404828405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25471209979368420269885603 38206814969052630404828405)
              ·
                refine ⟨3581888903348684100452663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38206814969052630404828405 3581888903348684100452663)
                ·
                  refine ⟨5372833355023026150678995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3581888903348684100452663 5372833355023026150678995)
                  ·
                    refine ⟨8059250032534539226018493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5372833355023026150678995 8059250032534539226018493)
                    ·
                      refine ⟨3022218762200452209756935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8059250032534539226018493 3022218762200452209756935)
                      ·
                        rfl

theorem cell23_5885750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_5885750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885750 prefixEnd_5885750 := by exact prefixLift 5885750
  have htrace : WordTrace (prefixWord ++ tailWord_5885750) baseStart_5885750 baseEnd_5885750 := by
    simpa [prefixWord, tailWord_5885750, baseEnd_5885750] using wordTrace_append hprefix tailTrace_5885750
  have hstable : (prefixWord ++ tailWord_5885750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885750).length < 2 ^ (prefixWord ++ tailWord_5885750).sum := by decide
  have hdescent : baseEnd_5885750 < baseStart_5885750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885756 : List Nat := [2, 2, 2, 2, 1, 1, 6, 1, 1, 1, 4]
def baseStart_5885756 : Nat := 118140960795 + 5885756 * 2 ^ 59
def prefixEnd_5885756 : Nat := 4983230072969 + 3 ^ 40 * 5885756 * 2
def baseEnd_5885756 : Nat := 3022221843084379186281907

theorem tailTrace_5885756 : CollatzResearch.WordTrace tailWord_5885756 prefixEnd_5885756 3022221843084379186281907 := by
  unfold tailWord_5885756
  simp only [CollatzResearch.WordTrace]
  refine ⟨107335578632459346970642561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143114104843279129294190081 107335578632459346970642561)
  ·
    refine ⟨80501683974344510227981921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107335578632459346970642561 80501683974344510227981921)
    ·
      refine ⟨60376262980758382670986441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80501683974344510227981921 60376262980758382670986441)
      ·
        refine ⟨45282197235568787003239831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60376262980758382670986441 45282197235568787003239831)
        ·
          refine ⟨67923295853353180504859747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45282197235568787003239831 67923295853353180504859747)
          ·
            refine ⟨101884943780029770757289621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67923295853353180504859747 101884943780029770757289621)
            ·
              refine ⟨4775856739688895504247951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101884943780029770757289621 4775856739688895504247951)
              ·
                refine ⟨7163785109533343256371927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775856739688895504247951 7163785109533343256371927)
                ·
                  refine ⟨10745677664300014884557891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7163785109533343256371927 10745677664300014884557891)
                  ·
                    refine ⟨16118516496450022326836837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10745677664300014884557891 16118516496450022326836837)
                    ·
                      refine ⟨3022221843084379186281907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16118516496450022326836837 3022221843084379186281907)
                      ·
                        rfl

theorem cell23_5885756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_5885756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885756 prefixEnd_5885756 := by exact prefixLift 5885756
  have htrace : WordTrace (prefixWord ++ tailWord_5885756) baseStart_5885756 baseEnd_5885756 := by
    simpa [prefixWord, tailWord_5885756, baseEnd_5885756] using wordTrace_append hprefix tailTrace_5885756
  have hstable : (prefixWord ++ tailWord_5885756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885756).length < 2 ^ (prefixWord ++ tailWord_5885756).sum := by decide
  have hdescent : baseEnd_5885756 < baseStart_5885756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885783 : List Nat := [1, 1, 3, 2, 5, 1, 3, 1, 2, 4]
def baseStart_5885783 : Nat := 118140960795 + 5885783 * 2 ^ 59
def prefixEnd_5885783 : Nat := 4983230072969 + 3 ^ 40 * 5885783 * 2
def baseEnd_5885783 : Nat := 1007411902354016860214761

theorem tailTrace_5885783 : CollatzResearch.WordTrace tailWord_5885783 prefixEnd_5885783 1007411902354016860214761 := by
  unfold tailWord_5885783
  simp only [CollatzResearch.WordTrace]
  refine ⟨214672142035820877552518003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143114761357213918368345335 214672142035820877552518003)
  ·
    refine ⟨322008213053731316328777005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214672142035820877552518003 322008213053731316328777005)
    ·
      refine ⟨120753079895149243623291377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322008213053731316328777005 120753079895149243623291377)
      ·
        refine ⟨90564809921361932717468533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120753079895149243623291377 90564809921361932717468533)
        ·
          refine ⟨8490450930127681192262675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90564809921361932717468533 8490450930127681192262675)
          ·
            refine ⟨12735676395191521788394013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8490450930127681192262675 12735676395191521788394013)
            ·
              refine ⟨4775878648196820670647755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12735676395191521788394013 4775878648196820670647755)
              ·
                refine ⟨7163817972295231005971633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775878648196820670647755 7163817972295231005971633)
                ·
                  refine ⟨5372863479221423254478725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7163817972295231005971633 5372863479221423254478725)
                  ·
                    refine ⟨1007411902354016860214761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5372863479221423254478725 1007411902354016860214761)
                    ·
                      rfl

theorem cell23_5885783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_5885783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885783 prefixEnd_5885783 := by exact prefixLift 5885783
  have htrace : WordTrace (prefixWord ++ tailWord_5885783) baseStart_5885783 baseEnd_5885783 := by
    simpa [prefixWord, tailWord_5885783, baseEnd_5885783] using wordTrace_append hprefix tailTrace_5885783
  have hstable : (prefixWord ++ tailWord_5885783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885783).length < 2 ^ (prefixWord ++ tailWord_5885783).sum := by decide
  have hdescent : baseEnd_5885783 < baseStart_5885783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885796 : List Nat := [2, 3, 1, 1, 5, 2, 2, 7]
def baseStart_5885796 : Nat := 118140960795 + 5885796 * 2 ^ 59
def prefixEnd_5885796 : Nat := 4983230072969 + 3 ^ 40 * 5885796 * 2
def baseEnd_5885796 : Nat := 111934903048539223325249

theorem tailTrace_5885796 : CollatzResearch.WordTrace tailWord_5885796 prefixEnd_5885796 111934903048539223325249 := by
  unfold tailWord_5885796
  simp only [CollatzResearch.WordTrace]
  refine ⟨107336308092386890386370621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143115077456515853848494161 107336308092386890386370621)
  ·
    refine ⟨40251115534645083894888983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107336308092386890386370621 40251115534645083894888983)
    ·
      refine ⟨60376673301967625842333475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40251115534645083894888983 60376673301967625842333475)
      ·
        refine ⟨90565009952951438763500213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60376673301967625842333475 90565009952951438763500213)
        ·
          refine ⟨8490469683089197384078145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90565009952951438763500213 8490469683089197384078145)
          ·
            refine ⟨6367852262316898038058609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8490469683089197384078145 6367852262316898038058609)
            ·
              refine ⟨4775889196737673528543957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6367852262316898038058609 4775889196737673528543957)
              ·
                refine ⟨111934903048539223325249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4775889196737673528543957 111934903048539223325249)
                ·
                  rfl

theorem cell23_5885796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 7].length) (baseStart_5885796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885796 prefixEnd_5885796 := by exact prefixLift 5885796
  have htrace : WordTrace (prefixWord ++ tailWord_5885796) baseStart_5885796 baseEnd_5885796 := by
    simpa [prefixWord, tailWord_5885796, baseEnd_5885796] using wordTrace_append hprefix tailTrace_5885796
  have hstable : (prefixWord ++ tailWord_5885796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885796).length < 2 ^ (prefixWord ++ tailWord_5885796).sum := by decide
  have hdescent : baseEnd_5885796 < baseStart_5885796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885850 : List Nat := [3, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2]
def baseStart_5885850 : Nat := 118140960795 + 5885850 * 2 ^ 59
def prefixEnd_5885850 : Nat := 4983230072969 + 3 ^ 40 * 5885850 * 2
def baseEnd_5885850 : Nat := 3022270110265901818506475

theorem tailTrace_5885850 : CollatzResearch.WordTrace tailWord_5885850 prefixEnd_5885850 3022270110265901818506475 := by
  unfold tailWord_5885850
  simp only [CollatzResearch.WordTrace]
  refine ⟨53668646431644536998801751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143116390484385431996804669 53668646431644536998801751)
  ·
    refine ⟨80502969647466805498202627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53668646431644536998801751 80502969647466805498202627)
    ·
      refine ⟨120754454471200208247303941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80502969647466805498202627 120754454471200208247303941)
      ·
        refine ⟨22641460213350039046369489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120754454471200208247303941 22641460213350039046369489)
        ·
          refine ⟨16981095160012529284777117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22641460213350039046369489 16981095160012529284777117)
          ·
            refine ⟨6367910685004698481791419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16981095160012529284777117 6367910685004698481791419)
            ·
              refine ⟨9551866027507047722687129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6367910685004698481791419 9551866027507047722687129)
              ·
                refine ⟨7163899520630285792015347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9551866027507047722687129 7163899520630285792015347)
                ·
                  refine ⟨10745849280945428688023021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7163899520630285792015347 10745849280945428688023021)
                  ·
                    refine ⟨4029693480354535758008633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10745849280945428688023021 4029693480354535758008633)
                    ·
                      refine ⟨3022270110265901818506475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029693480354535758008633 3022270110265901818506475)
                      ·
                        rfl

theorem cell23_5885850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_5885850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885850 prefixEnd_5885850 := by exact prefixLift 5885850
  have htrace : WordTrace (prefixWord ++ tailWord_5885850) baseStart_5885850 baseEnd_5885850 := by
    simpa [prefixWord, tailWord_5885850, baseEnd_5885850] using wordTrace_append hprefix tailTrace_5885850
  have hstable : (prefixWord ++ tailWord_5885850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885850).length < 2 ^ (prefixWord ++ tailWord_5885850).sum := by decide
  have hdescent : baseEnd_5885850 < baseStart_5885850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885863 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_5885863 : Nat := 118140960795 + 5885863 * 2 ^ 59
def prefixEnd_5885863 : Nat := 4983230072969 + 3 ^ 40 * 5885863 * 2
def baseEnd_5885863 : Nat := 3022276785514410267643915

theorem tailTrace_5885863 : CollatzResearch.WordTrace tailWord_5885863 prefixEnd_5885863 3022276785514410267643915 := by
  unfold tailWord_5885863
  simp only [CollatzResearch.WordTrace]
  refine ⟨214675059875531051215430243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143116706583687367476953495 214675059875531051215430243)
  ·
    refine ⟨322012589813296576823145365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214675059875531051215430243 322012589813296576823145365)
    ·
      refine ⟨15094340147498277038584939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 322012589813296576823145365 15094340147498277038584939)
      ·
        refine ⟨22641510221247415557877409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15094340147498277038584939 22641510221247415557877409)
        ·
          refine ⟨16981132665935561668408057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22641510221247415557877409 16981132665935561668408057)
          ·
            refine ⟨12735849499451671251306043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16981132665935561668408057 12735849499451671251306043)
            ·
              refine ⟨19103774249177506876959065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12735849499451671251306043 19103774249177506876959065)
              ·
                refine ⟨14327830686883130157719299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19103774249177506876959065 14327830686883130157719299)
                ·
                  refine ⟨21491746030324695236578949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14327830686883130157719299 21491746030324695236578949)
                  ·
                    refine ⟨4029702380685880356858553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21491746030324695236578949 4029702380685880356858553)
                    ·
                      refine ⟨3022276785514410267643915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029702380685880356858553 3022276785514410267643915)
                      ·
                        rfl

theorem cell23_5885863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_5885863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885863 prefixEnd_5885863 := by exact prefixLift 5885863
  have htrace : WordTrace (prefixWord ++ tailWord_5885863) baseStart_5885863 baseEnd_5885863 := by
    simpa [prefixWord, tailWord_5885863, baseEnd_5885863] using wordTrace_append hprefix tailTrace_5885863
  have hstable : (prefixWord ++ tailWord_5885863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885863).length < 2 ^ (prefixWord ++ tailWord_5885863).sum := by decide
  have hdescent : baseEnd_5885863 < baseStart_5885863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885879 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 3]
def baseStart_5885879 : Nat := 118140960795 + 5885879 * 2 ^ 59
def prefixEnd_5885879 : Nat := 4983230072969 + 3 ^ 40 * 5885879 * 2
def baseEnd_5885879 : Nat := 3022285001204882205043841

theorem tailTrace_5885879 : CollatzResearch.WordTrace tailWord_5885879 prefixEnd_5885879 3022285001204882205043841 := by
  unfold tailWord_5885879
  simp only [CollatzResearch.WordTrace]
  refine ⟨214675643443473085948012691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143117095628982057298675127 214675643443473085948012691)
  ·
    refine ⟨322013465165209628922019037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214675643443473085948012691 322013465165209628922019037)
    ·
      refine ⟨120755049436953610845757139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322013465165209628922019037 120755049436953610845757139)
      ·
        refine ⟨181132574155430416268635709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120755049436953610845757139 181132574155430416268635709)
        ·
          refine ⟨67924715308286406100738391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181132574155430416268635709 67924715308286406100738391)
          ·
            refine ⟨101887072962429609151107587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67924715308286406100738391 101887072962429609151107587)
            ·
              refine ⟨152830609443644413726661381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101887072962429609151107587 152830609443644413726661381)
              ·
                refine ⟨28655739270683327573749009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152830609443644413726661381 28655739270683327573749009)
                ·
                  refine ⟨21491804453012495680311757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28655739270683327573749009 21491804453012495680311757)
                  ·
                    refine ⟨8059426669879685880116909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21491804453012495680311757 8059426669879685880116909)
                    ·
                      refine ⟨3022285001204882205043841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8059426669879685880116909 3022285001204882205043841)
                      ·
                        rfl

theorem cell23_5885879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_5885879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885879 prefixEnd_5885879 := by exact prefixLift 5885879
  have htrace : WordTrace (prefixWord ++ tailWord_5885879) baseStart_5885879 baseEnd_5885879 := by
    simpa [prefixWord, tailWord_5885879, baseEnd_5885879] using wordTrace_append hprefix tailTrace_5885879
  have hstable : (prefixWord ++ tailWord_5885879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885879).length < 2 ^ (prefixWord ++ tailWord_5885879).sum := by decide
  have hdescent : baseEnd_5885879 < baseStart_5885879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885896 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_5885896 : Nat := 118140960795 + 5885896 * 2 ^ 59
def prefixEnd_5885896 : Nat := 4983230072969 + 3 ^ 40 * 5885896 * 2
def baseEnd_5885896 : Nat := 3022293730376008638531263

theorem tailTrace_5885896 : CollatzResearch.WordTrace tailWord_5885896 prefixEnd_5885896 3022293730376008638531263 := by
  unfold tailWord_5885896
  simp only [CollatzResearch.WordTrace]
  refine ⟨107338131742205748925690771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143117508989607665234254361 107338131742205748925690771)
  ·
    refine ⟨161007197613308623388536157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107338131742205748925690771 161007197613308623388536157)
    ·
      refine ⟨60377699104990733770701059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161007197613308623388536157 60377699104990733770701059)
      ·
        refine ⟨90566548657486100656051589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60377699104990733770701059 90566548657486100656051589)
        ·
          refine ⟨16981227873278643873009673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90566548657486100656051589 16981227873278643873009673)
          ·
            refine ⟨12735920904958982904757255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16981227873278643873009673 12735920904958982904757255)
            ·
              refine ⟨19103881357438474357135883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12735920904958982904757255 19103881357438474357135883)
              ·
                refine ⟨28655822036157711535703825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19103881357438474357135883 28655822036157711535703825)
                ·
                  refine ⟨21491866527118283651777869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28655822036157711535703825 21491866527118283651777869)
                  ·
                    refine ⟨8059449947669356369416701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21491866527118283651777869 8059449947669356369416701)
                    ·
                      refine ⟨3022293730376008638531263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8059449947669356369416701 3022293730376008638531263)
                      ·
                        rfl

theorem cell23_5885896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_5885896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885896 prefixEnd_5885896 := by exact prefixLift 5885896
  have htrace : WordTrace (prefixWord ++ tailWord_5885896) baseStart_5885896 baseEnd_5885896 := by
    simpa [prefixWord, tailWord_5885896, baseEnd_5885896] using wordTrace_append hprefix tailTrace_5885896
  have hstable : (prefixWord ++ tailWord_5885896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885896).length < 2 ^ (prefixWord ++ tailWord_5885896).sum := by decide
  have hdescent : baseEnd_5885896 < baseStart_5885896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885936 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 2, 4, 2]
def baseStart_5885936 : Nat := 118140960795 + 5885936 * 2 ^ 59
def prefixEnd_5885936 : Nat := 4983230072969 + 3 ^ 40 * 5885936 * 2
def baseEnd_5885936 : Nat := 3022314269602188482031079

theorem tailTrace_5885936 : CollatzResearch.WordTrace tailWord_5885936 prefixEnd_5885936 3022314269602188482031079 := by
  unfold tailWord_5885936
  simp only [CollatzResearch.WordTrace]
  refine ⟨107338861202133292341418831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143118481602844389788558441 107338861202133292341418831)
  ·
    refine ⟨161008291803199938512128247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107338861202133292341418831 161008291803199938512128247)
    ·
      refine ⟨241512437704799907768192371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161008291803199938512128247 241512437704799907768192371)
      ·
        refine ⟨362268656557199861652288557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241512437704799907768192371 362268656557199861652288557)
        ·
          refine ⟨135850746208949948119608209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362268656557199861652288557 135850746208949948119608209)
          ·
            refine ⟨101888059656712461089706157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135850746208949948119608209 101888059656712461089706157)
            ·
              refine ⟨38208022371267172908639809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101888059656712461089706157 38208022371267172908639809)
              ·
                refine ⟨28656016778450379681479857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38208022371267172908639809 28656016778450379681479857)
                ·
                  refine ⟨21492012583837784761109893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28656016778450379681479857 21492012583837784761109893)
                  ·
                    refine ⟨4029752359469584642708105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21492012583837784761109893 4029752359469584642708105)
                    ·
                      refine ⟨3022314269602188482031079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029752359469584642708105 3022314269602188482031079)
                      ·
                        rfl

theorem cell23_5885936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 4, 2].length) (baseStart_5885936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885936 prefixEnd_5885936 := by exact prefixLift 5885936
  have htrace : WordTrace (prefixWord ++ tailWord_5885936) baseStart_5885936 baseEnd_5885936 := by
    simpa [prefixWord, tailWord_5885936, baseEnd_5885936] using wordTrace_append hprefix tailTrace_5885936
  have hstable : (prefixWord ++ tailWord_5885936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885936).length < 2 ^ (prefixWord ++ tailWord_5885936).sum := by decide
  have hdescent : baseEnd_5885936 < baseStart_5885936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885980 : List Nat := [2, 2, 3, 1, 3, 1, 3, 3, 1, 4]
def baseStart_5885980 : Nat := 118140960795 + 5885980 * 2 ^ 59
def prefixEnd_5885980 : Nat := 4983230072969 + 3 ^ 40 * 5885980 * 2
def baseEnd_5885980 : Nat := 1007445620916995436626959

theorem tailTrace_5885980 : CollatzResearch.WordTrace tailWord_5885980 prefixEnd_5885980 1007445620916995436626959 := by
  unfold tailWord_5885980
  simp only [CollatzResearch.WordTrace]
  refine ⟨107339663608053590098719697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143119551477404786798292929 107339663608053590098719697)
  ·
    refine ⟨80504747706040192574039773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107339663608053590098719697 80504747706040192574039773)
    ·
      refine ⟨30189280389765072215264915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80504747706040192574039773 30189280389765072215264915)
      ·
        refine ⟨45283920584647608322897373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30189280389765072215264915 45283920584647608322897373)
        ·
          refine ⟨16981470219242853121086515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45283920584647608322897373 16981470219242853121086515)
          ·
            refine ⟨25472205328864279681629773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16981470219242853121086515 25472205328864279681629773)
            ·
              refine ⟨9552076998324104880611165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25472205328864279681629773 9552076998324104880611165)
              ·
                refine ⟨3582028874371539330229187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9552076998324104880611165 3582028874371539330229187)
                ·
                  refine ⟨5373043311557308995343781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582028874371539330229187 5373043311557308995343781)
                  ·
                    refine ⟨1007445620916995436626959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5373043311557308995343781 1007445620916995436626959)
                    ·
                      rfl

theorem cell23_5885980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_5885980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885980 prefixEnd_5885980 := by exact prefixLift 5885980
  have htrace : WordTrace (prefixWord ++ tailWord_5885980) baseStart_5885980 baseEnd_5885980 := by
    simpa [prefixWord, tailWord_5885980, baseEnd_5885980] using wordTrace_append hprefix tailTrace_5885980
  have hstable : (prefixWord ++ tailWord_5885980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885980).length < 2 ^ (prefixWord ++ tailWord_5885980).sum := by decide
  have hdescent : baseEnd_5885980 < baseStart_5885980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885996 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 3, 5, 2]
def baseStart_5885996 : Nat := 118140960795 + 5885996 * 2 ^ 59
def prefixEnd_5885996 : Nat := 4983230072969 + 3 ^ 40 * 5885996 * 2
def baseEnd_5885996 : Nat := 3022345078441458247280803

theorem tailTrace_5885996 : CollatzResearch.WordTrace tailWord_5885996 prefixEnd_5885996 3022345078441458247280803 := by
  unfold tailWord_5885996
  simp only [CollatzResearch.WordTrace]
  refine ⟨107339955392024607465010921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143119940522699476620014561 107339955392024607465010921)
  ·
    refine ⟨80504966544018455598758191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107339955392024607465010921 80504966544018455598758191)
    ·
      refine ⟨120757449816027683398137287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80504966544018455598758191 120757449816027683398137287)
      ·
        refine ⟨181136174724041525097205931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120757449816027683398137287 181136174724041525097205931)
        ·
          refine ⟨271704262086062287645808897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181136174724041525097205931 271704262086062287645808897)
          ·
            refine ⟨203778196564546715734356673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271704262086062287645808897 203778196564546715734356673)
            ·
              refine ⟨152833647423410036800767505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203778196564546715734356673 152833647423410036800767505)
              ·
                refine ⟨114625235567557527600575629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152833647423410036800767505 114625235567557527600575629)
                ·
                  refine ⟨42984463337834072850215861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114625235567557527600575629 42984463337834072850215861)
                  ·
                    refine ⟨4029793437921944329707737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42984463337834072850215861 4029793437921944329707737)
                    ·
                      refine ⟨3022345078441458247280803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029793437921944329707737 3022345078441458247280803)
                      ·
                        rfl

theorem cell23_5885996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 5, 2].length) (baseStart_5885996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885996 prefixEnd_5885996 := by exact prefixLift 5885996
  have htrace : WordTrace (prefixWord ++ tailWord_5885996) baseStart_5885996 baseEnd_5885996 := by
    simpa [prefixWord, tailWord_5885996, baseEnd_5885996] using wordTrace_append hprefix tailTrace_5885996
  have hstable : (prefixWord ++ tailWord_5885996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885996).length < 2 ^ (prefixWord ++ tailWord_5885996).sum := by decide
  have hdescent : baseEnd_5885996 < baseStart_5885996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886003 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 3, 1, 3]
def baseStart_5886003 : Nat := 118140960795 + 5886003 * 2 ^ 59
def prefixEnd_5886003 : Nat := 4983230072969 + 3 ^ 40 * 5886003 * 2
def baseEnd_5886003 : Nat := 3022348672806039719893271

theorem tailTrace_5886003 : CollatzResearch.WordTrace tailWord_5886003 prefixEnd_5886003 3022348672806039719893271 := by
  unfold tailWord_5886003
  simp only [CollatzResearch.WordTrace]
  refine ⟨214680166095023855125526663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143120110730015903417017775 214680166095023855125526663)
  ·
    refine ⟨322020249142535782688289995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214680166095023855125526663 322020249142535782688289995)
    ·
      refine ⟨483030373713803674032434993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322020249142535782688289995 483030373713803674032434993)
      ·
        refine ⟨362272780285352755524326245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483030373713803674032434993 362272780285352755524326245)
        ·
          refine ⟨67926146303503641660811171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362272780285352755524326245 67926146303503641660811171)
          ·
            refine ⟨101889219455255462491216757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67926146303503641660811171 101889219455255462491216757)
            ·
              refine ⟨9552114323930199608551571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101889219455255462491216757 9552114323930199608551571)
              ·
                refine ⟨14328171485895299412827357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9552114323930199608551571 14328171485895299412827357)
                ·
                  refine ⟨5373064307210737279810259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14328171485895299412827357 5373064307210737279810259)
                  ·
                    refine ⟨8059596460816105919715389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5373064307210737279810259 8059596460816105919715389)
                    ·
                      refine ⟨3022348672806039719893271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8059596460816105919715389 3022348672806039719893271)
                      ·
                        rfl

theorem cell23_5886003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 1, 3].length) (baseStart_5886003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886003 prefixEnd_5886003 := by exact prefixLift 5886003
  have htrace : WordTrace (prefixWord ++ tailWord_5886003) baseStart_5886003 baseEnd_5886003 := by
    simpa [prefixWord, tailWord_5886003, baseEnd_5886003] using wordTrace_append hprefix tailTrace_5886003
  have hstable : (prefixWord ++ tailWord_5886003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886003).length < 2 ^ (prefixWord ++ tailWord_5886003).sum := by decide
  have hdescent : baseEnd_5886003 < baseStart_5886003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886013 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 4, 3, 2]
def baseStart_5886013 : Nat := 118140960795 + 5886013 * 2 ^ 59
def prefixEnd_5886013 : Nat := 4983230072969 + 3 ^ 40 * 5886013 * 2
def baseEnd_5886013 : Nat := 3022353807612584680768225

theorem tailTrace_5886013 : CollatzResearch.WordTrace tailWord_5886013 prefixEnd_5886013 3022353807612584680768225 := by
  unfold tailWord_5886013
  simp only [CollatzResearch.WordTrace]
  refine ⟨214680530824987626833390693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143120353883325084555593795 214680530824987626833390693)
  ·
    refine ⟨40252599529685180031260755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214680530824987626833390693 40252599529685180031260755)
    ·
      refine ⟨60378899294527770046891133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40252599529685180031260755 60378899294527770046891133)
      ·
        refine ⟨22642087235447913767584175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60378899294527770046891133 22642087235447913767584175)
        ·
          refine ⟨33963130853171870651376263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22642087235447913767584175 33963130853171870651376263)
          ·
            refine ⟨50944696279757805977064395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33963130853171870651376263 50944696279757805977064395)
            ·
              refine ⟨76417044419636708965596593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50944696279757805977064395 76417044419636708965596593)
              ·
                refine ⟨57312783314727531724197445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76417044419636708965596593 57312783314727531724197445)
                ·
                  refine ⟨10746146871511412198287021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57312783314727531724197445 10746146871511412198287021)
                  ·
                    refine ⟨4029805076816779574357633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10746146871511412198287021 4029805076816779574357633)
                    ·
                      refine ⟨3022353807612584680768225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029805076816779574357633 3022353807612584680768225)
                      ·
                        rfl

theorem cell23_5886013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_5886013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886013 prefixEnd_5886013 := by exact prefixLift 5886013
  have htrace : WordTrace (prefixWord ++ tailWord_5886013) baseStart_5886013 baseEnd_5886013 := by
    simpa [prefixWord, tailWord_5886013, baseEnd_5886013] using wordTrace_append hprefix tailTrace_5886013
  have hstable : (prefixWord ++ tailWord_5886013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886013).length < 2 ^ (prefixWord ++ tailWord_5886013).sum := by decide
  have hdescent : baseEnd_5886013 < baseStart_5886013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886030 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2]
def baseStart_5886030 : Nat := 118140960795 + 5886030 * 2 ^ 59
def prefixEnd_5886030 : Nat := 4983230072969 + 3 ^ 40 * 5886030 * 2
def baseEnd_5886030 : Nat := 3022362536783711114255647

theorem tailTrace_5886030 : CollatzResearch.WordTrace tailWord_5886030 prefixEnd_5886030 3022362536783711114255647 := by
  unfold tailWord_5886030
  simp only [CollatzResearch.WordTrace]
  refine ⟨26835143858240754842094943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143120767243950692491173029 26835143858240754842094943)
  ·
    refine ⟨40252715787361132263142415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26835143858240754842094943 40252715787361132263142415)
    ·
      refine ⟨60379073681041698394713623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40252715787361132263142415 60379073681041698394713623)
      ·
        refine ⟨90568610521562547592070435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60379073681041698394713623 90568610521562547592070435)
        ·
          refine ⟨135852915782343821388105653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90568610521562547592070435 135852915782343821388105653)
          ·
            refine ⟨12736210854594733255134905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135852915782343821388105653 12736210854594733255134905)
            ·
              refine ⟨9552158140946049941351179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12736210854594733255134905 9552158140946049941351179)
              ·
                refine ⟨14328237211419074912026769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9552158140946049941351179 14328237211419074912026769)
                ·
                  refine ⟨10746177908564306184020077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14328237211419074912026769 10746177908564306184020077)
                  ·
                    refine ⟨4029816715711614819007529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10746177908564306184020077 4029816715711614819007529)
                    ·
                      refine ⟨3022362536783711114255647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029816715711614819007529 3022362536783711114255647)
                      ·
                        rfl

theorem cell23_5886030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_5886030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886030 prefixEnd_5886030 := by exact prefixLift 5886030
  have htrace : WordTrace (prefixWord ++ tailWord_5886030) baseStart_5886030 baseEnd_5886030 := by
    simpa [prefixWord, tailWord_5886030, baseEnd_5886030] using wordTrace_append hprefix tailTrace_5886030
  have hstable : (prefixWord ++ tailWord_5886030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886030).length < 2 ^ (prefixWord ++ tailWord_5886030).sum := by decide
  have hdescent : baseEnd_5886030 < baseStart_5886030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886053 : List Nat := [1, 3, 1, 3, 2, 2, 1, 4, 2, 4]
def baseStart_5886053 : Nat := 118140960795 + 5886053 * 2 ^ 59
def prefixEnd_5886053 : Nat := 4983230072969 + 3 ^ 40 * 5886053 * 2
def baseEnd_5886053 : Nat := 1007458115612921508089347

theorem tailTrace_5886053 : CollatzResearch.WordTrace tailWord_5886053 prefixEnd_5886053 1007458115612921508089347 := by
  unfold tailWord_5886053
  simp only [CollatzResearch.WordTrace]
  refine ⟨214681989744842713664846813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143121326496561809109897875 214681989744842713664846813)
  ·
    refine ⟨80505746154316017624317555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214681989744842713664846813 80505746154316017624317555)
    ·
      refine ⟨120758619231474026436476333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80505746154316017624317555 120758619231474026436476333)
      ·
        refine ⟨45284482211802759913678625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120758619231474026436476333 45284482211802759913678625)
        ·
          refine ⟨33963361658852069935258969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45284482211802759913678625 33963361658852069935258969)
          ·
            refine ⟨25472521244139052451444227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33963361658852069935258969 25472521244139052451444227)
            ·
              refine ⟨38208781866208578677166341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25472521244139052451444227 38208781866208578677166341)
              ·
                refine ⟨7164146599914108501968689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38208781866208578677166341 7164146599914108501968689)
                ·
                  refine ⟨5373109949935581376476517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7164146599914108501968689 5373109949935581376476517)
                  ·
                    refine ⟨1007458115612921508089347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5373109949935581376476517 1007458115612921508089347)
                    ·
                      rfl

theorem cell23_5886053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_5886053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886053 prefixEnd_5886053 := by exact prefixLift 5886053
  have htrace : WordTrace (prefixWord ++ tailWord_5886053) baseStart_5886053 baseEnd_5886053 := by
    simpa [prefixWord, tailWord_5886053, baseEnd_5886053] using wordTrace_append hprefix tailTrace_5886053
  have hstable : (prefixWord ++ tailWord_5886053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886053).length < 2 ^ (prefixWord ++ tailWord_5886053).sum := by decide
  have hdescent : baseEnd_5886053 < baseStart_5886053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886066 : List Nat := [3, 2, 1, 2, 2, 2, 3, 8]
def baseStart_5886066 : Nat := 118140960795 + 5886066 * 2 ^ 59
def prefixEnd_5886066 : Nat := 4983230072969 + 3 ^ 40 * 5886066 * 2
def baseEnd_5886066 : Nat := 111940037855084184200203

theorem tailTrace_5886066 : CollatzResearch.WordTrace tailWord_5886066 prefixEnd_5886066 111940037855084184200203 := by
  unfold tailWord_5886066
  simp only [CollatzResearch.WordTrace]
  refine ⟨53670615973448904221267513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143121642595863744590046701 53670615973448904221267513)
  ·
    refine ⟨40252961980086678165950635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53670615973448904221267513 40252961980086678165950635)
    ·
      refine ⟨60379442970130017248925953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40252961980086678165950635 60379442970130017248925953)
      ·
        refine ⟨45284582227597512936694465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60379442970130017248925953 45284582227597512936694465)
        ·
          refine ⟨33963436670698134702520849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45284582227597512936694465 33963436670698134702520849)
          ·
            refine ⟨25472577503023601026890637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33963436670698134702520849 25472577503023601026890637)
            ·
              refine ⟨9552216563633850385083989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25472577503023601026890637 9552216563633850385083989)
              ·
                refine ⟨111940037855084184200203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9552216563633850385083989 111940037855084184200203)
                ·
                  rfl

theorem cell23_5886066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 8].length) (baseStart_5886066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886066 prefixEnd_5886066 := by exact prefixLift 5886066
  have htrace : WordTrace (prefixWord ++ tailWord_5886066) baseStart_5886066 baseEnd_5886066 := by
    simpa [prefixWord, tailWord_5886066, baseEnd_5886066] using wordTrace_append hprefix tailTrace_5886066
  have hstable : (prefixWord ++ tailWord_5886066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886066).length < 2 ^ (prefixWord ++ tailWord_5886066).sum := by decide
  have hdescent : baseEnd_5886066 < baseStart_5886066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886070 : List Nat := [5, 1, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_5886070 : Nat := 118140960795 + 5886070 * 2 ^ 59
def prefixEnd_5886070 : Nat := 4983230072969 + 3 ^ 40 * 5886070 * 2
def baseEnd_5886070 : Nat := 1007461025336630319251821

theorem tailTrace_5886070 : CollatzResearch.WordTrace tailWord_5886070 prefixEnd_5886070 1007461025336630319251821 := by
  unfold tailWord_5886070
  simp only [CollatzResearch.WordTrace]
  refine ⟨13417663111611320348013479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143121739857187417045477109 13417663111611320348013479)
  ·
    refine ⟨20126494667416980522020219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13417663111611320348013479 20126494667416980522020219)
    ·
      refine ⟨30189742001125470783030329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20126494667416980522020219 30189742001125470783030329)
      ·
        refine ⟨22642306500844103087272747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30189742001125470783030329 22642306500844103087272747)
        ·
          refine ⟨33963459751266154630909121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22642306500844103087272747 33963459751266154630909121)
          ·
            refine ⟨25472594813449615973181841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33963459751266154630909121 25472594813449615973181841)
            ·
              refine ⟨19104446110087211979886381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25472594813449615973181841 19104446110087211979886381)
              ·
                refine ⟨7164167291282704492457393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19104446110087211979886381 7164167291282704492457393)
                ·
                  refine ⟨5373125468462028369343045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7164167291282704492457393 5373125468462028369343045)
                  ·
                    refine ⟨1007461025336630319251821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5373125468462028369343045 1007461025336630319251821)
                    ·
                      rfl

theorem cell23_5886070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_5886070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886070 prefixEnd_5886070 := by exact prefixLift 5886070
  have htrace : WordTrace (prefixWord ++ tailWord_5886070) baseStart_5886070 baseEnd_5886070 := by
    simpa [prefixWord, tailWord_5886070, baseEnd_5886070] using wordTrace_append hprefix tailTrace_5886070
  have hstable : (prefixWord ++ tailWord_5886070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886070).length < 2 ^ (prefixWord ++ tailWord_5886070).sum := by decide
  have hdescent : baseEnd_5886070 < baseStart_5886070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886073 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 1, 2, 4]
def baseStart_5886073 : Nat := 118140960795 + 5886073 * 2 ^ 59
def prefixEnd_5886073 : Nat := 4983230072969 + 3 ^ 40 * 5886073 * 2
def baseEnd_5886073 : Nat := 3022384616451854446017949

theorem tailTrace_5886073 : CollatzResearch.WordTrace tailWord_5886073 prefixEnd_5886073 3022384616451854446017949 := by
  unfold tailWord_5886073
  simp only [CollatzResearch.WordTrace]
  refine ⟨214682719204770257080574873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143121812803180171387049915 214682719204770257080574873)
  ·
    refine ⟨161012039403577692810431155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214682719204770257080574873 161012039403577692810431155)
    ·
      refine ⟨241518059105366539215646733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161012039403577692810431155 241518059105366539215646733)
      ·
        refine ⟨90569272164512452205867525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241518059105366539215646733 90569272164512452205867525)
        ·
          refine ⟨16981738530846084788600161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90569272164512452205867525 16981738530846084788600161)
          ·
            refine ⟨12736303898134563591450121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16981738530846084788600161 12736303898134563591450121)
            ·
              refine ⟨9552227923600922693587591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12736303898134563591450121 9552227923600922693587591)
              ·
                refine ⟨14328341885401384040381387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9552227923600922693587591 14328341885401384040381387)
                ·
                  refine ⟨21492512828102076060572081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14328341885401384040381387 21492512828102076060572081)
                  ·
                    refine ⟨16119384621076557045429061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21492512828102076060572081 16119384621076557045429061)
                    ·
                      refine ⟨3022384616451854446017949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16119384621076557045429061 3022384616451854446017949)
                      ·
                        rfl

theorem cell23_5886073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_5886073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886073 prefixEnd_5886073 := by exact prefixLift 5886073
  have htrace : WordTrace (prefixWord ++ tailWord_5886073) baseStart_5886073 baseEnd_5886073 := by
    simpa [prefixWord, tailWord_5886073, baseEnd_5886073] using wordTrace_append hprefix tailTrace_5886073
  have hstable : (prefixWord ++ tailWord_5886073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886073).length < 2 ^ (prefixWord ++ tailWord_5886073).sum := by decide
  have hdescent : baseEnd_5886073 < baseStart_5886073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886094 : List Nat := [4, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4]
def baseStart_5886094 : Nat := 118140960795 + 5886094 * 2 ^ 59
def prefixEnd_5886094 : Nat := 4983230072969 + 3 ^ 40 * 5886094 * 2
def baseEnd_5886094 : Nat := 3022395399545598863855353

theorem tailTrace_5886094 : CollatzResearch.WordTrace tailWord_5886094 prefixEnd_5886094 3022395399545598863855353 := by
  unfold tailWord_5886094
  simp only [CollatzResearch.WordTrace]
  refine ⟨26835435642211772208386167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143122323425129451778059557 26835435642211772208386167)
  ·
    refine ⟨40253153463317658312579251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26835435642211772208386167 40253153463317658312579251)
    ·
      refine ⟨60379730194976487468868877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40253153463317658312579251 60379730194976487468868877)
      ·
        refine ⟨22642398823116182800825829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60379730194976487468868877 22642398823116182800825829)
        ·
          refine ⟨4245449779334284275154843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22642398823116182800825829 4245449779334284275154843)
          ·
            refine ⟨6368174669001426412732265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245449779334284275154843 6368174669001426412732265)
            ·
              refine ⟨4776131001751069809549199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6368174669001426412732265 4776131001751069809549199)
              ·
                refine ⟨7164196502626604714323799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4776131001751069809549199 7164196502626604714323799)
                ·
                  refine ⟨10746294753939907071485699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7164196502626604714323799 10746294753939907071485699)
                  ·
                    refine ⟨16119442130909860607228549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10746294753939907071485699 16119442130909860607228549)
                    ·
                      refine ⟨3022395399545598863855353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16119442130909860607228549 3022395399545598863855353)
                      ·
                        rfl

theorem cell23_5886094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_5886094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886094 prefixEnd_5886094 := by exact prefixLift 5886094
  have htrace : WordTrace (prefixWord ++ tailWord_5886094) baseStart_5886094 baseEnd_5886094 := by
    simpa [prefixWord, tailWord_5886094, baseEnd_5886094] using wordTrace_append hprefix tailTrace_5886094
  have hstable : (prefixWord ++ tailWord_5886094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886094).length < 2 ^ (prefixWord ++ tailWord_5886094).sum := by decide
  have hdescent : baseEnd_5886094 < baseStart_5886094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886136 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_5886136 : Nat := 118140960795 + 5886136 * 2 ^ 59
def prefixEnd_5886136 : Nat := 4983230072969 + 3 ^ 40 * 5886136 * 2
def baseEnd_5886136 : Nat := 3022416965733087699530159

theorem tailTrace_5886136 : CollatzResearch.WordTrace tailWord_5886136 prefixEnd_5886136 3022416965733087699530159 := by
  unfold tailWord_5886136
  simp only [CollatzResearch.WordTrace]
  refine ⟨107342508501771009420059131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143123344669028012560078841 107342508501771009420059131)
  ·
    refine ⟨161013762752656514130088697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107342508501771009420059131 161013762752656514130088697)
    ·
      refine ⟨120760322064492385597566523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161013762752656514130088697 120760322064492385597566523)
      ·
        refine ⟨181140483096738578396349785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120760322064492385597566523 181140483096738578396349785)
        ·
          refine ⟨135855362322553933797262339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181140483096738578396349785 135855362322553933797262339)
          ·
            refine ⟨203783043483830900695893509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135855362322553933797262339 203783043483830900695893509)
            ·
              refine ⟨38209320653218293880480033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203783043483830900695893509 38209320653218293880480033)
              ·
                refine ⟨28656990489913720410360025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38209320653218293880480033 28656990489913720410360025)
                ·
                  refine ⟨21492742867435290307770019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28656990489913720410360025 21492742867435290307770019)
                  ·
                    refine ⟨32239114301152935461655029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21492742867435290307770019 32239114301152935461655029)
                    ·
                      refine ⟨3022416965733087699530159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32239114301152935461655029 3022416965733087699530159)
                      ·
                        rfl

theorem cell23_5886136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_5886136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886136 prefixEnd_5886136 := by exact prefixLift 5886136
  have htrace : WordTrace (prefixWord ++ tailWord_5886136) baseStart_5886136 baseEnd_5886136 := by
    simpa [prefixWord, tailWord_5886136, baseEnd_5886136] using wordTrace_append hprefix tailTrace_5886136
  have hstable : (prefixWord ++ tailWord_5886136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886136).length < 2 ^ (prefixWord ++ tailWord_5886136).sum := by decide
  have hdescent : baseEnd_5886136 < baseStart_5886136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886184 : List Nat := [2, 1, 4, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_5886184 : Nat := 118140960795 + 5886184 * 2 ^ 59
def prefixEnd_5886184 : Nat := 4983230072969 + 3 ^ 40 * 5886184 * 2
def baseEnd_5886184 : Nat := 3022441612804503511729939

theorem tailTrace_5886184 : CollatzResearch.WordTrace tailWord_5886184 prefixEnd_5886184 3022441612804503511729939 := by
  unfold tailWord_5886184
  simp only [CollatzResearch.WordTrace]
  refine ⟨107343383853684061518932803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143124511804912082025243737 107343383853684061518932803)
  ·
    refine ⟨161015075780526092278399205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107343383853684061518932803 161015075780526092278399205)
    ·
      refine ⟨30190326708848642302199851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161015075780526092278399205 30190326708848642302199851)
      ·
        refine ⟨45285490063272963453299777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30190326708848642302199851 45285490063272963453299777)
        ·
          refine ⟨33964117547454722589974833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45285490063272963453299777 33964117547454722589974833)
          ·
            refine ⟨25473088160591041942481125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33964117547454722589974833 25473088160591041942481125)
            ·
              refine ⟨4776204030110820364215211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25473088160591041942481125 4776204030110820364215211)
              ·
                refine ⟨7164306045166230546322817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4776204030110820364215211 7164306045166230546322817)
                ·
                  refine ⟨5373229533874672909742113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7164306045166230546322817 5373229533874672909742113)
                  ·
                    refine ⟨4029922150406004682306585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5373229533874672909742113 4029922150406004682306585)
                    ·
                      refine ⟨3022441612804503511729939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029922150406004682306585 3022441612804503511729939)
                      ·
                        rfl

theorem cell23_5886184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_5886184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886184 prefixEnd_5886184 := by exact prefixLift 5886184
  have htrace : WordTrace (prefixWord ++ tailWord_5886184) baseStart_5886184 baseEnd_5886184 := by
    simpa [prefixWord, tailWord_5886184, baseEnd_5886184] using wordTrace_append hprefix tailTrace_5886184
  have hstable : (prefixWord ++ tailWord_5886184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886184).length < 2 ^ (prefixWord ++ tailWord_5886184).sum := by decide
  have hdescent : baseEnd_5886184 < baseStart_5886184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886223 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 3, 6, 2]
def baseStart_5886223 : Nat := 118140960795 + 5886223 * 2 ^ 59
def prefixEnd_5886223 : Nat := 4983230072969 + 3 ^ 40 * 5886223 * 2
def baseEnd_5886223 : Nat := 3022461638550028859142259

theorem tailTrace_5886223 : CollatzResearch.WordTrace tailWord_5886223 prefixEnd_5886223 3022461638550028859142259 := by
  unfold tailWord_5886223
  simp only [CollatzResearch.WordTrace]
  refine ⟨214688190154226832698535323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143125460102817888465690215 214688190154226832698535323)
  ·
    refine ⟨322032285231340249047802985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214688190154226832698535323 322032285231340249047802985)
    ·
      refine ⟨241524213923505186785852239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322032285231340249047802985 241524213923505186785852239)
      ·
        refine ⟨362286320885257780178778359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241524213923505186785852239 362286320885257780178778359)
        ·
          refine ⟨543429481327886670268167539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362286320885257780178778359 543429481327886670268167539)
          ·
            refine ⟨815144221991830005402251309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543429481327886670268167539 815144221991830005402251309)
            ·
              refine ⟨305679083246936252025844241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 815144221991830005402251309 305679083246936252025844241)
              ·
                refine ⟨229259312435202189019383181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305679083246936252025844241 229259312435202189019383181)
                ·
                  refine ⟨85972242163200820882268693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229259312435202189019383181 85972242163200820882268693)
                  ·
                    refine ⟨4029948851400038478856345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85972242163200820882268693 4029948851400038478856345)
                    ·
                      refine ⟨3022461638550028859142259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029948851400038478856345 3022461638550028859142259)
                      ·
                        rfl

theorem cell23_5886223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 6, 2].length) (baseStart_5886223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886223 prefixEnd_5886223 := by exact prefixLift 5886223
  have htrace : WordTrace (prefixWord ++ tailWord_5886223) baseStart_5886223 baseEnd_5886223 := by
    simpa [prefixWord, tailWord_5886223, baseEnd_5886223] using wordTrace_append hprefix tailTrace_5886223
  have hstable : (prefixWord ++ tailWord_5886223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886223).length < 2 ^ (prefixWord ++ tailWord_5886223).sum := by decide
  have hdescent : baseEnd_5886223 < baseStart_5886223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886240 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 1, 6, 2]
def baseStart_5886240 : Nat := 118140960795 + 5886240 * 2 ^ 59
def prefixEnd_5886240 : Nat := 4983230072969 + 3 ^ 40 * 5886240 * 2
def baseEnd_5886240 : Nat := 3022470367721155292629681

theorem tailTrace_5886240 : CollatzResearch.WordTrace tailWord_5886240 prefixEnd_5886240 3022470367721155292629681 := by
  unfold tailWord_5886240
  simp only [CollatzResearch.WordTrace]
  refine ⟨107344405097582622300952087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143125873463443496401269449 107344405097582622300952087)
  ·
    refine ⟨161016607646373933451428131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107344405097582622300952087 161016607646373933451428131)
    ·
      refine ⟨241524911469560900177142197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161016607646373933451428131 241524911469560900177142197)
      ·
        refine ⟨22642960450271334391607081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241524911469560900177142197 22642960450271334391607081)
        ·
          refine ⟨16982220337703500793705311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22642960450271334391607081 16982220337703500793705311)
          ·
            refine ⟨25473330506555251190557967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16982220337703500793705311 25473330506555251190557967)
            ·
              refine ⟨38209995759832876785836951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25473330506555251190557967 38209995759832876785836951)
              ·
                refine ⟨57314993639749315178755427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38209995759832876785836951 57314993639749315178755427)
                ·
                  refine ⟨85972490459623972768133141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57314993639749315178755427 85972490459623972768133141)
                  ·
                    refine ⟨4029960490294873723506241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85972490459623972768133141 4029960490294873723506241)
                    ·
                      refine ⟨3022470367721155292629681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029960490294873723506241 3022470367721155292629681)
                      ·
                        rfl

theorem cell23_5886240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_5886240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886240 prefixEnd_5886240 := by exact prefixLift 5886240
  have htrace : WordTrace (prefixWord ++ tailWord_5886240) baseStart_5886240 baseEnd_5886240 := by
    simpa [prefixWord, tailWord_5886240, baseEnd_5886240] using wordTrace_append hprefix tailTrace_5886240
  have hstable : (prefixWord ++ tailWord_5886240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886240).length < 2 ^ (prefixWord ++ tailWord_5886240).sum := by decide
  have hdescent : baseEnd_5886240 < baseStart_5886240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886243 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 3]
def baseStart_5886243 : Nat := 118140960795 + 5886243 * 2 ^ 59
def prefixEnd_5886243 : Nat := 4983230072969 + 3 ^ 40 * 5886243 * 2
def baseEnd_5886243 : Nat := 3022471908163118780892167

theorem tailTrace_5886243 : CollatzResearch.WordTrace tailWord_5886243 prefixEnd_5886243 3022471908163118780892167 := by
  unfold tailWord_5886243
  simp only [CollatzResearch.WordTrace]
  refine ⟨214688919614154376114263383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143125946409436250742842255 214688919614154376114263383)
  ·
    refine ⟨322033379421231564171395075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214688919614154376114263383 322033379421231564171395075)
    ·
      refine ⟨483050069131847346257092613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322033379421231564171395075 483050069131847346257092613)
      ·
        refine ⟨90571887962221377423204865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 483050069131847346257092613 90571887962221377423204865)
        ·
          refine ⟨67928915971666033067403649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90571887962221377423204865 67928915971666033067403649)
          ·
            refine ⟨50946686978749524800552737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67928915971666033067403649 50946686978749524800552737)
            ·
              refine ⟨38210015234062143600414553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50946686978749524800552737 38210015234062143600414553)
              ·
                refine ⟨28657511425546607700310915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38210015234062143600414553 28657511425546607700310915)
                ·
                  refine ⟨42986267138319911550466373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28657511425546607700310915 42986267138319911550466373)
                  ·
                    refine ⟨8059925088434983415712445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42986267138319911550466373 8059925088434983415712445)
                    ·
                      refine ⟨3022471908163118780892167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8059925088434983415712445 3022471908163118780892167)
                      ·
                        rfl

theorem cell23_5886243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_5886243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886243 prefixEnd_5886243 := by exact prefixLift 5886243
  have htrace : WordTrace (prefixWord ++ tailWord_5886243) baseStart_5886243 baseEnd_5886243 := by
    simpa [prefixWord, tailWord_5886243, baseEnd_5886243] using wordTrace_append hprefix tailTrace_5886243
  have hstable : (prefixWord ++ tailWord_5886243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886243).length < 2 ^ (prefixWord ++ tailWord_5886243).sum := by decide
  have hdescent : baseEnd_5886243 < baseStart_5886243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886254 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_5886254 : Nat := 118140960795 + 5886254 * 2 ^ 59
def prefixEnd_5886254 : Nat := 4983230072969 + 3 ^ 40 * 5886254 * 2
def baseEnd_5886254 : Nat := 1007492518816772745951539

theorem tailTrace_5886254 : CollatzResearch.WordTrace tailWord_5886254 prefixEnd_5886254 1007492518816772745951539 := by
  unfold tailWord_5886254
  simp only [CollatzResearch.WordTrace]
  refine ⟨26836165102139315624114227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143126213878076349995275877 26836165102139315624114227)
  ·
    refine ⟨40254247653208973436171341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26836165102139315624114227 40254247653208973436171341)
    ·
      refine ⟨15095342869953365038564253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40254247653208973436171341 15095342869953365038564253)
      ·
        refine ⟨5660753576232511889461595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15095342869953365038564253 5660753576232511889461595)
        ·
          refine ⟨8491130364348767834192393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5660753576232511889461595 8491130364348767834192393)
          ·
            refine ⟨6368347773261575875644295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8491130364348767834192393 6368347773261575875644295)
            ·
              refine ⟨9552521659892363813466443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368347773261575875644295 9552521659892363813466443)
              ·
                refine ⟨14328782489838545720199665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9552521659892363813466443 14328782489838545720199665)
                ·
                  refine ⟨10746586867378909290149749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14328782489838545720199665 10746586867378909290149749)
                  ·
                    refine ⟨1007492518816772745951539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10746586867378909290149749 1007492518816772745951539)
                    ·
                      rfl

theorem cell23_5886254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_5886254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886254 prefixEnd_5886254 := by exact prefixLift 5886254
  have htrace : WordTrace (prefixWord ++ tailWord_5886254) baseStart_5886254 baseEnd_5886254 := by
    simpa [prefixWord, tailWord_5886254, baseEnd_5886254] using wordTrace_append hprefix tailTrace_5886254
  have hstable : (prefixWord ++ tailWord_5886254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886254).length < 2 ^ (prefixWord ++ tailWord_5886254).sum := by decide
  have hdescent : baseEnd_5886254 < baseStart_5886254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886257 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 2, 1, 4]
def baseStart_5886257 : Nat := 118140960795 + 5886257 * 2 ^ 59
def prefixEnd_5886257 : Nat := 4983230072969 + 3 ^ 40 * 5886257 * 2
def baseEnd_5886257 : Nat := 3022479096892281726117103

theorem tailTrace_5886257 : CollatzResearch.WordTrace tailWord_5886257 prefixEnd_5886257 3022479096892281726117103 := by
  unfold tailWord_5886257
  simp only [CollatzResearch.WordTrace]
  refine ⟨214689430236103656505273025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143126286824069104336848683 214689430236103656505273025)
  ·
    refine ⟨161017072677077742378954769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214689430236103656505273025 161017072677077742378954769)
    ·
      refine ⟨120762804507808306784216077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161017072677077742378954769 120762804507808306784216077)
      ·
        refine ⟨45286051690428115044081029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120762804507808306784216077 45286051690428115044081029)
        ·
          refine ⟨8491134691955271570765193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45286051690428115044081029 8491134691955271570765193)
          ·
            refine ⟨6368351018966453678073895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8491134691955271570765193 6368351018966453678073895)
            ·
              refine ⟨9552526528449680517110843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368351018966453678073895 9552526528449680517110843)
              ·
                refine ⟨14328789792674520775666265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9552526528449680517110843 14328789792674520775666265)
                ·
                  refine ⟨10746592344505890581749699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14328789792674520775666265 10746592344505890581749699)
                  ·
                    refine ⟨16119888516758835872624549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10746592344505890581749699 16119888516758835872624549)
                    ·
                      refine ⟨3022479096892281726117103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16119888516758835872624549 3022479096892281726117103)
                      ·
                        rfl

theorem cell23_5886257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_5886257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886257 prefixEnd_5886257 := by exact prefixLift 5886257
  have htrace : WordTrace (prefixWord ++ tailWord_5886257) baseStart_5886257 baseEnd_5886257 := by
    simpa [prefixWord, tailWord_5886257, baseEnd_5886257] using wordTrace_append hprefix tailTrace_5886257
  have hstable : (prefixWord ++ tailWord_5886257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886257).length < 2 ^ (prefixWord ++ tailWord_5886257).sum := by decide
  have hdescent : baseEnd_5886257 < baseStart_5886257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886317 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_5886317 : Nat := 118140960795 + 5886317 * 2 ^ 59
def prefixEnd_5886317 : Nat := 4983230072969 + 3 ^ 40 * 5886317 * 2
def baseEnd_5886317 : Nat := 3022509905731551491366827

theorem tailTrace_5886317 : CollatzResearch.WordTrace tailWord_5886317 prefixEnd_5886317 3022509905731551491366827 := by
  unfold tailWord_5886317
  simp only [CollatzResearch.WordTrace]
  refine ⟨214691618615886286752457205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143127745743924191168304803 214691618615886286752457205)
  ·
    refine ⟨20127339245239339383042863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214691618615886286752457205 20127339245239339383042863)
    ·
      refine ⟨30191008867859009074564295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20127339245239339383042863 30191008867859009074564295)
      ·
        refine ⟨45286513301788513611846443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30191008867859009074564295 45286513301788513611846443)
        ·
          refine ⟨67929769952682770417769665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45286513301788513611846443 67929769952682770417769665)
          ·
            refine ⟨50947327464512077813327249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67929769952682770417769665 50947327464512077813327249)
            ·
              refine ⟨38210495598384058359995437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50947327464512077813327249 38210495598384058359995437)
              ·
                refine ⟨14328935849394021884998289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38210495598384058359995437 14328935849394021884998289)
                ·
                  refine ⟨10746701887045516413748717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14328935849394021884998289 10746701887045516413748717)
                  ·
                    refine ⟨4030013207642068655155769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10746701887045516413748717 4030013207642068655155769)
                    ·
                      refine ⟨3022509905731551491366827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030013207642068655155769 3022509905731551491366827)
                      ·
                        rfl

theorem cell23_5886317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_5886317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886317 prefixEnd_5886317 := by exact prefixLift 5886317
  have htrace : WordTrace (prefixWord ++ tailWord_5886317) baseStart_5886317 baseEnd_5886317 := by
    simpa [prefixWord, tailWord_5886317, baseEnd_5886317] using wordTrace_append hprefix tailTrace_5886317
  have hstable : (prefixWord ++ tailWord_5886317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886317).length < 2 ^ (prefixWord ++ tailWord_5886317).sum := by decide
  have hdescent : baseEnd_5886317 < baseStart_5886317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886340 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_5886340 : Nat := 118140960795 + 5886340 * 2 ^ 59
def prefixEnd_5886340 : Nat := 4983230072969 + 3 ^ 40 * 5886340 * 2
def baseEnd_5886340 : Nat := 1007507238595534967126407

theorem tailTrace_5886340 : CollatzResearch.WordTrace tailWord_5886340 prefixEnd_5886340 1007507238595534967126407 := by
  unfold tailWord_5886340
  simp only [CollatzResearch.WordTrace]
  refine ⟨107346228747401480840272237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143128304996535307787029649 107346228747401480840272237)
  ·
    refine ⟨40254835780275555315102089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107346228747401480840272237 40254835780275555315102089)
    ·
      refine ⟨30191126835206666486326567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40254835780275555315102089 30191126835206666486326567)
      ·
        refine ⟨45286690252809999729489851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30191126835206666486326567 45286690252809999729489851)
        ·
          refine ⟨67930035379214999594234777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45286690252809999729489851 67930035379214999594234777)
          ·
            refine ⟨50947526534411249695676083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67930035379214999594234777 50947526534411249695676083)
            ·
              refine ⟨76421289801616874543514125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50947526534411249695676083 76421289801616874543514125)
              ·
                refine ⟨28657983675606327953817797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76421289801616874543514125 28657983675606327953817797)
                ·
                  refine ⟨5373371939176186491340837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28657983675606327953817797 5373371939176186491340837)
                  ·
                    refine ⟨1007507238595534967126407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5373371939176186491340837 1007507238595534967126407)
                    ·
                      rfl

theorem cell23_5886340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_5886340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886340 prefixEnd_5886340 := by exact prefixLift 5886340
  have htrace : WordTrace (prefixWord ++ tailWord_5886340) baseStart_5886340 baseEnd_5886340 := by
    simpa [prefixWord, tailWord_5886340, baseEnd_5886340] using wordTrace_append hprefix tailTrace_5886340
  have hstable : (prefixWord ++ tailWord_5886340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886340).length < 2 ^ (prefixWord ++ tailWord_5886340).sum := by decide
  have hdescent : baseEnd_5886340 < baseStart_5886340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886343 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_5886343 : Nat := 118140960795 + 5886343 * 2 ^ 59
def prefixEnd_5886343 : Nat := 4983230072969 + 3 ^ 40 * 5886343 * 2
def baseEnd_5886343 : Nat := 3022523256228568389641707

theorem tailTrace_5886343 : CollatzResearch.WordTrace tailWord_5886343 prefixEnd_5886343 3022523256228568389641707 := by
  unfold tailWord_5886343
  simp only [CollatzResearch.WordTrace]
  refine ⟨214692566913792093192903683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143128377942528062128602455 214692566913792093192903683)
  ·
    refine ⟨322038850370688139789355525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214692566913792093192903683 322038850370688139789355525)
    ·
      refine ⟨60382284444504026210504161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 322038850370688139789355525 60382284444504026210504161)
      ·
        refine ⟨45286713333378019657878121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60382284444504026210504161 45286713333378019657878121)
        ·
          refine ⟨33965035000033514743408591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45286713333378019657878121 33965035000033514743408591)
          ·
            refine ⟨50947552500050272115112887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33965035000033514743408591 50947552500050272115112887)
            ·
              refine ⟨76421328750075408172669331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50947552500050272115112887 76421328750075408172669331)
              ·
                refine ⟨114631993125113112259003997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76421328750075408172669331 114631993125113112259003997)
                ·
                  refine ⟨42986997421917417097126499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114631993125113112259003997 42986997421917417097126499)
                  ·
                    refine ⟨64480496132876125645689749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42986997421917417097126499 64480496132876125645689749)
                    ·
                      refine ⟨3022523256228568389641707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64480496132876125645689749 3022523256228568389641707)
                      ·
                        rfl

theorem cell23_5886343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_5886343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886343 prefixEnd_5886343 := by exact prefixLift 5886343
  have htrace : WordTrace (prefixWord ++ tailWord_5886343) baseStart_5886343 baseEnd_5886343 := by
    simpa [prefixWord, tailWord_5886343, baseEnd_5886343] using wordTrace_append hprefix tailTrace_5886343
  have hstable : (prefixWord ++ tailWord_5886343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886343).length < 2 ^ (prefixWord ++ tailWord_5886343).sum := by decide
  have hdescent : baseEnd_5886343 < baseStart_5886343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886360 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_5886360 : Nat := 118140960795 + 5886360 * 2 ^ 59
def prefixEnd_5886360 : Nat := 4983230072969 + 3 ^ 40 * 5886360 * 2
def baseEnd_5886360 : Nat := 3022531985399694823129129

theorem tailTrace_5886360 : CollatzResearch.WordTrace tailWord_5886360 prefixEnd_5886360 3022531985399694823129129 := by
  unfold tailWord_5886360
  simp only [CollatzResearch.WordTrace]
  refine ⟨107346593477365252548136267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143128791303153670064181689 107346593477365252548136267)
  ·
    refine ⟨161019890216047878822204401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107346593477365252548136267 161019890216047878822204401)
    ·
      refine ⟨120764917662035909116653301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161019890216047878822204401 120764917662035909116653301)
      ·
        refine ⟨11321711030815866479686247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120764917662035909116653301 11321711030815866479686247)
        ·
          refine ⟨16982566546223799719529371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11321711030815866479686247 16982566546223799719529371)
          ·
            refine ⟨25473849819335699579294057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16982566546223799719529371 25473849819335699579294057)
            ·
              refine ⟨19105387364501774684470543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25473849819335699579294057 19105387364501774684470543)
              ·
                refine ⟨28658081046752662026705815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19105387364501774684470543 28658081046752662026705815)
                ·
                  refine ⟨42987121570128993040058723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28658081046752662026705815 42987121570128993040058723)
                  ·
                    refine ⟨64480682355193489560088085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42987121570128993040058723 64480682355193489560088085)
                    ·
                      refine ⟨3022531985399694823129129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64480682355193489560088085 3022531985399694823129129)
                      ·
                        rfl

theorem cell23_5886360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_5886360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886360 prefixEnd_5886360 := by exact prefixLift 5886360
  have htrace : WordTrace (prefixWord ++ tailWord_5886360) baseStart_5886360 baseEnd_5886360 := by
    simpa [prefixWord, tailWord_5886360, baseEnd_5886360] using wordTrace_append hprefix tailTrace_5886360
  have hstable : (prefixWord ++ tailWord_5886360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886360).length < 2 ^ (prefixWord ++ tailWord_5886360).sum := by decide
  have hdescent : baseEnd_5886360 < baseStart_5886360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886378 : List Nat := [3, 1, 6, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5886378 : Nat := 118140960795 + 5886378 * 2 ^ 59
def prefixEnd_5886378 : Nat := 4983230072969 + 3 ^ 40 * 5886378 * 2
def baseEnd_5886378 : Nat := 1007513742683825250901349

theorem tailTrace_5886378 : CollatzResearch.WordTrace tailWord_5886378 prefixEnd_5886378 1007513742683825250901349 := by
  unfold tailWord_5886378
  simp only [CollatzResearch.WordTrace]
  refine ⟨53673460867166323542606947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143129228979110196113618525 53673460867166323542606947)
  ·
    refine ⟨80510191300749485313910421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53673460867166323542606947 80510191300749485313910421)
    ·
      refine ⟨3773915217222632124089551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80510191300749485313910421 3773915217222632124089551)
      ·
        refine ⟨5660872825833948186134327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3773915217222632124089551 5660872825833948186134327)
        ·
          refine ⟨8491309238750922279201491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5660872825833948186134327 8491309238750922279201491)
          ·
            refine ⟨12736963858126383418802237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8491309238750922279201491 12736963858126383418802237)
            ·
              refine ⟨4776361446797393782050839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12736963858126383418802237 4776361446797393782050839)
              ·
                refine ⟨7164542170196090673076259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4776361446797393782050839 7164542170196090673076259)
                ·
                  refine ⟨10746813255294136009614389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7164542170196090673076259 10746813255294136009614389)
                  ·
                    refine ⟨1007513742683825250901349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10746813255294136009614389 1007513742683825250901349)
                    ·
                      rfl

theorem cell23_5886378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5886378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886378 prefixEnd_5886378 := by exact prefixLift 5886378
  have htrace : WordTrace (prefixWord ++ tailWord_5886378) baseStart_5886378 baseEnd_5886378 := by
    simpa [prefixWord, tailWord_5886378, baseEnd_5886378] using wordTrace_append hprefix tailTrace_5886378
  have hstable : (prefixWord ++ tailWord_5886378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886378).length < 2 ^ (prefixWord ++ tailWord_5886378).sum := by decide
  have hdescent : baseEnd_5886378 < baseStart_5886378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886381 : List Nat := [1, 5, 2, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_5886381 : Nat := 118140960795 + 5886381 * 2 ^ 59
def prefixEnd_5886381 : Nat := 4983230072969 + 3 ^ 40 * 5886381 * 2
def baseEnd_5886381 : Nat := 3022542768493439240966533

theorem tailTrace_5886381 : CollatzResearch.WordTrace tailWord_5886381 prefixEnd_5886381 3022542768493439240966533 := by
  unfold tailWord_5886381
  simp only [CollatzResearch.WordTrace]
  refine ⟨214693952887654425682786997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143129301925102950455191331 214693952887654425682786997)
  ·
    refine ⟨20127558083217602407761281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214693952887654425682786997 20127558083217602407761281)
    ·
      refine ⟨15095668562413201805820961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20127558083217602407761281 15095668562413201805820961)
      ·
        refine ⟨11321751421809901354365721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15095668562413201805820961 11321751421809901354365721)
        ·
          refine ⟨8491313566357426015774291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11321751421809901354365721 8491313566357426015774291)
          ·
            refine ⟨12736970349536139023661437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8491313566357426015774291 12736970349536139023661437)
            ·
              refine ⟨4776363881076052133873039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12736970349536139023661437 4776363881076052133873039)
              ·
                refine ⟨7164545821614078200809559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4776363881076052133873039 7164545821614078200809559)
                ·
                  refine ⟨10746818732421117301214339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7164545821614078200809559 10746818732421117301214339)
                  ·
                    refine ⟨16120228098631675951821509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10746818732421117301214339 16120228098631675951821509)
                    ·
                      refine ⟨3022542768493439240966533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16120228098631675951821509 3022542768493439240966533)
                      ·
                        rfl

theorem cell23_5886381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_5886381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886381 prefixEnd_5886381 := by exact prefixLift 5886381
  have htrace : WordTrace (prefixWord ++ tailWord_5886381) baseStart_5886381 baseEnd_5886381 := by
    simpa [prefixWord, tailWord_5886381, baseEnd_5886381] using wordTrace_append hprefix tailTrace_5886381
  have hstable : (prefixWord ++ tailWord_5886381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886381).length < 2 ^ (prefixWord ++ tailWord_5886381).sum := by decide
  have hdescent : baseEnd_5886381 < baseStart_5886381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886398 : List Nat := [4, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_5886398 : Nat := 118140960795 + 5886398 * 2 ^ 59
def prefixEnd_5886398 : Nat := 4983230072969 + 3 ^ 40 * 5886398 * 2
def baseEnd_5886398 : Nat := 3022551497664565674453955

theorem tailTrace_5886398 : CollatzResearch.WordTrace tailWord_5886398 prefixEnd_5886398 3022551497664565674453955 := by
  unfold tailWord_5886398
  simp only [CollatzResearch.WordTrace]
  refine ⟨26836821616074104698269481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143129715285728558390770565 26836821616074104698269481)
  ·
    refine ⟨20127616212055578523702111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26836821616074104698269481 20127616212055578523702111)
    ·
      refine ⟨30191424318083367785553167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20127616212055578523702111 30191424318083367785553167)
      ·
        refine ⟨45287136477125051678329751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30191424318083367785553167 45287136477125051678329751)
        ·
          refine ⟨67930704715687577517494627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45287136477125051678329751 67930704715687577517494627)
          ·
            refine ⟨101896057073531366276241941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67930704715687577517494627 101896057073531366276241941)
            ·
              refine ⟨4776377675321782794198841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101896057073531366276241941 4776377675321782794198841)
              ·
                refine ⟨3582283256491337095649131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4776377675321782794198841 3582283256491337095649131)
                ·
                  refine ⟨5373424884737005643473697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582283256491337095649131 5373424884737005643473697)
                  ·
                    refine ⟨4030068663552754232605273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5373424884737005643473697 4030068663552754232605273)
                    ·
                      refine ⟨3022551497664565674453955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030068663552754232605273 3022551497664565674453955)
                      ·
                        rfl

theorem cell23_5886398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_5886398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886398 prefixEnd_5886398 := by exact prefixLift 5886398
  have htrace : WordTrace (prefixWord ++ tailWord_5886398) baseStart_5886398 baseEnd_5886398 := by
    simpa [prefixWord, tailWord_5886398, baseEnd_5886398] using wordTrace_append hprefix tailTrace_5886398
  have hstable : (prefixWord ++ tailWord_5886398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886398).length < 2 ^ (prefixWord ++ tailWord_5886398).sum := by decide
  have hdescent : baseEnd_5886398 < baseStart_5886398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886404 : List Nat := [2, 3, 3, 2, 3, 1, 1, 8]
def baseStart_5886404 : Nat := 118140960795 + 5886404 * 2 ^ 59
def prefixEnd_5886404 : Nat := 4983230072969 + 3 ^ 40 * 5886404 * 2
def baseEnd_5886404 : Nat := 111946465872166394480701

theorem tailTrace_5886404 : CollatzResearch.WordTrace tailWord_5886404 prefixEnd_5886404 111946465872166394480701 := by
  unfold tailWord_5886404
  simp only [CollatzResearch.WordTrace]
  refine ⟨107347395883285550305437133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143129861177714067073916177 107347395883285550305437133)
  ·
    refine ⟨40255273456232081364538925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107347395883285550305437133 40255273456232081364538925)
    ·
      refine ⟨15095727546087030511702097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40255273456232081364538925 15095727546087030511702097)
      ·
        refine ⟨11321795659565272883776573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15095727546087030511702097 11321795659565272883776573)
        ·
          refine ⟨4245673372336977331416215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11321795659565272883776573 4245673372336977331416215)
          ·
            refine ⟨6368510058505465997124323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245673372336977331416215 6368510058505465997124323)
            ·
              refine ⟨9552765087758198995686485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368510058505465997124323 9552765087758198995686485)
              ·
                refine ⟨111946465872166394480701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9552765087758198995686485 111946465872166394480701)
                ·
                  rfl

theorem cell23_5886404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 8].length) (baseStart_5886404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886404 prefixEnd_5886404 := by exact prefixLift 5886404
  have htrace : WordTrace (prefixWord ++ tailWord_5886404) baseStart_5886404 baseEnd_5886404 := by
    simpa [prefixWord, tailWord_5886404, baseEnd_5886404] using wordTrace_append hprefix tailTrace_5886404
  have hstable : (prefixWord ++ tailWord_5886404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886404).length < 2 ^ (prefixWord ++ tailWord_5886404).sum := by decide
  have hdescent : baseEnd_5886404 < baseStart_5886404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886407 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 3, 3, 2]
def baseStart_5886407 : Nat := 118140960795 + 5886407 * 2 ^ 59
def prefixEnd_5886407 : Nat := 4983230072969 + 3 ^ 40 * 5886407 * 2
def baseEnd_5886407 : Nat := 3022556118990456139241413

theorem tailTrace_5886407 : CollatzResearch.WordTrace tailWord_5886407 prefixEnd_5886407 3022556118990456139241413 := by
  unfold tailWord_5886407
  simp only [CollatzResearch.WordTrace]
  refine ⟨214694901185560232123233475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143129934123706821415488983 214694901185560232123233475)
  ·
    refine ⟨322042351778340348184850213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214694901185560232123233475 322042351778340348184850213)
    ·
      refine ⟨60382940958438815284659415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 322042351778340348184850213 60382940958438815284659415)
      ·
        refine ⟨90574411437658222926989123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60382940958438815284659415 90574411437658222926989123)
        ·
          refine ⟨135861617156487334390483685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90574411437658222926989123 135861617156487334390483685)
          ·
            refine ⟨25474053216841375198215691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135861617156487334390483685 25474053216841375198215691)
            ·
              refine ⟨38211079825262062797323537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25474053216841375198215691 38211079825262062797323537)
              ·
                refine ⟨28658309868946547097992653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38211079825262062797323537 28658309868946547097992653)
                ·
                  refine ⟨10746866200854955161747245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28658309868946547097992653 10746866200854955161747245)
                  ·
                    refine ⟨4030074825320608185655217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10746866200854955161747245 4030074825320608185655217)
                    ·
                      refine ⟨3022556118990456139241413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030074825320608185655217 3022556118990456139241413)
                      ·
                        rfl

theorem cell23_5886407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_5886407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886407 prefixEnd_5886407 := by exact prefixLift 5886407
  have htrace : WordTrace (prefixWord ++ tailWord_5886407) baseStart_5886407 baseEnd_5886407 := by
    simpa [prefixWord, tailWord_5886407, baseEnd_5886407] using wordTrace_append hprefix tailTrace_5886407
  have hstable : (prefixWord ++ tailWord_5886407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886407).length < 2 ^ (prefixWord ++ tailWord_5886407).sum := by decide
  have hdescent : baseEnd_5886407 < baseStart_5886407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886443 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 9]
def baseStart_5886443 : Nat := 118140960795 + 5886443 * 2 ^ 59
def prefixEnd_5886443 : Nat := 4983230072969 + 3 ^ 40 * 5886443 * 2
def baseEnd_5886443 : Nat := 335841622699335333154583

theorem tailTrace_5886443 : CollatzResearch.WordTrace tailWord_5886443 prefixEnd_5886443 335841622699335333154583 := by
  unfold tailWord_5886443
  simp only [CollatzResearch.WordTrace]
  refine ⟨214696214213429810271543983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143130809475619873514362655 214696214213429810271543983)
  ·
    refine ⟨322044321320144715407315975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214696214213429810271543983 322044321320144715407315975)
    ·
      refine ⟨483066481980217073110973963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322044321320144715407315975 483066481980217073110973963)
      ·
        refine ⟨724599722970325609666460945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483066481980217073110973963 724599722970325609666460945)
        ·
          refine ⟨543449792227744207249845709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724599722970325609666460945 543449792227744207249845709)
          ·
            refine ⟨203793672085404077718692141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 543449792227744207249845709 203793672085404077718692141)
            ·
              refine ⟨76422627032026529144509553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203793672085404077718692141 76422627032026529144509553)
              ·
                refine ⟨57316970274019896858382165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76422627032026529144509553 57316970274019896858382165)
                ·
                  refine ⟨335841622699335333154583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57316970274019896858382165 335841622699335333154583)
                  ·
                    rfl

theorem cell23_5886443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 9].length) (baseStart_5886443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886443 prefixEnd_5886443 := by exact prefixLift 5886443
  have htrace : WordTrace (prefixWord ++ tailWord_5886443) baseStart_5886443 baseEnd_5886443 := by
    simpa [prefixWord, tailWord_5886443, baseEnd_5886443] using wordTrace_append hprefix tailTrace_5886443
  have hstable : (prefixWord ++ tailWord_5886443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886443).length < 2 ^ (prefixWord ++ tailWord_5886443).sum := by decide
  have hdescent : baseEnd_5886443 < baseStart_5886443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886471 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 1, 4, 2]
def baseStart_5886471 : Nat := 118140960795 + 5886471 * 2 ^ 59
def prefixEnd_5886471 : Nat := 4983230072969 + 3 ^ 40 * 5886471 * 2
def baseEnd_5886471 : Nat := 3022588981752343888841119

theorem tailTrace_5886471 : CollatzResearch.WordTrace tailWord_5886471 prefixEnd_5886471 3022588981752343888841119 := by
  unfold tailWord_5886471
  simp only [CollatzResearch.WordTrace]
  refine ⟨214697235457328371053563267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143131490304885580702375511 214697235457328371053563267)
  ·
    refine ⟨322045853185992556580344901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214697235457328371053563267 322045853185992556580344901)
    ·
      refine ⟨60383597472373604358814669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 322045853185992556580344901 60383597472373604358814669)
      ·
        refine ⟨22643849052140101634555501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60383597472373604358814669 22643849052140101634555501)
        ·
          refine ⟨8491443394552538112958313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22643849052140101634555501 8491443394552538112958313)
          ·
            refine ⟨6368582545914403584718735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8491443394552538112958313 6368582545914403584718735)
            ·
              refine ⟨9552873818871605377078103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368582545914403584718735 9552873818871605377078103)
              ·
                refine ⟨14329310728307408065617155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9552873818871605377078103 14329310728307408065617155)
                ·
                  refine ⟨21493966092461112098425733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14329310728307408065617155 21493966092461112098425733)
                  ·
                    refine ⟨4030118642336458518454825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21493966092461112098425733 4030118642336458518454825)
                    ·
                      refine ⟨3022588981752343888841119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030118642336458518454825 3022588981752343888841119)
                      ·
                        rfl

theorem cell23_5886471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_5886471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886471 prefixEnd_5886471 := by exact prefixLift 5886471
  have htrace : WordTrace (prefixWord ++ tailWord_5886471) baseStart_5886471 baseEnd_5886471 := by
    simpa [prefixWord, tailWord_5886471, baseEnd_5886471] using wordTrace_append hprefix tailTrace_5886471
  have hstable : (prefixWord ++ tailWord_5886471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886471).length < 2 ^ (prefixWord ++ tailWord_5886471).sum := by decide
  have hdescent : baseEnd_5886471 < baseStart_5886471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886490 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 1, 7]
def baseStart_5886490 : Nat := 118140960795 + 5886490 * 2 ^ 59
def prefixEnd_5886490 : Nat := 4983230072969 + 3 ^ 40 * 5886490 * 2
def baseEnd_5886490 : Nat := 1007532912628259771501177

theorem tailTrace_5886490 : CollatzResearch.WordTrace tailWord_5886490 prefixEnd_5886490 1007532912628259771501177 := by
  unfold tailWord_5886490
  simp only [CollatzResearch.WordTrace]
  refine ⟨53674482111064884324626231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143131952296173024865669949 53674482111064884324626231)
  ·
    refine ⟨80511723166597326486939347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53674482111064884324626231 80511723166597326486939347)
    ·
      refine ⟨120767584749895989730409021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80511723166597326486939347 120767584749895989730409021)
      ·
        refine ⟨45287844281210996148903383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120767584749895989730409021 45287844281210996148903383)
        ·
          refine ⟨67931766421816494223355075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45287844281210996148903383 67931766421816494223355075)
          ·
            refine ⟨101897649632724741335032613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67931766421816494223355075 101897649632724741335032613)
            ·
              refine ⟨19105809306135889000318615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101897649632724741335032613 19105809306135889000318615)
              ·
                refine ⟨28658713959203833500477923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19105809306135889000318615 28658713959203833500477923)
                ·
                  refine ⟨42988070938805750250716885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28658713959203833500477923 42988070938805750250716885)
                  ·
                    refine ⟨1007532912628259771501177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42988070938805750250716885 1007532912628259771501177)
                    ·
                      rfl

theorem cell23_5886490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_5886490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886490 prefixEnd_5886490 := by exact prefixLift 5886490
  have htrace : WordTrace (prefixWord ++ tailWord_5886490) baseStart_5886490 baseEnd_5886490 := by
    simpa [prefixWord, tailWord_5886490, baseEnd_5886490] using wordTrace_append hprefix tailTrace_5886490
  have hstable : (prefixWord ++ tailWord_5886490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886490).length < 2 ^ (prefixWord ++ tailWord_5886490).sum := by decide
  have hdescent : baseEnd_5886490 < baseStart_5886490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886527 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 1, 6, 2]
def baseStart_5886527 : Nat := 118140960795 + 5886527 * 2 ^ 59
def prefixEnd_5886527 : Nat := 4983230072969 + 3 ^ 40 * 5886527 * 2
def baseEnd_5886527 : Nat := 3022617736668995669740861

theorem tailTrace_5886527 : CollatzResearch.WordTrace tailWord_5886527 prefixEnd_5886527 3022617736668995669740861 := by
  unfold tailWord_5886527
  simp only [CollatzResearch.WordTrace]
  refine ⟨214699277945125492617601835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143132851963416995078401223 214699277945125492617601835)
  ·
    refine ⟨322048916917688238926402753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214699277945125492617601835 322048916917688238926402753)
    ·
      refine ⟨241536687688266179194802065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322048916917688238926402753 241536687688266179194802065)
      ·
        refine ⟨181152515766199634396101549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241536687688266179194802065 181152515766199634396101549)
        ·
          refine ⟨67932193412324862898538081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181152515766199634396101549 67932193412324862898538081)
          ·
            refine ⟨50949145059243647173903561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67932193412324862898538081 50949145059243647173903561)
            ·
              refine ⟨38211858794432735380427671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50949145059243647173903561 38211858794432735380427671)
              ·
                refine ⟨57317788191649103070641507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38211858794432735380427671 57317788191649103070641507)
                ·
                  refine ⟨85976682287473654605962261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57317788191649103070641507 85976682287473654605962261)
                  ·
                    refine ⟨4030156982225327559654481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85976682287473654605962261 4030156982225327559654481)
                    ·
                      refine ⟨3022617736668995669740861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030156982225327559654481 3022617736668995669740861)
                      ·
                        rfl

theorem cell23_5886527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 6, 2].length) (baseStart_5886527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886527 prefixEnd_5886527 := by exact prefixLift 5886527
  have htrace : WordTrace (prefixWord ++ tailWord_5886527) baseStart_5886527 baseEnd_5886527 := by
    simpa [prefixWord, tailWord_5886527, baseEnd_5886527] using wordTrace_append hprefix tailTrace_5886527
  have hstable : (prefixWord ++ tailWord_5886527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886527).length < 2 ^ (prefixWord ++ tailWord_5886527).sum := by decide
  have hdescent : baseEnd_5886527 < baseStart_5886527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886597 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 3, 5]
def baseStart_5886597 : Nat := 118140960795 + 5886597 * 2 ^ 59
def prefixEnd_5886597 : Nat := 4983230072969 + 3 ^ 40 * 5886597 * 2
def baseEnd_5886597 : Nat := 1007551226771603465288513

theorem tailTrace_5886597 : CollatzResearch.WordTrace tailWord_5886597 prefixEnd_5886597 1007551226771603465288513 := by
  unfold tailWord_5886597
  simp only [CollatzResearch.WordTrace]
  refine ⟨214701831054871894572650045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143134554036581263048433363 214701831054871894572650045)
  ·
    refine ⟨80513186645576960464743767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214701831054871894572650045 80513186645576960464743767)
    ·
      refine ⟨120769779968365440697115651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80513186645576960464743767 120769779968365440697115651)
      ·
        refine ⟨181154669952548161045673477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120769779968365440697115651 181154669952548161045673477)
        ·
          refine ⟨33966500616102780196063777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181154669952548161045673477 33966500616102780196063777)
          ·
            refine ⟨25474875462077085147047833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33966500616102780196063777 25474875462077085147047833)
            ·
              refine ⟨19106156596557813860285875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25474875462077085147047833 19106156596557813860285875)
              ·
                refine ⟨28659234894836720790428813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19106156596557813860285875 28659234894836720790428813)
                ·
                  refine ⟨10747213085563770296410805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28659234894836720790428813 10747213085563770296410805)
                  ·
                    refine ⟨1007551226771603465288513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10747213085563770296410805 1007551226771603465288513)
                    ·
                      rfl

theorem cell23_5886597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_5886597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886597 prefixEnd_5886597 := by exact prefixLift 5886597
  have htrace : WordTrace (prefixWord ++ tailWord_5886597) baseStart_5886597 baseEnd_5886597 := by
    simpa [prefixWord, tailWord_5886597, baseEnd_5886597] using wordTrace_append hprefix tailTrace_5886597
  have hstable : (prefixWord ++ tailWord_5886597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886597).length < 2 ^ (prefixWord ++ tailWord_5886597).sum := by decide
  have hdescent : baseEnd_5886597 < baseStart_5886597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886604 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 2, 3, 2]
def baseStart_5886604 : Nat := 118140960795 + 5886604 * 2 ^ 59
def prefixEnd_5886604 : Nat := 4983230072969 + 3 ^ 40 * 5886604 * 2
def baseEnd_5886604 : Nat := 3022657274679391868478007

theorem tailTrace_5886604 : CollatzResearch.WordTrace tailWord_5886604 prefixEnd_5886604 3022657274679391868478007 := by
  unfold tailWord_5886604
  simp only [CollatzResearch.WordTrace]
  refine ⟨107351043182923267384077433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143134724243897689845436577 107351043182923267384077433)
  ·
    refine ⟨80513282387192450538058075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107351043182923267384077433 80513282387192450538058075)
    ·
      refine ⟨120769923580788675807087113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80513282387192450538058075 120769923580788675807087113)
      ·
        refine ⟨90577442685591506855315335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120769923580788675807087113 90577442685591506855315335)
        ·
          refine ⟨135866164028387260282973003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90577442685591506855315335 135866164028387260282973003)
          ·
            refine ⟨203799246042580890424459505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135866164028387260282973003 203799246042580890424459505)
            ·
              refine ⟨152849434531935667818344629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203799246042580890424459505 152849434531935667818344629)
              ·
                refine ⟨14329634487368968857969809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152849434531935667818344629 14329634487368968857969809)
                ·
                  refine ⟨10747225865526726643477357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14329634487368968857969809 10747225865526726643477357)
                  ·
                    refine ⟨4030209699572522491304009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10747225865526726643477357 4030209699572522491304009)
                    ·
                      refine ⟨3022657274679391868478007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030209699572522491304009 3022657274679391868478007)
                      ·
                        rfl

theorem cell23_5886604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_5886604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886604 prefixEnd_5886604 := by exact prefixLift 5886604
  have htrace : WordTrace (prefixWord ++ tailWord_5886604) baseStart_5886604 baseEnd_5886604 := by
    simpa [prefixWord, tailWord_5886604, baseEnd_5886604] using wordTrace_append hprefix tailTrace_5886604
  have hstable : (prefixWord ++ tailWord_5886604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886604).length < 2 ^ (prefixWord ++ tailWord_5886604).sum := by decide
  have hdescent : baseEnd_5886604 < baseStart_5886604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886618 : List Nat := [3, 1, 1, 6, 2, 1, 1, 2, 6]
def baseStart_5886618 : Nat := 118140960795 + 5886618 * 2 ^ 59
def prefixEnd_5886618 : Nat := 4983230072969 + 3 ^ 40 * 5886618 * 2
def baseEnd_5886618 : Nat := 335851607045394979300327

theorem tailTrace_5886618 : CollatzResearch.WordTrace tailWord_5886618 prefixEnd_5886618 335851607045394979300327 := by
  unfold tailWord_5886618
  simp only [CollatzResearch.WordTrace]
  refine ⟨53675649246948953789791127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143135064658530543439443005 53675649246948953789791127)
  ·
    refine ⟨80513473870423430684686691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53675649246948953789791127 80513473870423430684686691)
    ·
      refine ⟨120770210805635146027030037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80513473870423430684686691 120770210805635146027030037)
      ·
        refine ⟨5661103631514147470017033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120770210805635146027030037 5661103631514147470017033)
        ·
          refine ⟨4245827723635610602512775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5661103631514147470017033 4245827723635610602512775)
          ·
            refine ⟨6368741585453415903769163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245827723635610602512775 6368741585453415903769163)
            ·
              refine ⟨9553112378180123855653745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368741585453415903769163 9553112378180123855653745)
              ·
                refine ⟨7164834283635092891740309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9553112378180123855653745 7164834283635092891740309)
                ·
                  refine ⟨335851607045394979300327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7164834283635092891740309 335851607045394979300327)
                  ·
                    rfl

theorem cell23_5886618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_5886618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886618 prefixEnd_5886618 := by exact prefixLift 5886618
  have htrace : WordTrace (prefixWord ++ tailWord_5886618) baseStart_5886618 baseEnd_5886618 := by
    simpa [prefixWord, tailWord_5886618, baseEnd_5886618] using wordTrace_append hprefix tailTrace_5886618
  have hstable : (prefixWord ++ tailWord_5886618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886618).length < 2 ^ (prefixWord ++ tailWord_5886618).sum := by decide
  have hdescent : baseEnd_5886618 < baseStart_5886618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886640 : List Nat := [2, 1, 1, 1, 2, 1, 3, 12]
def baseStart_5886640 : Nat := 118140960795 + 5886640 * 2 ^ 59
def prefixEnd_5886640 : Nat := 4983230072969 + 3 ^ 40 * 5886640 * 2
def baseEnd_5886640 : Nat := 111950954073442730652883

theorem tailTrace_5886640 : CollatzResearch.WordTrace tailWord_5886640 prefixEnd_5886640 111950954073442730652883 := by
  unfold tailWord_5886640
  simp only [CollatzResearch.WordTrace]
  refine ⟨107351699696858056458232687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143135599595810741944310249 107351699696858056458232687)
  ·
    refine ⟨161027549545287084687349031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107351699696858056458232687 161027549545287084687349031)
    ·
      refine ⟨241541324317930627031023547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161027549545287084687349031 241541324317930627031023547)
      ·
        refine ⟨362311986476895940546535321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241541324317930627031023547 362311986476895940546535321)
        ·
          refine ⟨271733989857671955409901491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362311986476895940546535321 271733989857671955409901491)
          ·
            refine ⟨407600984786507933114852237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271733989857671955409901491 407600984786507933114852237)
            ·
              refine ⟨152850369294940474918069589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407600984786507933114852237 152850369294940474918069589)
              ·
                refine ⟨111950954073442730652883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 152850369294940474918069589 111950954073442730652883)
                ·
                  rfl

theorem cell23_5886640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 12].length) (baseStart_5886640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886640 prefixEnd_5886640 := by exact prefixLift 5886640
  have htrace : WordTrace (prefixWord ++ tailWord_5886640) baseStart_5886640 baseEnd_5886640 := by
    simpa [prefixWord, tailWord_5886640, baseEnd_5886640] using wordTrace_append hprefix tailTrace_5886640
  have hstable : (prefixWord ++ tailWord_5886640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886640).length < 2 ^ (prefixWord ++ tailWord_5886640).sum := by decide
  have hdescent : baseEnd_5886640 < baseStart_5886640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886674 : List Nat := [3, 2, 2, 2, 3, 2, 9]
def baseStart_5886674 : Nat := 118140960795 + 5886674 * 2 ^ 59
def prefixEnd_5886674 : Nat := 4983230072969 + 3 ^ 40 * 5886674 * 2
def baseEnd_5886674 : Nat := 37317200226237118451885

theorem tailTrace_5886674 : CollatzResearch.WordTrace tailWord_5886674 prefixEnd_5886674 37317200226237118451885 := by
  unfold tailWord_5886674
  simp only [CollatzResearch.WordTrace]
  refine ⟨53676159868898234180800769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143136426317061957815468717 53676159868898234180800769)
  ·
    refine ⟨40257119901673675635600577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53676159868898234180800769 40257119901673675635600577)
    ·
      refine ⟨30192839926255256726700433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40257119901673675635600577 30192839926255256726700433)
      ·
        refine ⟨22644629944691442545025325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30192839926255256726700433 22644629944691442545025325)
        ·
          refine ⟨8491736229259290954384497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22644629944691442545025325 8491736229259290954384497)
          ·
            refine ⟨6368802171944468215788373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8491736229259290954384497 6368802171944468215788373)
            ·
              refine ⟨37317200226237118451885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6368802171944468215788373 37317200226237118451885)
              ·
                rfl

theorem cell23_5886674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 9].length) (baseStart_5886674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886674 prefixEnd_5886674 := by exact prefixLift 5886674
  have htrace : WordTrace (prefixWord ++ tailWord_5886674) baseStart_5886674 baseEnd_5886674 := by
    simpa [prefixWord, tailWord_5886674, baseEnd_5886674] using wordTrace_append hprefix tailTrace_5886674
  have hstable : (prefixWord ++ tailWord_5886674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886674).length < 2 ^ (prefixWord ++ tailWord_5886674).sum := by decide
  have hdescent : baseEnd_5886674 < baseStart_5886674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886754 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_5886754 : Nat := 118140960795 + 5886754 * 2 ^ 59
def prefixEnd_5886754 : Nat := 4983230072969 + 3 ^ 40 * 5886754 * 2
def baseEnd_5886754 : Nat := 3022734296777566281602317

theorem tailTrace_5886754 : CollatzResearch.WordTrace tailWord_5886754 prefixEnd_5886754 3022734296777566281602317 := by
  unfold tailWord_5886754
  simp only [CollatzResearch.WordTrace]
  refine ⟨53676889328825777596528829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143138371543535406924076877 53676889328825777596528829)
  ·
    refine ⟨20128833498309666598698311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53676889328825777596528829 20128833498309666598698311)
    ·
      refine ⟨30193250247464499898047467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20128833498309666598698311 30193250247464499898047467)
      ·
        refine ⟨45289875371196749847071201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30193250247464499898047467 45289875371196749847071201)
        ·
          refine ⟨33967406528397562385303401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45289875371196749847071201 33967406528397562385303401)
          ·
            refine ⟨25475554896298171788977551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33967406528397562385303401 25475554896298171788977551)
            ·
              refine ⟨38213332344447257683466327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25475554896298171788977551 38213332344447257683466327)
              ·
                refine ⟨57319998516670886525199491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38213332344447257683466327 57319998516670886525199491)
                ·
                  refine ⟨85979997775006329787799237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57319998516670886525199491 85979997775006329787799237)
                  ·
                    refine ⟨16121249582813686835212357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85979997775006329787799237 16121249582813686835212357)
                    ·
                      refine ⟨3022734296777566281602317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16121249582813686835212357 3022734296777566281602317)
                      ·
                        rfl

theorem cell23_5886754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_5886754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886754 prefixEnd_5886754 := by exact prefixLift 5886754
  have htrace : WordTrace (prefixWord ++ tailWord_5886754) baseStart_5886754 baseEnd_5886754 := by
    simpa [prefixWord, tailWord_5886754, baseEnd_5886754] using wordTrace_append hprefix tailTrace_5886754
  have hstable : (prefixWord ++ tailWord_5886754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886754).length < 2 ^ (prefixWord ++ tailWord_5886754).sum := by decide
  have hdescent : baseEnd_5886754 < baseStart_5886754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886851 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 3]
def baseStart_5886851 : Nat := 118140960795 + 5886851 * 2 ^ 59
def prefixEnd_5886851 : Nat := 4983230072969 + 3 ^ 40 * 5886851 * 2
def baseEnd_5886851 : Nat := 3022784104401052402089371

theorem tailTrace_5886851 : CollatzResearch.WordTrace tailWord_5886851 prefixEnd_5886851 3022784104401052402089371 := by
  unfold tailWord_5886851
  simp only [CollatzResearch.WordTrace]
  refine ⟨214711095195951695952396407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143140730130634463968264271 214711095195951695952396407)
  ·
    refine ⟨322066642793927543928594611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214711095195951695952396407 322066642793927543928594611)
    ·
      refine ⟨483099964190891315892891917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322066642793927543928594611 483099964190891315892891917)
      ·
        refine ⟨181162486571584243459834469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 483099964190891315892891917 181162486571584243459834469)
        ·
          refine ⟨33967966232172045648718963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181162486571584243459834469 33967966232172045648718963)
          ·
            refine ⟨50951949348258068473078445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33967966232172045648718963 50951949348258068473078445)
            ·
              refine ⟨19106981005596775677404417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50951949348258068473078445 19106981005596775677404417)
              ·
                refine ⟨14330235754197581758053313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19106981005596775677404417 14330235754197581758053313)
                ·
                  refine ⟨10747676815648186318539985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14330235754197581758053313 10747676815648186318539985)
                  ·
                    refine ⟨8060757611736139738904989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10747676815648186318539985 8060757611736139738904989)
                    ·
                      refine ⟨3022784104401052402089371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8060757611736139738904989 3022784104401052402089371)
                      ·
                        rfl

theorem cell23_5886851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_5886851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886851 prefixEnd_5886851 := by exact prefixLift 5886851
  have htrace : WordTrace (prefixWord ++ tailWord_5886851) baseStart_5886851 baseEnd_5886851 := by
    simpa [prefixWord, tailWord_5886851, baseEnd_5886851] using wordTrace_append hprefix tailTrace_5886851
  have hstable : (prefixWord ++ tailWord_5886851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886851).length < 2 ^ (prefixWord ++ tailWord_5886851).sum := by decide
  have hdescent : baseEnd_5886851 < baseStart_5886851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886858 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 3, 4]
def baseStart_5886858 : Nat := 118140960795 + 5886858 * 2 ^ 59
def prefixEnd_5886858 : Nat := 4983230072969 + 3 ^ 40 * 5886858 * 2
def baseEnd_5886858 : Nat := 1007595899588544624900613

theorem tailTrace_5886858 : CollatzResearch.WordTrace tailWord_5886858 prefixEnd_5886858 1007595899588544624900613 := by
  unfold tailWord_5886858
  simp only [CollatzResearch.WordTrace]
  refine ⟨53677837626731584036975307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143140900337950890765267485 53677837626731584036975307)
  ·
    refine ⟨80516756440097376055462961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53677837626731584036975307 80516756440097376055462961)
    ·
      refine ⟨60387567330073032041597221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80516756440097376055462961 60387567330073032041597221)
      ·
        refine ⟨11322668874388693507799479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60387567330073032041597221 11322668874388693507799479)
        ·
          refine ⟨16984003311583040261699219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11322668874388693507799479 16984003311583040261699219)
          ·
            refine ⟨25476004967374560392548829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16984003311583040261699219 25476004967374560392548829)
            ·
              refine ⟨9553501862765460147205811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25476004967374560392548829 9553501862765460147205811)
              ·
                refine ⟨14330252794148190220808717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9553501862765460147205811 14330252794148190220808717)
                ·
                  refine ⟨5373844797805571332803269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14330252794148190220808717 5373844797805571332803269)
                  ·
                    refine ⟨1007595899588544624900613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5373844797805571332803269 1007595899588544624900613)
                    ·
                      rfl

theorem cell23_5886858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_5886858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886858 prefixEnd_5886858 := by exact prefixLift 5886858
  have htrace : WordTrace (prefixWord ++ tailWord_5886858) baseStart_5886858 baseEnd_5886858 := by
    simpa [prefixWord, tailWord_5886858, baseEnd_5886858] using wordTrace_append hprefix tailTrace_5886858
  have hstable : (prefixWord ++ tailWord_5886858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886858).length < 2 ^ (prefixWord ++ tailWord_5886858).sum := by decide
  have hdescent : baseEnd_5886858 < baseStart_5886858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886891 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 6, 3, 2]
def baseStart_5886891 : Nat := 118140960795 + 5886891 * 2 ^ 59
def prefixEnd_5886891 : Nat := 4983230072969 + 3 ^ 40 * 5886891 * 2
def baseEnd_5886891 : Nat := 3022804643627232245589187

theorem tailTrace_5886891 : CollatzResearch.WordTrace tailWord_5886891 prefixEnd_5886891 3022804643627232245589187 := by
  unfold tailWord_5886891
  simp only [CollatzResearch.WordTrace]
  refine ⟨214712554115806782783852527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143141702743871188522568351 214712554115806782783852527)
  ·
    refine ⟨322068831173710174175778791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214712554115806782783852527 322068831173710174175778791)
    ·
      refine ⟨483103246760565261263668187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322068831173710174175778791 483103246760565261263668187)
      ·
        refine ⟨724654870140847891895502281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483103246760565261263668187 724654870140847891895502281)
        ·
          refine ⟨543491152605635918921626711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724654870140847891895502281 543491152605635918921626711)
          ·
            refine ⟨815236728908453878382440067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543491152605635918921626711 815236728908453878382440067)
            ·
              refine ⟨1222855093362680817573660101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815236728908453878382440067 1222855093362680817573660101)
              ·
                refine ⟨229285330005502653295061269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1222855093362680817573660101 229285330005502653295061269)
                ·
                  refine ⟨10747749844007936873205997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 229285330005502653295061269 10747749844007936873205997)
                  ·
                    refine ⟨4030406191502976327452249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10747749844007936873205997 4030406191502976327452249)
                    ·
                      refine ⟨3022804643627232245589187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030406191502976327452249 3022804643627232245589187)
                      ·
                        rfl

theorem cell23_5886891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 3, 2].length) (baseStart_5886891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886891 prefixEnd_5886891 := by exact prefixLift 5886891
  have htrace : WordTrace (prefixWord ++ tailWord_5886891) baseStart_5886891 baseEnd_5886891 := by
    simpa [prefixWord, tailWord_5886891, baseEnd_5886891] using wordTrace_append hprefix tailTrace_5886891
  have hstable : (prefixWord ++ tailWord_5886891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886891).length < 2 ^ (prefixWord ++ tailWord_5886891).sum := by decide
  have hdescent : baseEnd_5886891 < baseStart_5886891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886909 : List Nat := [1, 4, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_5886909 : Nat := 118140960795 + 5886909 * 2 ^ 59
def prefixEnd_5886909 : Nat := 4983230072969 + 3 ^ 40 * 5886909 * 2
def baseEnd_5886909 : Nat := 1007604628759671058388035

theorem tailTrace_5886909 : CollatzResearch.WordTrace tailWord_5886909 prefixEnd_5886909 1007604628759671058388035 := by
  unfold tailWord_5886909
  simp only [CollatzResearch.WordTrace]
  refine ⟨214713210629741571858007781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143142140419827714572005187 214713210629741571858007781)
  ·
    refine ⟨40258726993076544723376459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214713210629741571858007781 40258726993076544723376459)
    ·
      refine ⟨60388090489614817085064689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40258726993076544723376459 60388090489614817085064689)
      ·
        refine ⟨45291067867211112813798517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60388090489614817085064689 45291067867211112813798517)
        ·
          refine ⟨4246037612551041826293611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45291067867211112813798517 4246037612551041826293611)
          ·
            refine ⟨6369056418826562739440417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4246037612551041826293611 6369056418826562739440417)
            ·
              refine ⟨4776792314119922054580313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6369056418826562739440417 4776792314119922054580313)
              ·
                refine ⟨3582594235589941540935235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4776792314119922054580313 3582594235589941540935235)
                ·
                  refine ⟨5373891353384912311402853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582594235589941540935235 5373891353384912311402853)
                  ·
                    refine ⟨1007604628759671058388035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5373891353384912311402853 1007604628759671058388035)
                    ·
                      rfl

theorem cell23_5886909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_5886909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886909 prefixEnd_5886909 := by exact prefixLift 5886909
  have htrace : WordTrace (prefixWord ++ tailWord_5886909) baseStart_5886909 baseEnd_5886909 := by
    simpa [prefixWord, tailWord_5886909, baseEnd_5886909] using wordTrace_append hprefix tailTrace_5886909
  have hstable : (prefixWord ++ tailWord_5886909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886909).length < 2 ^ (prefixWord ++ tailWord_5886909).sum := by decide
  have hdescent : baseEnd_5886909 < baseStart_5886909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886949 : List Nat := [1, 3, 1, 6, 1, 1, 2, 3, 1, 1, 3]
def baseStart_5886949 : Nat := 118140960795 + 5886949 * 2 ^ 59
def prefixEnd_5886949 : Nat := 4983230072969 + 3 ^ 40 * 5886949 * 2
def baseEnd_5886949 : Nat := 3022834425505193018663921

theorem tailTrace_5886949 : CollatzResearch.WordTrace tailWord_5886949 prefixEnd_5886949 3022834425505193018663921 := by
  unfold tailWord_5886949
  simp only [CollatzResearch.WordTrace]
  refine ⟨214714669549596658689463901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143143113033064439126309267 214714669549596658689463901)
  ·
    refine ⟨80518001081098747008548963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214714669549596658689463901 80518001081098747008548963)
    ·
      refine ⟨120777001621648120512823445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80518001081098747008548963 120777001621648120512823445)
      ·
        refine ⟨5661421951014755649038599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120777001621648120512823445 5661421951014755649038599)
        ·
          refine ⟨8492132926522133473557899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5661421951014755649038599 8492132926522133473557899)
          ·
            refine ⟨12738199389783200210336849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8492132926522133473557899 12738199389783200210336849)
            ·
              refine ⟨9553649542337400157752637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12738199389783200210336849 9553649542337400157752637)
              ·
                refine ⟨3582618578376525059157239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9553649542337400157752637 3582618578376525059157239)
                ·
                  refine ⟨5373927867564787588735859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582618578376525059157239 5373927867564787588735859)
                  ·
                    refine ⟨8060891801347181383103789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5373927867564787588735859 8060891801347181383103789)
                    ·
                      refine ⟨3022834425505193018663921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8060891801347181383103789 3022834425505193018663921)
                      ·
                        rfl

theorem cell23_5886949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_5886949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886949 prefixEnd_5886949 := by exact prefixLift 5886949
  have htrace : WordTrace (prefixWord ++ tailWord_5886949) baseStart_5886949 baseEnd_5886949 := by
    simpa [prefixWord, tailWord_5886949, baseEnd_5886949] using wordTrace_append hprefix tailTrace_5886949
  have hstable : (prefixWord ++ tailWord_5886949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886949).length < 2 ^ (prefixWord ++ tailWord_5886949).sum := by decide
  have hdescent : baseEnd_5886949 < baseStart_5886949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886972 : List Nat := [2, 2, 2, 1, 2, 3, 2, 4, 1, 2, 2]
def baseStart_5886972 : Nat := 118140960795 + 5886972 * 2 ^ 59
def prefixEnd_5886972 : Nat := 4983230072969 + 3 ^ 40 * 5886972 * 2
def baseEnd_5886972 : Nat := 3022846235560246428676315

theorem tailTrace_5886972 : CollatzResearch.WordTrace tailWord_5886972 prefixEnd_5886972 3022846235560246428676315 := by
  unfold tailWord_5886972
  simp only [CollatzResearch.WordTrace]
  refine ⟨107357754214256666808775585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143143672285675555745034113 107357754214256666808775585)
  ·
    refine ⟨80518315660692500106581689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107357754214256666808775585 80518315660692500106581689)
    ·
      refine ⟨60388736745519375079936267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80518315660692500106581689 60388736745519375079936267)
      ·
        refine ⟨90583105118279062619904401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60388736745519375079936267 90583105118279062619904401)
        ·
          refine ⟨67937328838709296964928301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90583105118279062619904401 67937328838709296964928301)
          ·
            refine ⟨25476498314515986361848113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67937328838709296964928301 25476498314515986361848113)
            ·
              refine ⟨19107373735886989771386085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25476498314515986361848113 19107373735886989771386085)
              ·
                refine ⟨3582632575478810582134891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19107373735886989771386085 3582632575478810582134891)
                ·
                  refine ⟨5373948863218215873202337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582632575478810582134891 5373948863218215873202337)
                  ·
                    refine ⟨4030461647413661904901753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5373948863218215873202337 4030461647413661904901753)
                    ·
                      refine ⟨3022846235560246428676315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030461647413661904901753 3022846235560246428676315)
                      ·
                        rfl

theorem cell23_5886972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_5886972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886972 prefixEnd_5886972 := by exact prefixLift 5886972
  have htrace : WordTrace (prefixWord ++ tailWord_5886972) baseStart_5886972 baseEnd_5886972 := by
    simpa [prefixWord, tailWord_5886972, baseEnd_5886972] using wordTrace_append hprefix tailTrace_5886972
  have hstable : (prefixWord ++ tailWord_5886972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886972).length < 2 ^ (prefixWord ++ tailWord_5886972).sum := by decide
  have hdescent : baseEnd_5886972 < baseStart_5886972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5886988 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 1, 3, 3]
def baseStart_5886988 : Nat := 118140960795 + 5886988 * 2 ^ 59
def prefixEnd_5886988 : Nat := 4983230072969 + 3 ^ 40 * 5886988 * 2
def baseEnd_5886988 : Nat := 3022854451250718366076241

theorem tailTrace_5886988 : CollatzResearch.WordTrace tailWord_5886988 prefixEnd_5886988 3022854451250718366076241 := by
  unfold tailWord_5886988
  simp only [CollatzResearch.WordTrace]
  refine ⟨107358045998227684175066809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143144061330970245566755745 107358045998227684175066809)
  ·
    refine ⟨80518534498670763131300107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107358045998227684175066809 80518534498670763131300107)
    ·
      refine ⟨120777801748006144696950161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80518534498670763131300107 120777801748006144696950161)
      ·
        refine ⟨90583351311004608522712621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120777801748006144696950161 90583351311004608522712621)
        ·
          refine ⟨33968756741626728196017233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90583351311004608522712621 33968756741626728196017233)
          ·
            refine ⟨25476567556220046147012925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33968756741626728196017233 25476567556220046147012925)
            ·
              refine ⟨9553712833582517305129847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25476567556220046147012925 9553712833582517305129847)
              ·
                refine ⟨14330569250373775957694771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9553712833582517305129847 14330569250373775957694771)
                ·
                  refine ⟨21495853875560663936542157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14330569250373775957694771 21495853875560663936542157)
                  ·
                    refine ⟨8060945203335248976203309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21495853875560663936542157 8060945203335248976203309)
                    ·
                      refine ⟨3022854451250718366076241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8060945203335248976203309 3022854451250718366076241)
                      ·
                        rfl

theorem cell23_5886988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_5886988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5886988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5886988 prefixEnd_5886988 := by exact prefixLift 5886988
  have htrace : WordTrace (prefixWord ++ tailWord_5886988) baseStart_5886988 baseEnd_5886988 := by
    simpa [prefixWord, tailWord_5886988, baseEnd_5886988] using wordTrace_append hprefix tailTrace_5886988
  have hstable : (prefixWord ++ tailWord_5886988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5886988).length < 2 ^ (prefixWord ++ tailWord_5886988).sum := by decide
  have hdescent : baseEnd_5886988 < baseStart_5886988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5886988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887031 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 3]
def baseStart_5887031 : Nat := 118140960795 + 5887031 * 2 ^ 59
def prefixEnd_5887031 : Nat := 4983230072969 + 3 ^ 40 * 5887031 * 2
def baseEnd_5887031 : Nat := 3022876530918861697838543

theorem tailTrace_5887031 : CollatzResearch.WordTrace tailWord_5887031 prefixEnd_5887031 3022876530918861697838543 := by
  unfold tailWord_5887031
  simp only [CollatzResearch.WordTrace]
  refine ⟨214717660335299586693948947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143145106890199724462632631 214717660335299586693948947)
  ·
    refine ⟨322076490502949380040923421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214717660335299586693948947 322076490502949380040923421)
    ·
      refine ⟨120778683938606017515346283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322076490502949380040923421 120778683938606017515346283)
      ·
        refine ⟨181168025907909026273019425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120778683938606017515346283 181168025907909026273019425)
        ·
          refine ⟨135876019430931769704764569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181168025907909026273019425 135876019430931769704764569)
          ·
            refine ⟨101907014573198827278573427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135876019430931769704764569 101907014573198827278573427)
            ·
              refine ⟨152860521859798240917860141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101907014573198827278573427 152860521859798240917860141)
              ·
                refine ⟨57322695697424340344197553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152860521859798240917860141 57322695697424340344197553)
                ·
                  refine ⟨42992021773068255258148165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57322695697424340344197553 42992021773068255258148165)
                  ·
                    refine ⟨8061004082450297860902781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42992021773068255258148165 8061004082450297860902781)
                    ·
                      refine ⟨3022876530918861697838543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8061004082450297860902781 3022876530918861697838543)
                      ·
                        rfl

theorem cell23_5887031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_5887031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887031 prefixEnd_5887031 := by exact prefixLift 5887031
  have htrace : WordTrace (prefixWord ++ tailWord_5887031) baseStart_5887031 baseEnd_5887031 := by
    simpa [prefixWord, tailWord_5887031, baseEnd_5887031] using wordTrace_append hprefix tailTrace_5887031
  have hstable : (prefixWord ++ tailWord_5887031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887031).length < 2 ^ (prefixWord ++ tailWord_5887031).sum := by decide
  have hdescent : baseEnd_5887031 < baseStart_5887031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887085 : List Nat := [1, 5, 1, 1, 2, 3, 1, 4, 5]
def baseStart_5887085 : Nat := 118140960795 + 5887085 * 2 ^ 59
def prefixEnd_5887085 : Nat := 4983230072969 + 3 ^ 40 * 5887085 * 2
def baseEnd_5887085 : Nat := 335878250986022720729255

theorem tailTrace_5887085 : CollatzResearch.WordTrace tailWord_5887085 prefixEnd_5887085 335878250986022720729255 := by
  unfold tailWord_5887085
  simp only [CollatzResearch.WordTrace]
  refine ⟨214719629877103953916414709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143146419918069302610943139 214719629877103953916414709)
  ·
    refine ⟨20129965300978495679663879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214719629877103953916414709 20129965300978495679663879)
    ·
      refine ⟨30194947951467743519495819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20129965300978495679663879 30194947951467743519495819)
      ·
        refine ⟨45292421927201615279243729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30194947951467743519495819 45292421927201615279243729)
        ·
          refine ⟨33969316445401211459432797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45292421927201615279243729 33969316445401211459432797)
          ·
            refine ⟨12738493667025454297287299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33969316445401211459432797 12738493667025454297287299)
            ·
              refine ⟨19107740500538181445930949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12738493667025454297287299 19107740500538181445930949)
              ·
                refine ⟨3582701343850909021112053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19107740500538181445930949 3582701343850909021112053)
                ·
                  refine ⟨335878250986022720729255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3582701343850909021112053 335878250986022720729255)
                  ·
                    rfl

theorem cell23_5887085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_5887085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887085 prefixEnd_5887085 := by exact prefixLift 5887085
  have htrace : WordTrace (prefixWord ++ tailWord_5887085) baseStart_5887085 baseEnd_5887085 := by
    simpa [prefixWord, tailWord_5887085, baseEnd_5887085] using wordTrace_append hprefix tailTrace_5887085
  have hstable : (prefixWord ++ tailWord_5887085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887085).length < 2 ^ (prefixWord ++ tailWord_5887085).sum := by decide
  have hdescent : baseEnd_5887085 < baseStart_5887085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887088 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 1, 7, 2]
def baseStart_5887088 : Nat := 118140960795 + 5887088 * 2 ^ 59
def prefixEnd_5887088 : Nat := 4983230072969 + 3 ^ 40 * 5887088 * 2
def baseEnd_5887088 : Nat := 3022905799316167974825781

theorem tailTrace_5887088 : CollatzResearch.WordTrace tailWord_5887088 prefixEnd_5887088 3022905799316167974825781 := by
  unfold tailWord_5887088
  simp only [CollatzResearch.WordTrace]
  refine ⟨107359869648046542714386959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143146492864062056952515945 107359869648046542714386959)
  ·
    refine ⟨161039804472069814071580439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107359869648046542714386959 161039804472069814071580439)
    ·
      refine ⟨241559706708104721107370659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161039804472069814071580439 241559706708104721107370659)
      ·
        refine ⟨362339560062157081661055989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241559706708104721107370659 362339560062157081661055989)
        ·
          refine ⟨33969333755827226405723999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 362339560062157081661055989 33969333755827226405723999)
          ·
            refine ⟨50954000633740839608585999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33969333755827226405723999 50954000633740839608585999)
            ·
              refine ⟨76431000950611259412878999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50954000633740839608585999 76431000950611259412878999)
              ·
                refine ⟨114646501425916889119318499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76431000950611259412878999 114646501425916889119318499)
                ·
                  refine ⟨171969752138875333678977749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114646501425916889119318499 171969752138875333678977749)
                  ·
                    refine ⟨4030541065754890633101041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 171969752138875333678977749 4030541065754890633101041)
                    ·
                      refine ⟨3022905799316167974825781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030541065754890633101041 3022905799316167974825781)
                      ·
                        rfl

theorem cell23_5887088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 7, 2].length) (baseStart_5887088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887088 prefixEnd_5887088 := by exact prefixLift 5887088
  have htrace : WordTrace (prefixWord ++ tailWord_5887088) baseStart_5887088 baseEnd_5887088 := by
    simpa [prefixWord, tailWord_5887088, baseEnd_5887088] using wordTrace_append hprefix tailTrace_5887088
  have hstable : (prefixWord ++ tailWord_5887088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887088).length < 2 ^ (prefixWord ++ tailWord_5887088).sum := by decide
  have hdescent : baseEnd_5887088 < baseStart_5887088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887272 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_5887272 : Nat := 118140960795 + 5887272 * 2 ^ 59
def prefixEnd_5887272 : Nat := 4983230072969 + 3 ^ 40 * 5887272 * 2
def baseEnd_5887272 : Nat := 3023000279756595254924935

theorem tailTrace_5887272 : CollatzResearch.WordTrace tailWord_5887272 prefixEnd_5887272 3023000279756595254924935 := by
  unfold tailWord_5887272
  simp only [CollatzResearch.WordTrace]
  refine ⟨107363225163713242426736035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143150966884950989902314713 107363225163713242426736035)
  ·
    refine ⟨161044837745569863640104053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107363225163713242426736035 161044837745569863640104053)
    ·
      refine ⟨15097953538647174716259755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161044837745569863640104053 15097953538647174716259755)
      ·
        refine ⟨22646930307970762074389633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15097953538647174716259755 22646930307970762074389633)
        ·
          refine ⟨16985197730978071555792225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22646930307970762074389633 16985197730978071555792225)
          ·
            refine ⟨12738898298233553666844169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16985197730978071555792225 12738898298233553666844169)
            ·
              refine ⟨9554173723675165250133127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12738898298233553666844169 9554173723675165250133127)
              ·
                refine ⟨14331260585512747875199691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9554173723675165250133127 14331260585512747875199691)
                ·
                  refine ⟨21496890878269121812799537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14331260585512747875199691 21496890878269121812799537)
                  ·
                    refine ⟨16122668158701841359599653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21496890878269121812799537 16122668158701841359599653)
                    ·
                      refine ⟨3023000279756595254924935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16122668158701841359599653 3023000279756595254924935)
                      ·
                        rfl

theorem cell23_5887272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_5887272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887272 prefixEnd_5887272 := by exact prefixLift 5887272
  have htrace : WordTrace (prefixWord ++ tailWord_5887272) baseStart_5887272 baseEnd_5887272 := by
    simpa [prefixWord, tailWord_5887272, baseEnd_5887272] using wordTrace_append hprefix tailTrace_5887272
  have hstable : (prefixWord ++ tailWord_5887272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887272).length < 2 ^ (prefixWord ++ tailWord_5887272).sum := by decide
  have hdescent : baseEnd_5887272 < baseStart_5887272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887288 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_5887288 : Nat := 118140960795 + 5887288 * 2 ^ 59
def prefixEnd_5887288 : Nat := 4983230072969 + 3 ^ 40 * 5887288 * 2
def baseEnd_5887288 : Nat := 3023008495447067192324861

theorem tailTrace_5887288 : CollatzResearch.WordTrace tailWord_5887288 prefixEnd_5887288 3023008495447067192324861 := by
  unfold tailWord_5887288
  simp only [CollatzResearch.WordTrace]
  refine ⟨107363516947684259793027259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143151355930245679724036345 107363516947684259793027259)
  ·
    refine ⟨161045275421526389689540889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107363516947684259793027259 161045275421526389689540889)
    ·
      refine ⟨120783956566144792267155667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161045275421526389689540889 120783956566144792267155667)
      ·
        refine ⟨181175934849217188400733501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120783956566144792267155667 181175934849217188400733501)
        ·
          refine ⟨67940975568456445650275063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181175934849217188400733501 67940975568456445650275063)
          ·
            refine ⟨101911463352684668475412595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67940975568456445650275063 101911463352684668475412595)
            ·
              refine ⟨152867195029027002713118893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101911463352684668475412595 152867195029027002713118893)
              ·
                refine ⟨57325198135885126017419585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152867195029027002713118893 57325198135885126017419585)
                ·
                  refine ⟨42993898601913844513064689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57325198135885126017419585 42993898601913844513064689)
                  ·
                    refine ⟨32245423951435383384798517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42993898601913844513064689 32245423951435383384798517)
                    ·
                      refine ⟨3023008495447067192324861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32245423951435383384798517 3023008495447067192324861)
                      ·
                        rfl

theorem cell23_5887288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_5887288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887288 prefixEnd_5887288 := by exact prefixLift 5887288
  have htrace : WordTrace (prefixWord ++ tailWord_5887288) baseStart_5887288 baseEnd_5887288 := by
    simpa [prefixWord, tailWord_5887288, baseEnd_5887288] using wordTrace_append hprefix tailTrace_5887288
  have hstable : (prefixWord ++ tailWord_5887288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887288).length < 2 ^ (prefixWord ++ tailWord_5887288).sum := by decide
  have hdescent : baseEnd_5887288 < baseStart_5887288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887293 : List Nat := [1, 4, 1, 5, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5887293 : Nat := 118140960795 + 5887293 * 2 ^ 59
def prefixEnd_5887293 : Nat := 4983230072969 + 3 ^ 40 * 5887293 * 2
def baseEnd_5887293 : Nat := 3023011062850339672762339

theorem tailTrace_5887293 : CollatzResearch.WordTrace tailWord_5887293 prefixEnd_5887293 3023011062850339672762339 := by
  unfold tailWord_5887293
  simp only [CollatzResearch.WordTrace]
  refine ⟨214727216260350405439986533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143151477506900270293324355 214727216260350405439986533)
  ·
    refine ⟨40261353048815701019997475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214727216260350405439986533 40261353048815701019997475)
    ·
      refine ⟨60392029573223551529996213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40261353048815701019997475 60392029573223551529996213)
      ·
        refine ⟨5661752772489707955937145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60392029573223551529996213 5661752772489707955937145)
        ·
          refine ⟨4246314579367280966952859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5661752772489707955937145 4246314579367280966952859)
          ·
            refine ⟨6369471869050921450429289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4246314579367280966952859 6369471869050921450429289)
            ·
              refine ⟨4777103901788191087821967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6369471869050921450429289 4777103901788191087821967)
              ·
                refine ⟨7165655852682286631732951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4777103901788191087821967 7165655852682286631732951)
                ·
                  refine ⟨10748483779023429947599427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7165655852682286631732951 10748483779023429947599427)
                  ·
                    refine ⟨16122725668535144921399141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10748483779023429947599427 16122725668535144921399141)
                    ·
                      refine ⟨3023011062850339672762339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16122725668535144921399141 3023011062850339672762339)
                      ·
                        rfl

theorem cell23_5887293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5887293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887293 prefixEnd_5887293 := by exact prefixLift 5887293
  have htrace : WordTrace (prefixWord ++ tailWord_5887293) baseStart_5887293 baseEnd_5887293 := by
    simpa [prefixWord, tailWord_5887293, baseEnd_5887293] using wordTrace_append hprefix tailTrace_5887293
  have hstable : (prefixWord ++ tailWord_5887293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887293).length < 2 ^ (prefixWord ++ tailWord_5887293).sum := by decide
  have hdescent : baseEnd_5887293 < baseStart_5887293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887336 : List Nat := [2, 1, 4, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_5887336 : Nat := 118140960795 + 5887336 * 2 ^ 59
def prefixEnd_5887336 : Nat := 4983230072969 + 3 ^ 40 * 5887336 * 2
def baseEnd_5887336 : Nat := 3023033142518483004524641

theorem tailTrace_5887336 : CollatzResearch.WordTrace tailWord_5887336 prefixEnd_5887336 3023033142518483004524641 := by
  unfold tailWord_5887336
  simp only [CollatzResearch.WordTrace]
  refine ⟨107364392299597311891900931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143152523066129749189201241 107364392299597311891900931)
  ·
    refine ⟨161046588449395967837851397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107364392299597311891900931 161046588449395967837851397)
    ·
      refine ⟨30196235334261743969597137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161046588449395967837851397 30196235334261743969597137)
      ·
        refine ⟨22647176500696307977197853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30196235334261743969597137 22647176500696307977197853)
        ·
          refine ⟨8492691187761115491449195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22647176500696307977197853 8492691187761115491449195)
          ·
            refine ⟨12739036781641673237173793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8492691187761115491449195 12739036781641673237173793)
            ·
              refine ⟨9554277586231254927880345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12739036781641673237173793 9554277586231254927880345)
              ·
                refine ⟨7165708189673441195910259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9554277586231254927880345 7165708189673441195910259)
                ·
                  refine ⟨10748562284510161793865389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7165708189673441195910259 10748562284510161793865389)
                  ·
                    refine ⟨4030710856691310672699521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10748562284510161793865389 4030710856691310672699521)
                    ·
                      refine ⟨3023033142518483004524641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030710856691310672699521 3023033142518483004524641)
                      ·
                        rfl

theorem cell23_5887336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_5887336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887336 prefixEnd_5887336 := by exact prefixLift 5887336
  have htrace : WordTrace (prefixWord ++ tailWord_5887336) baseStart_5887336 baseEnd_5887336 := by
    simpa [prefixWord, tailWord_5887336, baseEnd_5887336] using wordTrace_append hprefix tailTrace_5887336
  have hstable : (prefixWord ++ tailWord_5887336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887336).length < 2 ^ (prefixWord ++ tailWord_5887336).sum := by decide
  have hdescent : baseEnd_5887336 < baseStart_5887336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887365 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 4, 3, 3]
def baseStart_5887365 : Nat := 118140960795 + 5887365 * 2 ^ 59
def prefixEnd_5887365 : Nat := 4983230072969 + 3 ^ 40 * 5887365 * 2
def baseEnd_5887365 : Nat := 3023048033457463391062007

theorem tailTrace_5887365 : CollatzResearch.WordTrace tailWord_5887365 prefixEnd_5887365 3023048033457463391062007 := by
  unfold tailWord_5887365
  simp only [CollatzResearch.WordTrace]
  refine ⟨214729842316089561736607549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143153228210726374491071699 214729842316089561736607549)
  ·
    refine ⟨80523690868533585651227831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214729842316089561736607549 80523690868533585651227831)
    ·
      refine ⟨120785536302800378476841747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80523690868533585651227831 120785536302800378476841747)
      ·
        refine ⟨181178304454200567715262621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120785536302800378476841747 181178304454200567715262621)
        ·
          refine ⟨67941864170325212893223483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181178304454200567715262621 67941864170325212893223483)
          ·
            refine ⟨101912796255487819339835225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67941864170325212893223483 101912796255487819339835225)
            ·
              refine ⟨76434597191615864504876419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101912796255487819339835225 76434597191615864504876419)
              ·
                refine ⟨114651895787423796757314629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76434597191615864504876419 114651895787423796757314629)
                ·
                  refine ⟨21497230460141961891996493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114651895787423796757314629 21497230460141961891996493)
                  ·
                    refine ⟨8061461422553235709498685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21497230460141961891996493 8061461422553235709498685)
                    ·
                      refine ⟨3023048033457463391062007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8061461422553235709498685 3023048033457463391062007)
                      ·
                        rfl

theorem cell23_5887365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_5887365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887365 prefixEnd_5887365 := by exact prefixLift 5887365
  have htrace : WordTrace (prefixWord ++ tailWord_5887365) baseStart_5887365 baseEnd_5887365 := by
    simpa [prefixWord, tailWord_5887365, baseEnd_5887365] using wordTrace_append hprefix tailTrace_5887365
  have hstable : (prefixWord ++ tailWord_5887365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887365).length < 2 ^ (prefixWord ++ tailWord_5887365).sum := by decide
  have hdescent : baseEnd_5887365 < baseStart_5887365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887432 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 3, 4]
def baseStart_5887432 : Nat := 118140960795 + 5887432 * 2 ^ 59
def prefixEnd_5887432 : Nat := 4983230072969 + 3 ^ 40 * 5887432 * 2
def baseEnd_5887432 : Nat := 1007694145553771542974733

theorem tailTrace_5887432 : CollatzResearch.WordTrace tailWord_5887432 prefixEnd_5887432 1007694145553771542974733 := by
  unfold tailWord_5887432
  simp only [CollatzResearch.WordTrace]
  refine ⟨107366143003423416089648275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143154857337897888119531033 107366143003423416089648275)
  ·
    refine ⟨161049214505135124134472413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107366143003423416089648275 161049214505135124134472413)
    ·
      refine ⟨60393455439425671550427155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161049214505135124134472413 60393455439425671550427155)
      ·
        refine ⟨90590183159138507325640733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60393455439425671550427155 90590183159138507325640733)
        ·
          refine ⟨33971318684676940247115275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90590183159138507325640733 33971318684676940247115275)
          ·
            refine ⟨50956978027015410370672913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33971318684676940247115275 50956978027015410370672913)
            ·
              refine ⟨38217733520261557778004685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50956978027015410370672913 38217733520261557778004685)
              ·
                refine ⟨14331650070098084166751757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38217733520261557778004685 14331650070098084166751757)
                ·
                  refine ⟨5374368776286781562531909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14331650070098084166751757 5374368776286781562531909)
                  ·
                    refine ⟨1007694145553771542974733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5374368776286781562531909 1007694145553771542974733)
                    ·
                      rfl

theorem cell23_5887432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_5887432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887432 prefixEnd_5887432 := by exact prefixLift 5887432
  have htrace : WordTrace (prefixWord ++ tailWord_5887432) baseStart_5887432 baseEnd_5887432 := by
    simpa [prefixWord, tailWord_5887432, baseEnd_5887432] using wordTrace_append hprefix tailTrace_5887432
  have hstable : (prefixWord ++ tailWord_5887432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887432).length < 2 ^ (prefixWord ++ tailWord_5887432).sum := by decide
  have hdescent : baseEnd_5887432 < baseStart_5887432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887459 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 3]
def baseStart_5887459 : Nat := 118140960795 + 5887459 * 2 ^ 59
def prefixEnd_5887459 : Nat := 4983230072969 + 3 ^ 40 * 5887459 * 2
def baseEnd_5887459 : Nat := 3023096300638986023286575

theorem tailTrace_5887459 : CollatzResearch.WordTrace tailWord_5887459 prefixEnd_5887459 3023096300638986023286575 := by
  unfold tailWord_5887459
  simp only [CollatzResearch.WordTrace]
  refine ⟨214733270777749015790529431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143155513851832677193686287 214733270777749015790529431)
  ·
    refine ⟨322099906166623523685794147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214733270777749015790529431 322099906166623523685794147)
    ·
      refine ⟨483149859249935285528691221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322099906166623523685794147 483149859249935285528691221)
      ·
        refine ⟨22647649652340716509157401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 483149859249935285528691221 22647649652340716509157401)
        ·
          refine ⟨16985737239255537381868051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22647649652340716509157401 16985737239255537381868051)
          ·
            refine ⟨25478605858883306072802077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16985737239255537381868051 25478605858883306072802077)
            ·
              refine ⟨9554477197081239777300779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25478605858883306072802077 9554477197081239777300779)
              ·
                refine ⟨14331715795621859665951169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9554477197081239777300779 14331715795621859665951169)
                ·
                  refine ⟨10748786846716394749463377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14331715795621859665951169 10748786846716394749463377)
                  ·
                    refine ⟨8061590135037296062097533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10748786846716394749463377 8061590135037296062097533)
                    ·
                      refine ⟨3023096300638986023286575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8061590135037296062097533 3023096300638986023286575)
                      ·
                        rfl

theorem cell23_5887459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_5887459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887459 prefixEnd_5887459 := by exact prefixLift 5887459
  have htrace : WordTrace (prefixWord ++ tailWord_5887459) baseStart_5887459 baseEnd_5887459 := by
    simpa [prefixWord, tailWord_5887459, baseEnd_5887459] using wordTrace_append hprefix tailTrace_5887459
  have hstable : (prefixWord ++ tailWord_5887459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887459).length < 2 ^ (prefixWord ++ tailWord_5887459).sum := by decide
  have hdescent : baseEnd_5887459 < baseStart_5887459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887475 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 5, 5]
def baseStart_5887475 : Nat := 118140960795 + 5887475 * 2 ^ 59
def prefixEnd_5887475 : Nat := 4983230072969 + 3 ^ 40 * 5887475 * 2
def baseEnd_5887475 : Nat := 1007701505443152653562167

theorem tailTrace_5887475 : CollatzResearch.WordTrace tailWord_5887475 prefixEnd_5887475 1007701505443152653562167 := by
  unfold tailWord_5887475
  simp only [CollatzResearch.WordTrace]
  refine ⟨214733854345691050523111879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143155902897127367015407919 214733854345691050523111879)
  ·
    refine ⟨322100781518536575784667819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214733854345691050523111879 322100781518536575784667819)
    ·
      refine ⟨483151172277804863677001729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322100781518536575784667819 483151172277804863677001729)
      ·
        refine ⟨362363379208353647757751297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483151172277804863677001729 362363379208353647757751297)
        ·
          refine ⟨271772534406265235818313473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362363379208353647757751297 271772534406265235818313473)
          ·
            refine ⟨203829400804698926863735105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271772534406265235818313473 203829400804698926863735105)
            ·
              refine ⟨152872050603524195147801329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203829400804698926863735105 152872050603524195147801329)
              ·
                refine ⟨114654037952643146360850997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152872050603524195147801329 114654037952643146360850997)
                ·
                  refine ⟨10748816058060294971329781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114654037952643146360850997 10748816058060294971329781)
                  ·
                    refine ⟨1007701505443152653562167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10748816058060294971329781 1007701505443152653562167)
                    ·
                      rfl

theorem cell23_5887475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 5].length) (baseStart_5887475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887475 prefixEnd_5887475 := by exact prefixLift 5887475
  have htrace : WordTrace (prefixWord ++ tailWord_5887475) baseStart_5887475 baseEnd_5887475 := by
    simpa [prefixWord, tailWord_5887475, baseEnd_5887475] using wordTrace_append hprefix tailTrace_5887475
  have hstable : (prefixWord ++ tailWord_5887475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887475).length < 2 ^ (prefixWord ++ tailWord_5887475).sum := by decide
  have hdescent : baseEnd_5887475 < baseStart_5887475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887509 : List Nat := [1, 3, 2, 1, 3, 3, 2, 2, 1, 5]
def baseStart_5887509 : Nat := 118140960795 + 5887509 * 2 ^ 59
def prefixEnd_5887509 : Nat := 4983230072969 + 3 ^ 40 * 5887509 * 2
def baseEnd_5887509 : Nat := 1007707324890570275887115

theorem tailTrace_5887509 : CollatzResearch.WordTrace tailWord_5887509 prefixEnd_5887509 1007707324890570275887115 := by
  unfold tailWord_5887509
  simp only [CollatzResearch.WordTrace]
  refine ⟨214735094427567874329849581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143156729618378582886566387 214735094427567874329849581)
  ·
    refine ⟨80525660410337952873693593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214735094427567874329849581 80525660410337952873693593)
    ·
      refine ⟨60394245307753464655270195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80525660410337952873693593 60394245307753464655270195)
      ·
        refine ⟨90591367961630196982905293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60394245307753464655270195 90591367961630196982905293)
        ·
          refine ⟨33971762985611323868589485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90591367961630196982905293 33971762985611323868589485)
          ·
            refine ⟨12739411119604246450721057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33971762985611323868589485 12739411119604246450721057)
            ·
              refine ⟨9554558339703184838040793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12739411119604246450721057 9554558339703184838040793)
              ·
                refine ⟨7165918754777388628530595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9554558339703184838040793 7165918754777388628530595)
                ·
                  refine ⟨10748878132166082942795893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7165918754777388628530595 10748878132166082942795893)
                  ·
                    refine ⟨1007707324890570275887115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10748878132166082942795893 1007707324890570275887115)
                    ·
                      rfl

theorem cell23_5887509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_5887509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887509 prefixEnd_5887509 := by exact prefixLift 5887509
  have htrace : WordTrace (prefixWord ++ tailWord_5887509) baseStart_5887509 baseEnd_5887509 := by
    simpa [prefixWord, tailWord_5887509, baseEnd_5887509] using wordTrace_append hprefix tailTrace_5887509
  have hstable : (prefixWord ++ tailWord_5887509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887509).length < 2 ^ (prefixWord ++ tailWord_5887509).sum := by decide
  have hdescent : baseEnd_5887509 < baseStart_5887509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887522 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_5887522 : Nat := 118140960795 + 5887522 * 2 ^ 59
def prefixEnd_5887522 : Nat := 4983230072969 + 3 ^ 40 * 5887522 * 2
def baseEnd_5887522 : Nat := 1007709549973406425599595

theorem tailTrace_5887522 : CollatzResearch.WordTrace tailWord_5887522 prefixEnd_5887522 1007709549973406425599595 := by
  unfold tailWord_5887522
  simp only [CollatzResearch.WordTrace]
  refine ⟨53683892144130194387518205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143157045717680518366715213 53683892144130194387518205)
  ·
    refine ⟨20131459554048822895319327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53683892144130194387518205 20131459554048822895319327)
    ·
      refine ⟨30197189331073234342978991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20131459554048822895319327 30197189331073234342978991)
      ·
        refine ⟨45295783996609851514468487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30197189331073234342978991 45295783996609851514468487)
        ·
          refine ⟨67943675994914777271702731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45295783996609851514468487 67943675994914777271702731)
          ·
            refine ⟨101915513992372165907554097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67943675994914777271702731 101915513992372165907554097)
            ·
              refine ⟨76436635494279124430665573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101915513992372165907554097 76436635494279124430665573)
              ·
                refine ⟨14331869155177335830749795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76436635494279124430665573 14331869155177335830749795)
                ·
                  refine ⟨21497803732766003746124693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14331869155177335830749795 21497803732766003746124693)
                  ·
                    refine ⟨1007709549973406425599595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21497803732766003746124693 1007709549973406425599595)
                    ·
                      rfl

theorem cell23_5887522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_5887522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887522 prefixEnd_5887522 := by exact prefixLift 5887522
  have htrace : WordTrace (prefixWord ++ tailWord_5887522) baseStart_5887522 baseEnd_5887522 := by
    simpa [prefixWord, tailWord_5887522, baseEnd_5887522] using wordTrace_append hprefix tailTrace_5887522
  have hstable : (prefixWord ++ tailWord_5887522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887522).length < 2 ^ (prefixWord ++ tailWord_5887522).sum := by decide
  have hdescent : baseEnd_5887522 < baseStart_5887522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887532 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 3]
def baseStart_5887532 : Nat := 118140960795 + 5887532 * 2 ^ 59
def prefixEnd_5887532 : Nat := 4983230072969 + 3 ^ 40 * 5887532 * 2
def baseEnd_5887532 : Nat := 3023133784726764237673739

theorem tailTrace_5887532 : CollatzResearch.WordTrace tailWord_5887532 prefixEnd_5887532 3023133784726764237673739 := by
  unfold tailWord_5887532
  simp only [CollatzResearch.WordTrace]
  refine ⟨107367966653242274628968425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143157288870989699505291233 107367966653242274628968425)
  ·
    refine ⟨80525974989931705971726319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107367966653242274628968425 80525974989931705971726319)
    ·
      refine ⟨120788962484897558957589479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80525974989931705971726319 120788962484897558957589479)
      ·
        refine ⟨181183443727346338436384219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120788962484897558957589479 181183443727346338436384219)
        ·
          refine ⟨271775165591019507654576329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181183443727346338436384219 271775165591019507654576329)
          ·
            refine ⟨203831374193264630740932247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271775165591019507654576329 203831374193264630740932247)
            ·
              refine ⟨305747061289896946111398371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203831374193264630740932247 305747061289896946111398371)
              ·
                refine ⟨458620591934845419167097557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305747061289896946111398371 458620591934845419167097557)
                ·
                  refine ⟨10748920123472939511728849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 458620591934845419167097557 10748920123472939511728849)
                  ·
                    refine ⟨8061690092604704633796637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10748920123472939511728849 8061690092604704633796637)
                    ·
                      refine ⟨3023133784726764237673739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8061690092604704633796637 3023133784726764237673739)
                      ·
                        rfl

theorem cell23_5887532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_5887532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887532 prefixEnd_5887532 := by exact prefixLift 5887532
  have htrace : WordTrace (prefixWord ++ tailWord_5887532) baseStart_5887532 baseEnd_5887532 := by
    simpa [prefixWord, tailWord_5887532, baseEnd_5887532] using wordTrace_append hprefix tailTrace_5887532
  have hstable : (prefixWord ++ tailWord_5887532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887532).length < 2 ^ (prefixWord ++ tailWord_5887532).sum := by decide
  have hdescent : baseEnd_5887532 < baseStart_5887532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887640 : List Nat := [2, 1, 2, 4, 1, 4, 2, 1, 1, 3, 2]
def baseStart_5887640 : Nat := 118140960795 + 5887640 * 2 ^ 59
def prefixEnd_5887640 : Nat := 4983230072969 + 3 ^ 40 * 5887640 * 2
def baseEnd_5887640 : Nat := 3023189240637449815123243

theorem tailTrace_5887640 : CollatzResearch.WordTrace tailWord_5887640 prefixEnd_5887640 3023189240637449815123243 := by
  unfold tailWord_5887640
  simp only [CollatzResearch.WordTrace]
  refine ⟨107369936195046641851434187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143159914926728855801912249 107369936195046641851434187)
  ·
    refine ⟨161054904292569962777151281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107369936195046641851434187 161054904292569962777151281)
    ·
      refine ⟨120791178219427472082863461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161054904292569962777151281 120791178219427472082863461)
      ·
        refine ⟨22648345916142651015536899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120791178219427472082863461 22648345916142651015536899)
        ·
          refine ⟨33972518874213976523305349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22648345916142651015536899 33972518874213976523305349)
          ·
            refine ⟨6369847288915120598119753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33972518874213976523305349 6369847288915120598119753)
            ·
              refine ⟨4777385466686340448589815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6369847288915120598119753 4777385466686340448589815)
              ·
                refine ⟨7166078200029510672884723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4777385466686340448589815 7166078200029510672884723)
                ·
                  refine ⟨10749117300044266009327085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7166078200029510672884723 10749117300044266009327085)
                  ·
                    refine ⟨4030918987516599753497657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10749117300044266009327085 4030918987516599753497657)
                    ·
                      refine ⟨3023189240637449815123243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030918987516599753497657 3023189240637449815123243)
                      ·
                        rfl

theorem cell23_5887640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_5887640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887640 prefixEnd_5887640 := by exact prefixLift 5887640
  have htrace : WordTrace (prefixWord ++ tailWord_5887640) baseStart_5887640 baseEnd_5887640 := by
    simpa [prefixWord, tailWord_5887640, baseEnd_5887640] using wordTrace_append hprefix tailTrace_5887640
  have hstable : (prefixWord ++ tailWord_5887640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887640).length < 2 ^ (prefixWord ++ tailWord_5887640).sum := by decide
  have hdescent : baseEnd_5887640 < baseStart_5887640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887647 : List Nat := [1, 1, 2, 7, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5887647 : Nat := 118140960795 + 5887647 * 2 ^ 59
def prefixEnd_5887647 : Nat := 4983230072969 + 3 ^ 40 * 5887647 * 2
def baseEnd_5887647 : Nat := 3023192835002031287735711

theorem tailTrace_5887647 : CollatzResearch.WordTrace tailWord_5887647 prefixEnd_5887647 3023192835002031287735711 := by
  unfold tailWord_5887647
  simp only [CollatzResearch.WordTrace]
  refine ⟨214740127701067923898373195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143160085134045282598915463 214740127701067923898373195)
  ·
    refine ⟨322110191551601885847559793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214740127701067923898373195 322110191551601885847559793)
    ·
      refine ⟨241582643663701414385669845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322110191551601885847559793 241582643663701414385669845)
      ·
        refine ⟨5662093210868001899664137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 241582643663701414385669845 5662093210868001899664137)
        ·
          refine ⟨4246569908151001424748103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5662093210868001899664137 4246569908151001424748103)
          ·
            refine ⟨6369854862226502137122155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4246569908151001424748103 6369854862226502137122155)
            ·
              refine ⟨9554782293339753205683233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6369854862226502137122155 9554782293339753205683233)
              ·
                refine ⟨7166086720004814904262425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9554782293339753205683233 7166086720004814904262425)
                ·
                  refine ⟨5374565040003611178196819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7166086720004814904262425 5374565040003611178196819)
                  ·
                    refine ⟨8061847560005416767295229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5374565040003611178196819 8061847560005416767295229)
                    ·
                      refine ⟨3023192835002031287735711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8061847560005416767295229 3023192835002031287735711)
                      ·
                        rfl

theorem cell23_5887647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5887647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887647 prefixEnd_5887647 := by exact prefixLift 5887647
  have htrace : WordTrace (prefixWord ++ tailWord_5887647) baseStart_5887647 baseEnd_5887647 := by
    simpa [prefixWord, tailWord_5887647, baseEnd_5887647] using wordTrace_append hprefix tailTrace_5887647
  have hstable : (prefixWord ++ tailWord_5887647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887647).length < 2 ^ (prefixWord ++ tailWord_5887647).sum := by decide
  have hdescent : baseEnd_5887647 < baseStart_5887647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887649 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_5887649 : Nat := 118140960795 + 5887649 * 2 ^ 59
def prefixEnd_5887649 : Nat := 4983230072969 + 3 ^ 40 * 5887649 * 2
def baseEnd_5887649 : Nat := 3023193861963340279910701

theorem tailTrace_5887649 : CollatzResearch.WordTrace tailWord_5887649 prefixEnd_5887649 3023193861963340279910701 := by
  unfold tailWord_5887649
  simp only [CollatzResearch.WordTrace]
  refine ⟨214740200647060678239946001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143160133764707118826630667 214740200647060678239946001)
  ·
    refine ⟨161055150485295508679959501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214740200647060678239946001 161055150485295508679959501)
    ·
      refine ⟨60395681431985815754984813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161055150485295508679959501 60395681431985815754984813)
      ·
        refine ⟨22648380536994680908119305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60395681431985815754984813 22648380536994680908119305)
        ·
          refine ⟨16986285402746010681089479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22648380536994680908119305 16986285402746010681089479)
          ·
            refine ⟨25479428104119016021634219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16986285402746010681089479 25479428104119016021634219)
            ·
              refine ⟨38219142156178524032451329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25479428104119016021634219 38219142156178524032451329)
              ·
                refine ⟨28664356617133893024338497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38219142156178524032451329 28664356617133893024338497)
                ·
                  refine ⟨21498267462850419768253873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28664356617133893024338497 21498267462850419768253873)
                  ·
                    refine ⟨16123700597137814826190405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21498267462850419768253873 16123700597137814826190405)
                    ·
                      refine ⟨3023193861963340279910701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16123700597137814826190405 3023193861963340279910701)
                      ·
                        rfl

theorem cell23_5887649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_5887649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887649 prefixEnd_5887649 := by exact prefixLift 5887649
  have htrace : WordTrace (prefixWord ++ tailWord_5887649) baseStart_5887649 baseEnd_5887649 := by
    simpa [prefixWord, tailWord_5887649, baseEnd_5887649] using wordTrace_append hprefix tailTrace_5887649
  have hstable : (prefixWord ++ tailWord_5887649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887649).length < 2 ^ (prefixWord ++ tailWord_5887649).sum := by decide
  have hdescent : baseEnd_5887649 < baseStart_5887649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887653 : List Nat := [1, 3, 1, 2, 1, 2, 5, 2, 2, 2, 2]
def baseStart_5887653 : Nat := 118140960795 + 5887653 * 2 ^ 59
def prefixEnd_5887653 : Nat := 4983230072969 + 3 ^ 40 * 5887653 * 2
def baseEnd_5887653 : Nat := 3023195915885958264260683

theorem tailTrace_5887653 : CollatzResearch.WordTrace tailWord_5887653 prefixEnd_5887653 3023195915885958264260683 := by
  unfold tailWord_5887653
  simp only [CollatzResearch.WordTrace]
  refine ⟨214740346539046186923091613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143160231026030791282061075 214740346539046186923091613)
  ·
    refine ⟨80527629952142320096159355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214740346539046186923091613 80527629952142320096159355)
    ·
      refine ⟨120791444928213480144239033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80527629952142320096159355 120791444928213480144239033)
      ·
        refine ⟨90593583696160110108179275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120791444928213480144239033 90593583696160110108179275)
        ·
          refine ⟨135890375544240165162268913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90593583696160110108179275 135890375544240165162268913)
          ·
            refine ⟨101917781658180123871701685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135890375544240165162268913 101917781658180123871701685)
            ·
              refine ⟨9554792030454386612972033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101917781658180123871701685 9554792030454386612972033)
              ·
                refine ⟨7166094022840789959729025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9554792030454386612972033 7166094022840789959729025)
                ·
                  refine ⟨5374570517130592469796769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7166094022840789959729025 5374570517130592469796769)
                  ·
                    refine ⟨4030927887847944352347577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5374570517130592469796769 4030927887847944352347577)
                    ·
                      refine ⟨3023195915885958264260683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030927887847944352347577 3023195915885958264260683)
                      ·
                        rfl

theorem cell23_5887653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_5887653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887653 prefixEnd_5887653 := by exact prefixLift 5887653
  have htrace : WordTrace (prefixWord ++ tailWord_5887653) baseStart_5887653 baseEnd_5887653 := by
    simpa [prefixWord, tailWord_5887653, baseEnd_5887653] using wordTrace_append hprefix tailTrace_5887653
  have hstable : (prefixWord ++ tailWord_5887653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887653).length < 2 ^ (prefixWord ++ tailWord_5887653).sum := by decide
  have hdescent : baseEnd_5887653 < baseStart_5887653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887670 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_5887670 : Nat := 118140960795 + 5887670 * 2 ^ 59
def prefixEnd_5887670 : Nat := 4983230072969 + 3 ^ 40 * 5887670 * 2
def baseEnd_5887670 : Nat := 3023204645057084697748105

theorem tailTrace_5887670 : CollatzResearch.WordTrace tailWord_5887670 prefixEnd_5887670 3023204645057084697748105 := by
  unfold tailWord_5887670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13421310411249037426653779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143160644386656399217640309 13421310411249037426653779)
  ·
    refine ⟨20131965616873556139980669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13421310411249037426653779 20131965616873556139980669)
    ·
      refine ⟨7549487106327583552492751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20131965616873556139980669 7549487106327583552492751)
      ·
        refine ⟨11324230659491375328739127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7549487106327583552492751 11324230659491375328739127)
        ·
          refine ⟨16986345989237062993108691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11324230659491375328739127 16986345989237062993108691)
          ·
            refine ⟨25479518983855594489663037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16986345989237062993108691 25479518983855594489663037)
            ·
              refine ⟨9554819618945847933623639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25479518983855594489663037 9554819618945847933623639)
              ·
                refine ⟨14332229428418771900435459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9554819618945847933623639 14332229428418771900435459)
                ·
                  refine ⟨21498344142628157850653189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14332229428418771900435459 21498344142628157850653189)
                  ·
                    refine ⟨4030939526742779596997473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21498344142628157850653189 4030939526742779596997473)
                    ·
                      refine ⟨3023204645057084697748105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030939526742779596997473 3023204645057084697748105)
                      ·
                        rfl

theorem cell23_5887670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_5887670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887670 prefixEnd_5887670 := by exact prefixLift 5887670
  have htrace : WordTrace (prefixWord ++ tailWord_5887670) baseStart_5887670 baseEnd_5887670 := by
    simpa [prefixWord, tailWord_5887670, baseEnd_5887670] using wordTrace_append hprefix tailTrace_5887670
  have hstable : (prefixWord ++ tailWord_5887670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887670).length < 2 ^ (prefixWord ++ tailWord_5887670).sum := by decide
  have hdescent : baseEnd_5887670 < baseStart_5887670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887726 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_5887726 : Nat := 118140960795 + 5887726 * 2 ^ 59
def prefixEnd_5887726 : Nat := 4983230072969 + 3 ^ 40 * 5887726 * 2
def baseEnd_5887726 : Nat := 3023233399973736478647847

theorem tailTrace_5887726 : CollatzResearch.WordTrace tailWord_5887726 prefixEnd_5887726 3023233399973736478647847 := by
  unfold tailWord_5887726
  simp only [CollatzResearch.WordTrace]
  refine ⟨26842876133472715048812379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143162006045187813593666021 26842876133472715048812379)
  ·
    refine ⟨40264314200209072573218569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26842876133472715048812379 40264314200209072573218569)
    ·
      refine ⟨30198235650156804429913927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40264314200209072573218569 30198235650156804429913927)
      ·
        refine ⟨45297353475235206644870891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30198235650156804429913927 45297353475235206644870891)
        ·
          refine ⟨67946030212852809967306337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45297353475235206644870891 67946030212852809967306337)
          ·
            refine ⟨50959522659639607475479753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67946030212852809967306337 50959522659639607475479753)
            ·
              refine ⟨38219641994729705606609815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50959522659639607475479753 38219641994729705606609815)
              ·
                refine ⟨57329462992094558409914723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38219641994729705606609815 57329462992094558409914723)
                ·
                  refine ⟨85994194488141837614872085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57329462992094558409914723 85994194488141837614872085)
                  ·
                    refine ⟨4030977866631648638197129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85994194488141837614872085 4030977866631648638197129)
                    ·
                      refine ⟨3023233399973736478647847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4030977866631648638197129 3023233399973736478647847)
                      ·
                        rfl

theorem cell23_5887726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_5887726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887726 prefixEnd_5887726 := by exact prefixLift 5887726
  have htrace : WordTrace (prefixWord ++ tailWord_5887726) baseStart_5887726 baseEnd_5887726 := by
    simpa [prefixWord, tailWord_5887726, baseEnd_5887726] using wordTrace_append hprefix tailTrace_5887726
  have hstable : (prefixWord ++ tailWord_5887726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887726).length < 2 ^ (prefixWord ++ tailWord_5887726).sum := by decide
  have hdescent : baseEnd_5887726 < baseStart_5887726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887770 : List Nat := [3, 1, 1, 3, 2, 2, 4, 2, 1, 4]
def baseStart_5887770 : Nat := 118140960795 + 5887770 * 2 ^ 59
def prefixEnd_5887770 : Nat := 4983230072969 + 3 ^ 40 * 5887770 * 2
def baseEnd_5887770 : Nat := 1007751997707511435499215

theorem tailTrace_5887770 : CollatzResearch.WordTrace tailWord_5887770 prefixEnd_5887770 1007751997707511435499215 := by
  unfold tailWord_5887770
  simp only [CollatzResearch.WordTrace]
  refine ⟨53686153469905578976275191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143163075919748210603400509 53686153469905578976275191)
  ·
    refine ⟨80529230204858368464412787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53686153469905578976275191 80529230204858368464412787)
    ·
      refine ⟨120793845307287552696619181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80529230204858368464412787 120793845307287552696619181)
      ·
        refine ⟨45297691990232832261232193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120793845307287552696619181 45297691990232832261232193)
        ·
          refine ⟨33973268992674624195924145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45297691990232832261232193 33973268992674624195924145)
          ·
            refine ⟨25479951744505968146943109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33973268992674624195924145 25479951744505968146943109)
            ·
              refine ⟨4777490952094869027551833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25479951744505968146943109 4777490952094869027551833)
              ·
                refine ⟨3583118214071151770663875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4777490952094869027551833 3583118214071151770663875)
                ·
                  refine ⟨5374677321106727655995813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583118214071151770663875 5374677321106727655995813)
                  ·
                    refine ⟨1007751997707511435499215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5374677321106727655995813 1007751997707511435499215)
                    ·
                      rfl

theorem cell23_5887770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_5887770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887770 prefixEnd_5887770 := by exact prefixLift 5887770
  have htrace : WordTrace (prefixWord ++ tailWord_5887770) baseStart_5887770 baseEnd_5887770 := by
    simpa [prefixWord, tailWord_5887770, baseEnd_5887770] using wordTrace_append hprefix tailTrace_5887770
  have hstable : (prefixWord ++ tailWord_5887770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887770).length < 2 ^ (prefixWord ++ tailWord_5887770).sum := by decide
  have hdescent : baseEnd_5887770 < baseStart_5887770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887779 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 3, 5]
def baseStart_5887779 : Nat := 118140960795 + 5887779 * 2 ^ 59
def prefixEnd_5887779 : Nat := 4983230072969 + 3 ^ 40 * 5887779 * 2
def baseEnd_5887779 : Nat := 1007753538149474923761701

theorem tailTrace_5887779 : CollatzResearch.WordTrace tailWord_5887779 prefixEnd_5887779 1007753538149474923761701 := by
  unfold tailWord_5887779
  simp only [CollatzResearch.WordTrace]
  refine ⟨214744942136589710442178391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143163294757726473628118927 214744942136589710442178391)
  ·
    refine ⟨322117413204884565663267587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214744942136589710442178391 322117413204884565663267587)
    ·
      refine ⟨483176119807326848494901381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322117413204884565663267587 483176119807326848494901381)
      ·
        refine ⟨90595522463873784092794009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 483176119807326848494901381 90595522463873784092794009)
        ·
          refine ⟨67946641847905338069595507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90595522463873784092794009 67946641847905338069595507)
          ·
            refine ⟨101919962771858007104393261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67946641847905338069595507 101919962771858007104393261)
            ·
              refine ⟨38219986039446752664147473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101919962771858007104393261 38219986039446752664147473)
              ·
                refine ⟨28664989529585064498110605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38219986039446752664147473 28664989529585064498110605)
                ·
                  refine ⟨10749371073594399186791477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28664989529585064498110605 10749371073594399186791477)
                  ·
                    refine ⟨1007753538149474923761701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10749371073594399186791477 1007753538149474923761701)
                    ·
                      rfl

theorem cell23_5887779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 5].length) (baseStart_5887779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887779 prefixEnd_5887779 := by exact prefixLift 5887779
  have htrace : WordTrace (prefixWord ++ tailWord_5887779) baseStart_5887779 baseEnd_5887779 := by
    simpa [prefixWord, tailWord_5887779, baseEnd_5887779] using wordTrace_append hprefix tailTrace_5887779
  have hstable : (prefixWord ++ tailWord_5887779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887779).length < 2 ^ (prefixWord ++ tailWord_5887779).sum := by decide
  have hdescent : baseEnd_5887779 < baseStart_5887779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887793 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 3, 1, 3]
def baseStart_5887793 : Nat := 118140960795 + 5887793 * 2 ^ 59
def prefixEnd_5887793 : Nat := 4983230072969 + 3 ^ 40 * 5887793 * 2
def baseEnd_5887793 : Nat := 3023267803177587716510039

theorem tailTrace_5887793 : CollatzResearch.WordTrace tailWord_5887793 prefixEnd_5887793 3023267803177587716510039 := by
  unfold tailWord_5887793
  simp only [CollatzResearch.WordTrace]
  refine ⟨214745452758538990833188033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143163635172359327222125355 214745452758538990833188033)
  ·
    refine ⟨161059089568904243124891025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214745452758538990833188033 161059089568904243124891025)
    ·
      refine ⟨120794317176678182343668269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161059089568904243124891025 120794317176678182343668269)
      ·
        refine ⟨45297868941254318378875601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120794317176678182343668269 45297868941254318378875601)
        ·
          refine ⟨33973401705940738784156701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45297868941254318378875601 33973401705940738784156701)
          ·
            refine ⟨12740025639727777044058763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33973401705940738784156701 12740025639727777044058763)
            ·
              refine ⟨19110038459591665566088145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12740025639727777044058763 19110038459591665566088145)
              ·
                refine ⟨14332528844693749174566109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19110038459591665566088145 14332528844693749174566109)
                ·
                  refine ⟨5374698316760155940462291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14332528844693749174566109 5374698316760155940462291)
                  ·
                    refine ⟨8062047475140233910693437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5374698316760155940462291 8062047475140233910693437)
                    ·
                      refine ⟨3023267803177587716510039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8062047475140233910693437 3023267803177587716510039)
                      ·
                        rfl

theorem cell23_5887793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_5887793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887793 prefixEnd_5887793 := by exact prefixLift 5887793
  have htrace : WordTrace (prefixWord ++ tailWord_5887793) baseStart_5887793 baseEnd_5887793 := by
    simpa [prefixWord, tailWord_5887793, baseEnd_5887793] using wordTrace_append hprefix tailTrace_5887793
  have hstable : (prefixWord ++ tailWord_5887793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887793).length < 2 ^ (prefixWord ++ tailWord_5887793).sum := by decide
  have hdescent : baseEnd_5887793 < baseStart_5887793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887843 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 1, 6]
def baseStart_5887843 : Nat := 118140960795 + 5887843 * 2 ^ 59
def prefixEnd_5887843 : Nat := 4983230072969 + 3 ^ 40 * 5887843 * 2
def baseEnd_5887843 : Nat := 1007764492403437506961603

theorem tailTrace_5887843 : CollatzResearch.WordTrace tailWord_5887843 prefixEnd_5887843 1007764492403437506961603 := by
  unfold tailWord_5887843
  simp only [CollatzResearch.WordTrace]
  refine ⟨214747276408357849372508183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143164850938905232915005455 214747276408357849372508183)
  ·
    refine ⟨322120914612536774058762275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214747276408357849372508183 322120914612536774058762275)
    ·
      refine ⟨483181371918805161088143413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322120914612536774058762275 483181371918805161088143413)
      ·
        refine ⟨45298253617387983852013445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 483181371918805161088143413 45298253617387983852013445)
        ·
          refine ⟨8493422553260246972252521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45298253617387983852013445 8493422553260246972252521)
          ·
            refine ⟨6370066914945185229189391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8493422553260246972252521 6370066914945185229189391)
            ·
              refine ⟨9555100372417777843784087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6370066914945185229189391 9555100372417777843784087)
              ·
                refine ⟨14332650558626666765676131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9555100372417777843784087 14332650558626666765676131)
                ·
                  refine ⟨21498975837940000148514197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14332650558626666765676131 21498975837940000148514197)
                  ·
                    refine ⟨1007764492403437506961603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21498975837940000148514197 1007764492403437506961603)
                    ·
                      rfl

theorem cell23_5887843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 6].length) (baseStart_5887843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887843 prefixEnd_5887843 := by exact prefixLift 5887843
  have htrace : WordTrace (prefixWord ++ tailWord_5887843) baseStart_5887843 baseEnd_5887843 := by
    simpa [prefixWord, tailWord_5887843, baseEnd_5887843] using wordTrace_append hprefix tailTrace_5887843
  have hstable : (prefixWord ++ tailWord_5887843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887843).length < 2 ^ (prefixWord ++ tailWord_5887843).sum := by decide
  have hdescent : baseEnd_5887843 < baseStart_5887843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887853 : List Nat := [1, 5, 1, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_5887853 : Nat := 118140960795 + 5887853 * 2 ^ 59
def prefixEnd_5887853 : Nat := 4983230072969 + 3 ^ 40 * 5887853 * 2
def baseEnd_5887853 : Nat := 3023298612016857481759763

theorem tailTrace_5887853 : CollatzResearch.WordTrace tailWord_5887853 prefixEnd_5887853 3023298612016857481759763 := by
  unfold tailWord_5887853
  simp only [CollatzResearch.WordTrace]
  refine ⟨214747641138321621080372213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143165094092214414053581475 214747641138321621080372213)
  ·
    refine ⟨20132591356717651976284895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214747641138321621080372213 20132591356717651976284895)
    ·
      refine ⟨30198887035076477964427343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20132591356717651976284895 30198887035076477964427343)
      ·
        refine ⟨45298330552614716946641015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30198887035076477964427343 45298330552614716946641015)
        ·
          refine ⟨67947495828922075419961523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45298330552614716946641015 67947495828922075419961523)
          ·
            refine ⟨101921243743383113129942285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67947495828922075419961523 101921243743383113129942285)
            ·
              refine ⟨38220466403768667423728357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101921243743383113129942285 38220466403768667423728357)
              ·
                refine ⟨7166337450706625141949067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38220466403768667423728357 7166337450706625141949067)
                ·
                  refine ⟨10749506176059937712923601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7166337450706625141949067 10749506176059937712923601)
                  ·
                    refine ⟨8062129632044953284692701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10749506176059937712923601 8062129632044953284692701)
                    ·
                      refine ⟨3023298612016857481759763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8062129632044953284692701 3023298612016857481759763)
                      ·
                        rfl

theorem cell23_5887853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_5887853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887853 prefixEnd_5887853 := by exact prefixLift 5887853
  have htrace : WordTrace (prefixWord ++ tailWord_5887853) baseStart_5887853 baseEnd_5887853 := by
    simpa [prefixWord, tailWord_5887853, baseEnd_5887853] using wordTrace_append hprefix tailTrace_5887853
  have hstable : (prefixWord ++ tailWord_5887853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887853).length < 2 ^ (prefixWord ++ tailWord_5887853).sum := by decide
  have hdescent : baseEnd_5887853 < baseStart_5887853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887866 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3]
def baseStart_5887866 : Nat := 118140960795 + 5887866 * 2 ^ 59
def prefixEnd_5887866 : Nat := 4983230072969 + 3 ^ 40 * 5887866 * 2
def baseEnd_5887866 : Nat := 3023305287265365930897203

theorem tailTrace_5887866 : CollatzResearch.WordTrace tailWord_5887866 prefixEnd_5887866 3023305287265365930897203 := by
  unfold tailWord_5887866
  simp only [CollatzResearch.WordTrace]
  refine ⟨53687028821818631075148863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143165410191516349533730301 53687028821818631075148863)
  ·
    refine ⟨80530543232727946612723295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53687028821818631075148863 80530543232727946612723295)
    ·
      refine ⟨120795814849091919919084943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80530543232727946612723295 120795814849091919919084943)
      ·
        refine ⟨181193722273637879878627415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120795814849091919919084943 181193722273637879878627415)
        ·
          refine ⟨271790583410456819817941123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181193722273637879878627415 271790583410456819817941123)
          ·
            refine ⟨407685875115685229726911685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271790583410456819817941123 407685875115685229726911685)
            ·
              refine ⟨76441101584190980573795941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 407685875115685229726911685 76441101584190980573795941)
              ·
                refine ⟨14332706547035808857586739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76441101584190980573795941 14332706547035808857586739)
                ·
                  refine ⟨21499059820553713286380109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14332706547035808857586739 21499059820553713286380109)
                  ·
                    refine ⟨8062147432707642482392541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21499059820553713286380109 8062147432707642482392541)
                    ·
                      refine ⟨3023305287265365930897203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8062147432707642482392541 3023305287265365930897203)
                      ·
                        rfl

theorem cell23_5887866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_5887866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887866 prefixEnd_5887866 := by exact prefixLift 5887866
  have htrace : WordTrace (prefixWord ++ tailWord_5887866) baseStart_5887866 baseEnd_5887866 := by
    simpa [prefixWord, tailWord_5887866, baseEnd_5887866] using wordTrace_append hprefix tailTrace_5887866
  have hstable : (prefixWord ++ tailWord_5887866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887866).length < 2 ^ (prefixWord ++ tailWord_5887866).sum := by decide
  have hdescent : baseEnd_5887866 < baseStart_5887866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887869 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_5887869 : Nat := 118140960795 + 5887869 * 2 ^ 59
def prefixEnd_5887869 : Nat := 4983230072969 + 3 ^ 40 * 5887869 * 2
def baseEnd_5887869 : Nat := 1007768942569109806386563

theorem tailTrace_5887869 : CollatzResearch.WordTrace tailWord_5887869 prefixEnd_5887869 1007768942569109806386563 := by
  unfold tailWord_5887869
  simp only [CollatzResearch.WordTrace]
  refine ⟨214748224706263655812954661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143165483137509103875303107 214748224706263655812954661)
  ·
    refine ⟨40265292132424435464928999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214748224706263655812954661 40265292132424435464928999)
    ·
      refine ⟨60397938198636653197393499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40265292132424435464928999 60397938198636653197393499)
      ·
        refine ⟨90596907297954979796090249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60397938198636653197393499 90596907297954979796090249)
        ·
          refine ⟨67947680473466234847067687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90596907297954979796090249 67947680473466234847067687)
          ·
            refine ⟨101921520710199352270601531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67947680473466234847067687 101921520710199352270601531)
            ·
              refine ⟨152882281065299028405902297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101921520710199352270601531 152882281065299028405902297)
              ·
                refine ⟨114661710798974271304426723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152882281065299028405902297 114661710798974271304426723)
                ·
                  refine ⟨171992566198461406956640085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114661710798974271304426723 171992566198461406956640085)
                  ·
                    refine ⟨1007768942569109806386563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 171992566198461406956640085 1007768942569109806386563)
                    ·
                      rfl

theorem cell23_5887869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_5887869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887869 prefixEnd_5887869 := by exact prefixLift 5887869
  have htrace : WordTrace (prefixWord ++ tailWord_5887869) baseStart_5887869 baseEnd_5887869 := by
    simpa [prefixWord, tailWord_5887869, baseEnd_5887869] using wordTrace_append hprefix tailTrace_5887869
  have hstable : (prefixWord ++ tailWord_5887869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887869).length < 2 ^ (prefixWord ++ tailWord_5887869).sum := by decide
  have hdescent : baseEnd_5887869 < baseStart_5887869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887870 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5887870 : Nat := 118140960795 + 5887870 * 2 ^ 59
def prefixEnd_5887870 : Nat := 4983230072969 + 3 ^ 40 * 5887870 * 2
def baseEnd_5887870 : Nat := 3023307341187983915247185

theorem tailTrace_5887870 : CollatzResearch.WordTrace tailWord_5887870 prefixEnd_5887870 3023307341187983915247185 := by
  unfold tailWord_5887870
  simp only [CollatzResearch.WordTrace]
  refine ⟨26843532647407504122967633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143165507452840021989160709 26843532647407504122967633)
  ·
    refine ⟨20132649485555628092225725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26843532647407504122967633 20132649485555628092225725)
    ·
      refine ⟨7549743557083360534584647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20132649485555628092225725 7549743557083360534584647)
      ·
        refine ⟨11324615335625040801876971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7549743557083360534584647 11324615335625040801876971)
        ·
          refine ⟨16986923003437561202815457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11324615335625040801876971 16986923003437561202815457)
          ·
            refine ⟨12740192252578170902111593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16986923003437561202815457 12740192252578170902111593)
            ·
              refine ⟨9555144189433628176583695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12740192252578170902111593 9555144189433628176583695)
              ·
                refine ⟨14332716284150442264875543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9555144189433628176583695 14332716284150442264875543)
                ·
                  refine ⟨21499074426225663397313315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14332716284150442264875543 21499074426225663397313315)
                  ·
                    refine ⟨32248611639338495095969973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21499074426225663397313315 32248611639338495095969973)
                    ·
                      refine ⟨3023307341187983915247185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32248611639338495095969973 3023307341187983915247185)
                      ·
                        rfl

theorem cell23_5887870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5887870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887870 prefixEnd_5887870 := by exact prefixLift 5887870
  have htrace : WordTrace (prefixWord ++ tailWord_5887870) baseStart_5887870 baseEnd_5887870 := by
    simpa [prefixWord, tailWord_5887870, baseEnd_5887870] using wordTrace_append hprefix tailTrace_5887870
  have hstable : (prefixWord ++ tailWord_5887870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887870).length < 2 ^ (prefixWord ++ tailWord_5887870).sum := by decide
  have hdescent : baseEnd_5887870 < baseStart_5887870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887873 : List Nat := [1, 2, 4, 4, 1, 2, 9]
def baseStart_5887873 : Nat := 118140960795 + 5887873 * 2 ^ 59
def prefixEnd_5887873 : Nat := 4983230072969 + 3 ^ 40 * 5887873 * 2
def baseEnd_5887873 : Nat := 37324801007777128438391

theorem tailTrace_5887873 : CollatzResearch.WordTrace tailWord_5887873 prefixEnd_5887873 37324801007777128438391 := by
  unfold tailWord_5887873
  simp only [CollatzResearch.WordTrace]
  refine ⟨214748370598249164496100273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143165580398832776330733515 214748370598249164496100273)
  ·
    refine ⟨161061277948686873372075205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214748370598249164496100273 161061277948686873372075205)
    ·
      refine ⟨30198989615378788757264101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161061277948686873372075205 30198989615378788757264101)
      ·
        refine ⟨5662310552883522891987019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30198989615378788757264101 5662310552883522891987019)
        ·
          refine ⟨8493465829325284337980529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662310552883522891987019 8493465829325284337980529)
          ·
            refine ⟨6370099371993963253485397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8493465829325284337980529 6370099371993963253485397)
            ·
              refine ⟨37324801007777128438391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6370099371993963253485397 37324801007777128438391)
              ·
                rfl

theorem cell23_5887873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 9].length) (baseStart_5887873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887873 prefixEnd_5887873 := by exact prefixLift 5887873
  have htrace : WordTrace (prefixWord ++ tailWord_5887873) baseStart_5887873 baseEnd_5887873 := by
    simpa [prefixWord, tailWord_5887873, baseEnd_5887873] using wordTrace_append hprefix tailTrace_5887873
  have hstable : (prefixWord ++ tailWord_5887873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887873).length < 2 ^ (prefixWord ++ tailWord_5887873).sum := by decide
  have hdescent : baseEnd_5887873 < baseStart_5887873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887883 : List Nat := [1, 1, 1, 1, 4, 2, 1, 6, 2, 1, 3]
def baseStart_5887883 : Nat := 118140960795 + 5887883 * 2 ^ 59
def prefixEnd_5887883 : Nat := 4983230072969 + 3 ^ 40 * 5887883 * 2
def baseEnd_5887883 : Nat := 3023314016436492364384625

theorem tailTrace_5887883 : CollatzResearch.WordTrace tailWord_5887883 prefixEnd_5887883 3023314016436492364384625 := by
  unfold tailWord_5887883
  simp only [CollatzResearch.WordTrace]
  refine ⟨214748735328212936203964303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143165823552141957469309535 214748735328212936203964303)
  ·
    refine ⟨322123102992319404305946455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214748735328212936203964303 322123102992319404305946455)
    ·
      refine ⟨483184654488479106458919683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322123102992319404305946455 483184654488479106458919683)
      ·
        refine ⟨724776981732718659688379525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483184654488479106458919683 724776981732718659688379525)
        ·
          refine ⟨135895684074884748691571161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 724776981732718659688379525 135895684074884748691571161)
          ·
            refine ⟨101921763056163561518678371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135895684074884748691571161 101921763056163561518678371)
            ·
              refine ⟨152882644584245342278017557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101921763056163561518678371 152882644584245342278017557)
              ·
                refine ⟨7166373964886500419282073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 152882644584245342278017557 7166373964886500419282073)
                ·
                  refine ⟨5374780473664875314461555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7166373964886500419282073 5374780473664875314461555)
                  ·
                    refine ⟨8062170710497312971692333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5374780473664875314461555 8062170710497312971692333)
                    ·
                      refine ⟨3023314016436492364384625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8062170710497312971692333 3023314016436492364384625)
                      ·
                        rfl

theorem cell23_5887883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 1, 3].length) (baseStart_5887883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887883 prefixEnd_5887883 := by exact prefixLift 5887883
  have htrace : WordTrace (prefixWord ++ tailWord_5887883) baseStart_5887883 baseEnd_5887883 := by
    simpa [prefixWord, tailWord_5887883, baseEnd_5887883] using wordTrace_append hprefix tailTrace_5887883
  have hstable : (prefixWord ++ tailWord_5887883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887883).length < 2 ^ (prefixWord ++ tailWord_5887883).sum := by decide
  have hdescent : baseEnd_5887883 < baseStart_5887883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887893 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 3, 3, 2]
def baseStart_5887893 : Nat := 118140960795 + 5887893 * 2 ^ 59
def prefixEnd_5887893 : Nat := 4983230072969 + 3 ^ 40 * 5887893 * 2
def baseEnd_5887893 : Nat := 3023319151243037325259579

theorem tailTrace_5887893 : CollatzResearch.WordTrace tailWord_5887893 prefixEnd_5887893 3023319151243037325259579 := by
  unfold tailWord_5887893
  simp only [CollatzResearch.WordTrace]
  refine ⟨214749100058176707911828333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143166066705451138607885555 214749100058176707911828333)
  ·
    refine ⟨80530912521816265466935625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214749100058176707911828333 80530912521816265466935625)
    ·
      refine ⟨60398184391362199100201719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80530912521816265466935625 60398184391362199100201719)
      ·
        refine ⟨90597276587043298650302579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60398184391362199100201719 90597276587043298650302579)
        ·
          refine ⟨135895914880564947975453869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90597276587043298650302579 135895914880564947975453869)
          ·
            refine ⟨50960968080211855490795201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135895914880564947975453869 50960968080211855490795201)
            ·
              refine ⟨38220726060158891618096401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50960968080211855490795201 38220726060158891618096401)
              ·
                refine ⟨28665544545119168713572301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38220726060158891618096401 28665544545119168713572301)
                ·
                  refine ⟨10749579204419688267589613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28665544545119168713572301 10749579204419688267589613)
                  ·
                    refine ⟨4031092201657383100346105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10749579204419688267589613 4031092201657383100346105)
                    ·
                      refine ⟨3023319151243037325259579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031092201657383100346105 3023319151243037325259579)
                      ·
                        rfl

theorem cell23_5887893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_5887893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887893 prefixEnd_5887893 := by exact prefixLift 5887893
  have htrace : WordTrace (prefixWord ++ tailWord_5887893) baseStart_5887893 baseEnd_5887893 := by
    simpa [prefixWord, tailWord_5887893, baseEnd_5887893] using wordTrace_append hprefix tailTrace_5887893
  have hstable : (prefixWord ++ tailWord_5887893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887893).length < 2 ^ (prefixWord ++ tailWord_5887893).sum := by decide
  have hdescent : baseEnd_5887893 < baseStart_5887893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887894 : List Nat := [5, 3, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_5887894 : Nat := 118140960795 + 5887894 * 2 ^ 59
def prefixEnd_5887894 : Nat := 4983230072969 + 3 ^ 40 * 5887894 * 2
def baseEnd_5887894 : Nat := 1007773221574563940449025

theorem tailTrace_5887894 : CollatzResearch.WordTrace tailWord_5887894 prefixEnd_5887894 1007773221574563940449025 := by
  unfold tailWord_5887894
  simp only [CollatzResearch.WordTrace]
  refine ⟨13421821033198317817663421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143166091020782056721743157 13421821033198317817663421)
  ·
    refine ⟨5033182887449369181623783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13421821033198317817663421 5033182887449369181623783)
    ·
      refine ⟨7549774331174053772435675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5033182887449369181623783 7549774331174053772435675)
      ·
        refine ⟨11324661496761080658653513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7549774331174053772435675 11324661496761080658653513)
        ·
          refine ⟨8493496122570810493990135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11324661496761080658653513 8493496122570810493990135)
          ·
            refine ⟨12740244183856215740985203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8493496122570810493990135 12740244183856215740985203)
            ·
              refine ⟨19110366275784323611477805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12740244183856215740985203 19110366275784323611477805)
              ·
                refine ⟨7166387353419121354304177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19110366275784323611477805 7166387353419121354304177)
                ·
                  refine ⟨5374790515064341015728133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7166387353419121354304177 5374790515064341015728133)
                  ·
                    refine ⟨1007773221574563940449025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5374790515064341015728133 1007773221574563940449025)
                    ·
                      rfl

theorem cell23_5887894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_5887894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887894 prefixEnd_5887894 := by exact prefixLift 5887894
  have htrace : WordTrace (prefixWord ++ tailWord_5887894) baseStart_5887894 baseEnd_5887894 := by
    simpa [prefixWord, tailWord_5887894, baseEnd_5887894] using wordTrace_append hprefix tailTrace_5887894
  have hstable : (prefixWord ++ tailWord_5887894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887894).length < 2 ^ (prefixWord ++ tailWord_5887894).sum := by decide
  have hdescent : baseEnd_5887894 < baseStart_5887894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887923 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 1, 4, 2]
def baseStart_5887923 : Nat := 118140960795 + 5887923 * 2 ^ 59
def prefixEnd_5887923 : Nat := 4983230072969 + 3 ^ 40 * 5887923 * 2
def baseEnd_5887923 : Nat := 3023334555662672207884441

theorem tailTrace_5887923 : CollatzResearch.WordTrace tailWord_5887923 prefixEnd_5887923 3023334555662672207884441 := by
  unfold tailWord_5887923
  simp only [CollatzResearch.WordTrace]
  refine ⟨214750194248068023035420423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143166796165378682023613615 214750194248068023035420423)
  ·
    refine ⟨322125291372102034553130635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214750194248068023035420423 322125291372102034553130635)
    ·
      refine ⟨483187937058153051829695953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322125291372102034553130635 483187937058153051829695953)
      ·
        refine ⟨362390952793614788872271965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483187937058153051829695953 362390952793614788872271965)
        ·
          refine ⟨135896607297605545827101987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362390952793614788872271965 135896607297605545827101987)
          ·
            refine ⟨203844910946408318740652981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135896607297605545827101987 203844910946408318740652981)
            ·
              refine ⟨19110460401225779881936217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203844910946408318740652981 19110460401225779881936217)
              ·
                refine ⟨14332845300919334911452163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19110460401225779881936217 14332845300919334911452163)
                ·
                  refine ⟨21499267951379002367178245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14332845300919334911452163 21499267951379002367178245)
                  ·
                    refine ⟨4031112740883562943845921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21499267951379002367178245 4031112740883562943845921)
                    ·
                      refine ⟨3023334555662672207884441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031112740883562943845921 3023334555662672207884441)
                      ·
                        rfl

theorem cell23_5887923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 4, 2].length) (baseStart_5887923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887923 prefixEnd_5887923 := by exact prefixLift 5887923
  have htrace : WordTrace (prefixWord ++ tailWord_5887923) baseStart_5887923 baseEnd_5887923 := by
    simpa [prefixWord, tailWord_5887923, baseEnd_5887923] using wordTrace_append hprefix tailTrace_5887923
  have hstable : (prefixWord ++ tailWord_5887923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887923).length < 2 ^ (prefixWord ++ tailWord_5887923).sum := by decide
  have hdescent : baseEnd_5887923 < baseStart_5887923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887936 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 4]
def baseStart_5887936 : Nat := 118140960795 + 5887936 * 2 ^ 59
def prefixEnd_5887936 : Nat := 4983230072969 + 3 ^ 40 * 5887936 * 2
def baseEnd_5887936 : Nat := 3023341230911180657021881

theorem tailTrace_5887936 : CollatzResearch.WordTrace tailWord_5887936 prefixEnd_5887936 3023341230911180657021881 := by
  unfold tailWord_5887936
  simp only [CollatzResearch.WordTrace]
  refine ⟨107375334198510463127821831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143167112264680617503762441 107375334198510463127821831)
  ·
    refine ⟨161063001297765694691732747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107375334198510463127821831 161063001297765694691732747)
    ·
      refine ⟨241594501946648542037599121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161063001297765694691732747 241594501946648542037599121)
      ·
        refine ⟨181195876459986406528199341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241594501946648542037599121 181195876459986406528199341)
        ·
          refine ⟨67948453672494902448074753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181195876459986406528199341 67948453672494902448074753)
          ·
            refine ⟨50961340254371176836056065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67948453672494902448074753 50961340254371176836056065)
            ·
              refine ⟨38221005190778382627042049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50961340254371176836056065 38221005190778382627042049)
              ·
                refine ⟨28665753893083786970281537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38221005190778382627042049 28665753893083786970281537)
                ·
                  refine ⟨21499315419812840227711153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28665753893083786970281537 21499315419812840227711153)
                  ·
                    refine ⟨16124486564859630170783365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21499315419812840227711153 16124486564859630170783365)
                    ·
                      refine ⟨3023341230911180657021881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16124486564859630170783365 3023341230911180657021881)
                      ·
                        rfl

theorem cell23_5887936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_5887936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887936 prefixEnd_5887936 := by exact prefixLift 5887936
  have htrace : WordTrace (prefixWord ++ tailWord_5887936) baseStart_5887936 baseEnd_5887936 := by
    simpa [prefixWord, tailWord_5887936, baseEnd_5887936] using wordTrace_append hprefix tailTrace_5887936
  have hstable : (prefixWord ++ tailWord_5887936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887936).length < 2 ^ (prefixWord ++ tailWord_5887936).sum := by decide
  have hdescent : baseEnd_5887936 < baseStart_5887936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5887957 : List Nat := [1, 3, 2, 3, 2, 1, 2, 3, 2, 2, 2]
def baseStart_5887957 : Nat := 118140960795 + 5887957 * 2 ^ 59
def prefixEnd_5887957 : Nat := 4983230072969 + 3 ^ 40 * 5887957 * 2
def baseEnd_5887957 : Nat := 3023352014004925074859285

theorem tailTrace_5887957 : CollatzResearch.WordTrace tailWord_5887957 prefixEnd_5887957 3023352014004925074859285 := by
  unfold tailWord_5887957
  simp only [CollatzResearch.WordTrace]
  refine ⟨214751434329944846842158125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143167622886629897894772083 214751434329944846842158125)
  ·
    refine ⟨80531787873729317565809297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214751434329944846842158125 80531787873729317565809297)
    ·
      refine ⟨60398840905296988174356973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80531787873729317565809297 60398840905296988174356973)
      ·
        refine ⟨22649565339486370565383865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60398840905296988174356973 22649565339486370565383865)
        ·
          refine ⟨16987174004614777924037899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22649565339486370565383865 16987174004614777924037899)
          ·
            refine ⟨25480761006922166886056849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16987174004614777924037899 25480761006922166886056849)
            ·
              refine ⟨19110570755191625164542637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25480761006922166886056849 19110570755191625164542637)
              ·
                refine ⟨7166464033196859436703489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19110570755191625164542637 7166464033196859436703489)
                ·
                  refine ⟨5374848024897644577527617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7166464033196859436703489 5374848024897644577527617)
                  ·
                    refine ⟨4031136018673233433145713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5374848024897644577527617 4031136018673233433145713)
                    ·
                      refine ⟨3023352014004925074859285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031136018673233433145713 3023352014004925074859285)
                      ·
                        rfl

theorem cell23_5887957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_5887957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5887957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5887957 prefixEnd_5887957 := by exact prefixLift 5887957
  have htrace : WordTrace (prefixWord ++ tailWord_5887957) baseStart_5887957 baseEnd_5887957 := by
    simpa [prefixWord, tailWord_5887957, baseEnd_5887957] using wordTrace_append hprefix tailTrace_5887957
  have hstable : (prefixWord ++ tailWord_5887957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5887957).length < 2 ^ (prefixWord ++ tailWord_5887957).sum := by decide
  have hdescent : baseEnd_5887957 < baseStart_5887957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5887957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888050 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_5888050 : Nat := 118140960795 + 5888050 * 2 ^ 59
def prefixEnd_5888050 : Nat := 4983230072969 + 3 ^ 40 * 5888050 * 2
def baseEnd_5888050 : Nat := 3023399767705793210996357

theorem tailTrace_5888050 : CollatzResearch.WordTrace tailWord_5888050 prefixEnd_5888050 3023399767705793210996357 := by
  unfold tailWord_5888050
  simp only [CollatzResearch.WordTrace]
  refine ⟨53688706579651980931323401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143169884212405282483529069 53688706579651980931323401)
  ·
    refine ⟨40266529934738985698492551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53688706579651980931323401 40266529934738985698492551)
    ·
      refine ⟨60399794902108478547738827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40266529934738985698492551 60399794902108478547738827)
      ·
        refine ⟨90599692353162717821608241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60399794902108478547738827 90599692353162717821608241)
        ·
          refine ⟨67949769264872038366206181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90599692353162717821608241 67949769264872038366206181)
          ·
            refine ⟨12740581737163507193663659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67949769264872038366206181 12740581737163507193663659)
            ·
              refine ⟨19110872605745260790495489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12740581737163507193663659 19110872605745260790495489)
              ·
                refine ⟨14333154454308945592871617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19110872605745260790495489 14333154454308945592871617)
                ·
                  refine ⟨10749865840731709194653713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14333154454308945592871617 10749865840731709194653713)
                  ·
                    refine ⟨8062399380548781895990285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10749865840731709194653713 8062399380548781895990285)
                    ·
                      refine ⟨3023399767705793210996357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8062399380548781895990285 3023399767705793210996357)
                      ·
                        rfl

theorem cell23_5888050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_5888050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888050 prefixEnd_5888050 := by exact prefixLift 5888050
  have htrace : WordTrace (prefixWord ++ tailWord_5888050) baseStart_5888050 baseEnd_5888050 := by
    simpa [prefixWord, tailWord_5888050, baseEnd_5888050] using wordTrace_append hprefix tailTrace_5888050
  have hstable : (prefixWord ++ tailWord_5888050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888050).length < 2 ^ (prefixWord ++ tailWord_5888050).sum := by decide
  have hdescent : baseEnd_5888050 < baseStart_5888050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888057 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 3, 4]
def baseStart_5888057 : Nat := 118140960795 + 5888057 * 2 ^ 59
def prefixEnd_5888057 : Nat := 4983230072969 + 3 ^ 40 * 5888057 * 2
def baseEnd_5888057 : Nat := 1007801120690124894536275

theorem tailTrace_5888057 : CollatzResearch.WordTrace tailWord_5888057 prefixEnd_5888057 1007801120690124894536275 := by
  unfold tailWord_5888057
  simp only [CollatzResearch.WordTrace]
  refine ⟨214755081629582563920798425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143170054419721709280532283 214755081629582563920798425)
  ·
    refine ⟨161066311222186922940598819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214755081629582563920798425 161066311222186922940598819)
    ·
      refine ⟨241599466833280384410898229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161066311222186922940598819 241599466833280384410898229)
      ·
        refine ⟨22649950015620036038521709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241599466833280384410898229 22649950015620036038521709)
        ·
          refine ⟨8493731255857513514445641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22649950015620036038521709 8493731255857513514445641)
          ·
            refine ⟨6370298441893135135834231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8493731255857513514445641 6370298441893135135834231)
            ·
              refine ⟨9555447662839702703751347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6370298441893135135834231 9555447662839702703751347)
              ·
                refine ⟨14333171494259554055627021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9555447662839702703751347 14333171494259554055627021)
                ·
                  refine ⟨5374939310347332770860133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14333171494259554055627021 5374939310347332770860133)
                  ·
                    refine ⟨1007801120690124894536275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5374939310347332770860133 1007801120690124894536275)
                    ·
                      rfl

theorem cell23_5888057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 4].length) (baseStart_5888057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888057 prefixEnd_5888057 := by exact prefixLift 5888057
  have htrace : WordTrace (prefixWord ++ tailWord_5888057) baseStart_5888057 baseEnd_5888057 := by
    simpa [prefixWord, tailWord_5888057, baseEnd_5888057] using wordTrace_append hprefix tailTrace_5888057
  have hstable : (prefixWord ++ tailWord_5888057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888057).length < 2 ^ (prefixWord ++ tailWord_5888057).sum := by decide
  have hdescent : baseEnd_5888057 < baseStart_5888057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888097 : List Nat := [1, 2, 3, 1, 1, 2, 1, 7, 1, 1, 3]
def baseStart_5888097 : Nat := 118140960795 + 5888097 * 2 ^ 59
def prefixEnd_5888097 : Nat := 4983230072969 + 3 ^ 40 * 5888097 * 2
def baseEnd_5888097 : Nat := 3023423901296554527108641

theorem tailTrace_5888097 : CollatzResearch.WordTrace tailWord_5888097 prefixEnd_5888097 3023423901296554527108641 := by
  unfold tailWord_5888097
  simp only [CollatzResearch.WordTrace]
  refine ⟨214756540549437650752254545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143171027032958433834836363 214756540549437650752254545)
  ·
    refine ⟨161067405412078238064190909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214756540549437650752254545 161067405412078238064190909)
    ·
      refine ⟨60400277029529339274071591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161067405412078238064190909 60400277029529339274071591)
      ·
        refine ⟨90600415544294008911107387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60400277029529339274071591 90600415544294008911107387)
        ·
          refine ⟨135900623316441013366661081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90600415544294008911107387 135900623316441013366661081)
          ·
            refine ⟨101925467487330760024995811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135900623316441013366661081 101925467487330760024995811)
            ·
              refine ⟨152888201230996140037493717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101925467487330760024995811 152888201230996140037493717)
              ·
                refine ⟨3583317216351472032128759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 152888201230996140037493717 3583317216351472032128759)
                ·
                  refine ⟨5374975824527208048193139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583317216351472032128759 5374975824527208048193139)
                  ·
                    refine ⟨8062463736790812072289709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5374975824527208048193139 8062463736790812072289709)
                    ·
                      refine ⟨3023423901296554527108641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8062463736790812072289709 3023423901296554527108641)
                      ·
                        rfl

theorem cell23_5888097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_5888097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888097 prefixEnd_5888097 := by exact prefixLift 5888097
  have htrace : WordTrace (prefixWord ++ tailWord_5888097) baseStart_5888097 baseEnd_5888097 := by
    simpa [prefixWord, tailWord_5888097, baseEnd_5888097] using wordTrace_append hprefix tailTrace_5888097
  have hstable : (prefixWord ++ tailWord_5888097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888097).length < 2 ^ (prefixWord ++ tailWord_5888097).sum := by decide
  have hdescent : baseEnd_5888097 < baseStart_5888097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888114 : List Nat := [3, 2, 1, 2, 2, 3, 1, 4, 1, 1, 3]
def baseStart_5888114 : Nat := 118140960795 + 5888114 * 2 ^ 59
def prefixEnd_5888114 : Nat := 4983230072969 + 3 ^ 40 * 5888114 * 2
def baseEnd_5888114 : Nat := 3023432630467680960596063

theorem tailTrace_5888114 : CollatzResearch.WordTrace tailWord_5888114 prefixEnd_5888114 3023432630467680960596063 := by
  unfold tailWord_5888114
  simp only [CollatzResearch.WordTrace]
  refine ⟨53689290147594015663905849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143171440393584041770415597 53689290147594015663905849)
  ·
    refine ⟨40266967610695511747929387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53689290147594015663905849 40266967610695511747929387)
    ·
      refine ⟨60400451416043267621894081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40266967610695511747929387 60400451416043267621894081)
      ·
        refine ⟨45300338562032450716420561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60400451416043267621894081 45300338562032450716420561)
        ·
          refine ⟨33975253921524338037315421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45300338562032450716420561 33975253921524338037315421)
          ·
            refine ⟨12740720220571626763993283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33975253921524338037315421 12740720220571626763993283)
            ·
              refine ⟨19111080330857440145989925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12740720220571626763993283 19111080330857440145989925)
              ·
                refine ⟨3583327562035770027373111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19111080330857440145989925 3583327562035770027373111)
                ·
                  refine ⟨5374991343053655041059667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583327562035770027373111 5374991343053655041059667)
                  ·
                    refine ⟨8062487014580482561589501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5374991343053655041059667 8062487014580482561589501)
                    ·
                      refine ⟨3023432630467680960596063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8062487014580482561589501 3023432630467680960596063)
                      ·
                        rfl

theorem cell23_5888114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_5888114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888114 prefixEnd_5888114 := by exact prefixLift 5888114
  have htrace : WordTrace (prefixWord ++ tailWord_5888114) baseStart_5888114 baseEnd_5888114 := by
    simpa [prefixWord, tailWord_5888114, baseEnd_5888114] using wordTrace_append hprefix tailTrace_5888114
  have hstable : (prefixWord ++ tailWord_5888114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888114).length < 2 ^ (prefixWord ++ tailWord_5888114).sum := by decide
  have hdescent : baseEnd_5888114 < baseStart_5888114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888137 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 3, 2, 2]
def baseStart_5888137 : Nat := 118140960795 + 5888137 * 2 ^ 59
def prefixEnd_5888137 : Nat := 4983230072969 + 3 ^ 40 * 5888137 * 2
def baseEnd_5888137 : Nat := 3023444440522734370608457

theorem tailTrace_5888137 : CollatzResearch.WordTrace tailWord_5888137 prefixEnd_5888137 3023444440522734370608457 := by
  unfold tailWord_5888137
  simp only [CollatzResearch.WordTrace]
  refine ⟨214757999469292737583710665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143171999646195158389140443 214757999469292737583710665)
  ·
    refine ⟨161068499601969553187782999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214757999469292737583710665 161068499601969553187782999)
    ·
      refine ⟨241602749402954329781674499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161068499601969553187782999 241602749402954329781674499)
      ·
        refine ⟨362404124104431494672511749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241602749402954329781674499 362404124104431494672511749)
        ·
          refine ⟨67950773269580905251095953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362404124104431494672511749 67950773269580905251095953)
          ·
            refine ⟨50963079952185678938321965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67950773269580905251095953 50963079952185678938321965)
            ·
              refine ⟨19111154982069629601870737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50963079952185678938321965 19111154982069629601870737)
              ·
                refine ⟨14333366236552222201403053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19111154982069629601870737 14333366236552222201403053)
                ·
                  refine ⟨5375012338707083325526145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14333366236552222201403053 5375012338707083325526145)
                  ·
                    refine ⟨4031259254030312494144609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5375012338707083325526145 4031259254030312494144609)
                    ·
                      refine ⟨3023444440522734370608457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031259254030312494144609 3023444440522734370608457)
                      ·
                        rfl

theorem cell23_5888137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 2, 2].length) (baseStart_5888137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888137 prefixEnd_5888137 := by exact prefixLift 5888137
  have htrace : WordTrace (prefixWord ++ tailWord_5888137) baseStart_5888137 baseEnd_5888137 := by
    simpa [prefixWord, tailWord_5888137, baseEnd_5888137] using wordTrace_append hprefix tailTrace_5888137
  have hstable : (prefixWord ++ tailWord_5888137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888137).length < 2 ^ (prefixWord ++ tailWord_5888137).sum := by decide
  have hdescent : baseEnd_5888137 < baseStart_5888137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888148 : List Nat := [2, 4, 2, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_5888148 : Nat := 118140960795 + 5888148 * 2 ^ 59
def prefixEnd_5888148 : Nat := 4983230072969 + 3 ^ 40 * 5888148 * 2
def baseEnd_5888148 : Nat := 3023450088809933827570907

theorem tailTrace_5888148 : CollatzResearch.WordTrace tailWord_5888148 prefixEnd_5888148 3023450088809933827570907 := by
  unfold tailWord_5888148
  simp only [CollatzResearch.WordTrace]
  refine ⟨107379200336126443231180549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143172267114835257641574065 107379200336126443231180549)
  ·
    refine ⟨20133600063023708105846353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107379200336126443231180549 20133600063023708105846353)
    ·
      refine ⟨15100200047267781079384765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20133600063023708105846353 15100200047267781079384765)
      ·
        refine ⟨5662575017725417904769287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15100200047267781079384765 5662575017725417904769287)
        ·
          refine ⟨8493862526588126857153931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662575017725417904769287 8493862526588126857153931)
          ·
            refine ⟨12740793789882190285730897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8493862526588126857153931 12740793789882190285730897)
            ·
              refine ⟨9555595342411642714298173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12740793789882190285730897 9555595342411642714298173)
              ·
                refine ⟨3583348253404366017861815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9555595342411642714298173 3583348253404366017861815)
                ·
                  refine ⟨5375022380106549026792723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583348253404366017861815 5375022380106549026792723)
                  ·
                    refine ⟨8062533570159823540189085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5375022380106549026792723 8062533570159823540189085)
                    ·
                      refine ⟨3023450088809933827570907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8062533570159823540189085 3023450088809933827570907)
                      ·
                        rfl

theorem cell23_5888148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_5888148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888148 prefixEnd_5888148 := by exact prefixLift 5888148
  have htrace : WordTrace (prefixWord ++ tailWord_5888148) baseStart_5888148 baseEnd_5888148 := by
    simpa [prefixWord, tailWord_5888148, baseEnd_5888148] using wordTrace_append hprefix tailTrace_5888148
  have hstable : (prefixWord ++ tailWord_5888148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888148).length < 2 ^ (prefixWord ++ tailWord_5888148).sum := by decide
  have hdescent : baseEnd_5888148 < baseStart_5888148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888157 : List Nat := [1, 4, 2, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_5888157 : Nat := 118140960795 + 5888157 * 2 ^ 59
def prefixEnd_5888157 : Nat := 4983230072969 + 3 ^ 40 * 5888157 * 2
def baseEnd_5888157 : Nat := 3023454710135824292358365

theorem tailTrace_5888157 : CollatzResearch.WordTrace tailWord_5888157 prefixEnd_5888157 3023454710135824292358365 := by
  unfold tailWord_5888157
  simp only [CollatzResearch.WordTrace]
  refine ⟨214758728929220280999438725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143172485952813520666292483 214758728929220280999438725)
  ·
    refine ⟨40267261674228802687394761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214758728929220280999438725 40267261674228802687394761)
    ·
      refine ⟨30200446255671602015546071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40267261674228802687394761 30200446255671602015546071)
      ·
        refine ⟨45300669383507403023319107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30200446255671602015546071 45300669383507403023319107)
        ·
          refine ⟨67951004075261104534978661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45300669383507403023319107 67951004075261104534978661)
          ·
            refine ⟨12740813264111457100308499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67951004075261104534978661 12740813264111457100308499)
            ·
              refine ⟨19111219896167185650462749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12740813264111457100308499 19111219896167185650462749)
              ·
                refine ⟨7166707461062694618923531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19111219896167185650462749 7166707461062694618923531)
                ·
                  refine ⟨10750061191594041928385297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7166707461062694618923531 10750061191594041928385297)
                  ·
                    refine ⟨8062545893695531446288973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10750061191594041928385297 8062545893695531446288973)
                    ·
                      refine ⟨3023454710135824292358365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8062545893695531446288973 3023454710135824292358365)
                      ·
                        rfl

theorem cell23_5888157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_5888157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888157 prefixEnd_5888157 := by exact prefixLift 5888157
  have htrace : WordTrace (prefixWord ++ tailWord_5888157) baseStart_5888157 baseEnd_5888157 := by
    simpa [prefixWord, tailWord_5888157, baseEnd_5888157] using wordTrace_append hprefix tailTrace_5888157
  have hstable : (prefixWord ++ tailWord_5888157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888157).length < 2 ^ (prefixWord ++ tailWord_5888157).sum := by decide
  have hdescent : baseEnd_5888157 < baseStart_5888157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888164 : List Nat := [2, 3, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_5888164 : Nat := 118140960795 + 5888164 * 2 ^ 59
def prefixEnd_5888164 : Nat := 4983230072969 + 3 ^ 40 * 5888164 * 2
def baseEnd_5888164 : Nat := 1007819434833468588323611

theorem tailTrace_5888164 : CollatzResearch.WordTrace tailWord_5888164 prefixEnd_5888164 1007819434833468588323611 := by
  unfold tailWord_5888164
  simp only [CollatzResearch.WordTrace]
  refine ⟨107379492120097460597471773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143172656160129947463295697 107379492120097460597471773)
  ·
    refine ⟨40267309545036547724051915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107379492120097460597471773 40267309545036547724051915)
    ·
      refine ⟨60400964317554821586077873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40267309545036547724051915 60400964317554821586077873)
      ·
        refine ⟨45300723238166116189558405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60400964317554821586077873 45300723238166116189558405)
        ·
          refine ⟨8493885607156146785542201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45300723238166116189558405 8493885607156146785542201)
          ·
            refine ⟨6370414205367110089156651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8493885607156146785542201 6370414205367110089156651)
            ·
              refine ⟨9555621308050665133734977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6370414205367110089156651 9555621308050665133734977)
              ·
                refine ⟨7166715981037998850301233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9555621308050665133734977 7166715981037998850301233)
                ·
                  refine ⟨5375036985778499137725925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7166715981037998850301233 5375036985778499137725925)
                  ·
                    refine ⟨1007819434833468588323611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5375036985778499137725925 1007819434833468588323611)
                    ·
                      rfl

theorem cell23_5888164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_5888164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888164 prefixEnd_5888164 := by exact prefixLift 5888164
  have htrace : WordTrace (prefixWord ++ tailWord_5888164) baseStart_5888164 baseEnd_5888164 := by
    simpa [prefixWord, tailWord_5888164, baseEnd_5888164] using wordTrace_append hprefix tailTrace_5888164
  have hstable : (prefixWord ++ tailWord_5888164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888164).length < 2 ^ (prefixWord ++ tailWord_5888164).sum := by decide
  have hdescent : baseEnd_5888164 < baseStart_5888164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888174 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5888174 : Nat := 118140960795 + 5888174 * 2 ^ 59
def prefixEnd_5888174 : Nat := 4983230072969 + 3 ^ 40 * 5888174 * 2
def baseEnd_5888174 : Nat := 3023463439306950725845787

theorem tailTrace_5888174 : CollatzResearch.WordTrace tailWord_5888174 prefixEnd_5888174 3023463439306950725845787 := by
  unfold tailWord_5888174
  simp only [CollatzResearch.WordTrace]
  refine ⟨26844918621269836612850947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143172899313439128601871717 26844918621269836612850947)
  ·
    refine ⟨40267377931904754919276421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26844918621269836612850947 40267377931904754919276421)
    ·
      refine ⟨7550133362232141547364329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40267377931904754919276421 7550133362232141547364329)
      ·
        refine ⟨5662600021674106160523247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7550133362232141547364329 5662600021674106160523247)
        ·
          refine ⟨8493900032511159240784871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662600021674106160523247 8493900032511159240784871)
          ·
            refine ⟨12740850048766738861177307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8493900032511159240784871 12740850048766738861177307)
            ·
              refine ⟨19111275073150108291765961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12740850048766738861177307 19111275073150108291765961)
              ·
                refine ⟨14333456304862581218824471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19111275073150108291765961 14333456304862581218824471)
                ·
                  refine ⟨21500184457293871828236707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14333456304862581218824471 21500184457293871828236707)
                  ·
                    refine ⟨32250276685940807742355061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21500184457293871828236707 32250276685940807742355061)
                    ·
                      refine ⟨3023463439306950725845787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32250276685940807742355061 3023463439306950725845787)
                      ·
                        rfl

theorem cell23_5888174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5888174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888174 prefixEnd_5888174 := by exact prefixLift 5888174
  have htrace : WordTrace (prefixWord ++ tailWord_5888174) baseStart_5888174 baseEnd_5888174 := by
    simpa [prefixWord, tailWord_5888174, baseEnd_5888174] using wordTrace_append hprefix tailTrace_5888174
  have hstable : (prefixWord ++ tailWord_5888174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888174).length < 2 ^ (prefixWord ++ tailWord_5888174).sum := by decide
  have hdescent : baseEnd_5888174 < baseStart_5888174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888181 : List Nat := [1, 3, 3, 4, 1, 1, 3, 1, 2, 4]
def baseStart_5888181 : Nat := 118140960795 + 5888181 * 2 ^ 59
def prefixEnd_5888181 : Nat := 4983230072969 + 3 ^ 40 * 5888181 * 2
def baseEnd_5888181 : Nat := 1007822344557177399486085

theorem tailTrace_5888181 : CollatzResearch.WordTrace tailWord_5888181 prefixEnd_5888181 1007822344557177399486085 := by
  unfold tailWord_5888181
  simp only [CollatzResearch.WordTrace]
  refine ⟨214759604281133333098312397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143173069520755555398874931 214759604281133333098312397)
  ·
    refine ⟨80534851605424999911867149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214759604281133333098312397 80534851605424999911867149)
    ·
      refine ⟨30200569352034374966950181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80534851605424999911867149 30200569352034374966950181)
      ·
        refine ⟨5662606753506445306303159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30200569352034374966950181 5662606753506445306303159)
        ·
          refine ⟨8493910130259667959454739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662606753506445306303159 8493910130259667959454739)
          ·
            refine ⟨12740865195389501939182109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8493910130259667959454739 12740865195389501939182109)
            ·
              refine ⟨4777824448271063227193291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12740865195389501939182109 4777824448271063227193291)
              ·
                refine ⟨7166736672406594840789937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4777824448271063227193291 7166736672406594840789937)
                ·
                  refine ⟨5375052504304946130592453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7166736672406594840789937 5375052504304946130592453)
                  ·
                    refine ⟨1007822344557177399486085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5375052504304946130592453 1007822344557177399486085)
                    ·
                      rfl

theorem cell23_5888181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_5888181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888181 prefixEnd_5888181 := by exact prefixLift 5888181
  have htrace : WordTrace (prefixWord ++ tailWord_5888181) baseStart_5888181 baseEnd_5888181 := by
    simpa [prefixWord, tailWord_5888181, baseEnd_5888181] using wordTrace_append hprefix tailTrace_5888181
  have hstable : (prefixWord ++ tailWord_5888181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888181).length < 2 ^ (prefixWord ++ tailWord_5888181).sum := by decide
  have hdescent : baseEnd_5888181 < baseStart_5888181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888194 : List Nat := [3, 5, 1, 1, 1, 1, 4, 7]
def baseStart_5888194 : Nat := 118140960795 + 5888194 * 2 ^ 59
def prefixEnd_5888194 : Nat := 4983230072969 + 3 ^ 40 * 5888194 * 2
def baseEnd_5888194 : Nat := 111980507737779283244285

theorem tailTrace_5888194 : CollatzResearch.WordTrace tailWord_5888194 prefixEnd_5888194 111980507737779283244285 := by
  unfold tailWord_5888194
  simp only [CollatzResearch.WordTrace]
  refine ⟨53690019607521559079633909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143173385620057490879023757 53690019607521559079633909)
  ·
    refine ⟨5033439338205146163715679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53690019607521559079633909 5033439338205146163715679)
    ·
      refine ⟨7550159007307719245573519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5033439338205146163715679 7550159007307719245573519)
      ·
        refine ⟨11325238510961578868360279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7550159007307719245573519 11325238510961578868360279)
        ·
          refine ⟨16987857766442368302540419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11325238510961578868360279 16987857766442368302540419)
          ·
            refine ⟨25481786649663552453810629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16987857766442368302540419 25481786649663552453810629)
            ·
              refine ⟨4777834996811916085089493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25481786649663552453810629 4777834996811916085089493)
              ·
                refine ⟨111980507737779283244285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4777834996811916085089493 111980507737779283244285)
                ·
                  rfl

theorem cell23_5888194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 7].length) (baseStart_5888194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888194 prefixEnd_5888194 := by exact prefixLift 5888194
  have htrace : WordTrace (prefixWord ++ tailWord_5888194) baseStart_5888194 baseEnd_5888194 := by
    simpa [prefixWord, tailWord_5888194, baseEnd_5888194] using wordTrace_append hprefix tailTrace_5888194
  have hstable : (prefixWord ++ tailWord_5888194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888194).length < 2 ^ (prefixWord ++ tailWord_5888194).sum := by decide
  have hdescent : baseEnd_5888194 < baseStart_5888194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888197 : List Nat := [1, 3, 1, 1, 1, 1, 5, 4, 1, 3, 2]
def baseStart_5888197 : Nat := 118140960795 + 5888197 * 2 ^ 59
def prefixEnd_5888197 : Nat := 4983230072969 + 3 ^ 40 * 5888197 * 2
def baseEnd_5888197 : Nat := 3023475249362004135858181

theorem tailTrace_5888197 : CollatzResearch.WordTrace tailWord_5888197 prefixEnd_5888197 3023475249362004135858181 := by
  unfold tailWord_5888197
  simp only [CollatzResearch.WordTrace]
  refine ⟨214760187849075367830894845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143173458566050245220596563 214760187849075367830894845)
  ·
    refine ⟨80535070443403262936585567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214760187849075367830894845 80535070443403262936585567)
    ·
      refine ⟨120802605665104894404878351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80535070443403262936585567 120802605665104894404878351)
      ·
        refine ⟨181203908497657341607317527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120802605665104894404878351 181203908497657341607317527)
        ·
          refine ⟨271805862746486012410976291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181203908497657341607317527 271805862746486012410976291)
          ·
            refine ⟨407708794119729018616464437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271805862746486012410976291 407708794119729018616464437)
            ·
              refine ⟨38222699448724595495293541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 407708794119729018616464437 38222699448724595495293541)
              ·
                refine ⟨7166756146635861655367539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38222699448724595495293541 7166756146635861655367539)
                ·
                  refine ⟨10750134219953792483051309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7166756146635861655367539 10750134219953792483051309)
                  ·
                    refine ⟨4031300332482672181144241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10750134219953792483051309 4031300332482672181144241)
                    ·
                      refine ⟨3023475249362004135858181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031300332482672181144241 3023475249362004135858181)
                      ·
                        rfl

theorem cell23_5888197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 3, 2].length) (baseStart_5888197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888197 prefixEnd_5888197 := by exact prefixLift 5888197
  have htrace : WordTrace (prefixWord ++ tailWord_5888197) baseStart_5888197 baseEnd_5888197 := by
    simpa [prefixWord, tailWord_5888197, baseEnd_5888197] using wordTrace_append hprefix tailTrace_5888197
  have hstable : (prefixWord ++ tailWord_5888197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888197).length < 2 ^ (prefixWord ++ tailWord_5888197).sum := by decide
  have hdescent : baseEnd_5888197 < baseStart_5888197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888253 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_5888253 : Nat := 118140960795 + 5888253 * 2 ^ 59
def prefixEnd_5888253 : Nat := 4983230072969 + 3 ^ 40 * 5888253 * 2
def baseEnd_5888253 : Nat := 3023504004278655916757923

theorem tailTrace_5888253 : CollatzResearch.WordTrace tailWord_5888253 prefixEnd_5888253 3023504004278655916757923 := by
  unfold tailWord_5888253
  simp only [CollatzResearch.WordTrace]
  refine ⟨214762230336872489394933413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143174820224581659596622275 214762230336872489394933413)
  ·
    refine ⟨40267918188163591761550015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214762230336872489394933413 40267918188163591761550015)
    ·
      refine ⟨60401877282245387642325023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40267918188163591761550015 60401877282245387642325023)
      ·
        refine ⟨90602815923368081463487535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60401877282245387642325023 90602815923368081463487535)
        ·
          refine ⟨135904223885052122195231303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90602815923368081463487535 135904223885052122195231303)
          ·
            refine ⟨203856335827578183292846955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135904223885052122195231303 203856335827578183292846955)
            ·
              refine ⟨305784503741367274939270433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203856335827578183292846955 305784503741367274939270433)
              ·
                refine ⟨229338377806025456204452825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305784503741367274939270433 229338377806025456204452825)
                ·
                  refine ⟨172003783354519092153339619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229338377806025456204452825 172003783354519092153339619)
                  ·
                    refine ⟨258005675031778638230009429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 172003783354519092153339619 258005675031778638230009429)
                    ·
                      refine ⟨3023504004278655916757923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 258005675031778638230009429 3023504004278655916757923)
                      ·
                        rfl

theorem cell23_5888253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_5888253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888253 prefixEnd_5888253 := by exact prefixLift 5888253
  have htrace : WordTrace (prefixWord ++ tailWord_5888253) baseStart_5888253 baseEnd_5888253 := by
    simpa [prefixWord, tailWord_5888253, baseEnd_5888253] using wordTrace_append hprefix tailTrace_5888253
  have hstable : (prefixWord ++ tailWord_5888253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888253).length < 2 ^ (prefixWord ++ tailWord_5888253).sum := by decide
  have hdescent : baseEnd_5888253 < baseStart_5888253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888280 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 2, 5]
def baseStart_5888280 : Nat := 118140960795 + 5888280 * 2 ^ 59
def prefixEnd_5888280 : Nat := 4983230072969 + 3 ^ 40 * 5888280 * 2
def baseEnd_5888280 : Nat := 1007839289418775770373433

theorem tailTrace_5888280 : CollatzResearch.WordTrace tailWord_5888280 prefixEnd_5888280 1007839289418775770373433 := by
  unfold tailWord_5888280
  simp only [CollatzResearch.WordTrace]
  refine ⟨107381607553887336503083147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143175476738516448670777529 107381607553887336503083147)
  ·
    refine ⟨161072411330831004754624721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107381607553887336503083147 161072411330831004754624721)
    ·
      refine ⟨120804308498123253565968541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161072411330831004754624721 120804308498123253565968541)
      ·
        refine ⟨45301615686796220087238203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120804308498123253565968541 45301615686796220087238203)
        ·
          refine ⟨67952423530194330130857305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45301615686796220087238203 67952423530194330130857305)
          ·
            refine ⟨50964317647645747598142979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67952423530194330130857305 50964317647645747598142979)
            ·
              refine ⟨76446476471468621397214469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50964317647645747598142979 76446476471468621397214469)
              ·
                refine ⟨14333714338400366511977713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76446476471468621397214469 14333714338400366511977713)
                ·
                  refine ⟨10750285753800274883983285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14333714338400366511977713 10750285753800274883983285)
                  ·
                    refine ⟨1007839289418775770373433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10750285753800274883983285 1007839289418775770373433)
                    ·
                      rfl

theorem cell23_5888280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_5888280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888280 prefixEnd_5888280 := by exact prefixLift 5888280
  have htrace : WordTrace (prefixWord ++ tailWord_5888280) baseStart_5888280 baseEnd_5888280 := by
    simpa [prefixWord, tailWord_5888280, baseEnd_5888280] using wordTrace_append hprefix tailTrace_5888280
  have hstable : (prefixWord ++ tailWord_5888280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888280).length < 2 ^ (prefixWord ++ tailWord_5888280).sum := by decide
  have hdescent : baseEnd_5888280 < baseStart_5888280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888287 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 2, 5, 2]
def baseStart_5888287 : Nat := 118140960795 + 5888287 * 2 ^ 59
def prefixEnd_5888287 : Nat := 4983230072969 + 3 ^ 40 * 5888287 * 2
def baseEnd_5888287 : Nat := 3023521462620908783732767

theorem tailTrace_5888287 : CollatzResearch.WordTrace tailWord_5888287 prefixEnd_5888287 3023521462620908783732767 := by
  unfold tailWord_5888287
  simp only [CollatzResearch.WordTrace]
  refine ⟨214763470418749313201671115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143175646945832875467780743 214763470418749313201671115)
  ·
    refine ⟨322145205628123969802506673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214763470418749313201671115 322145205628123969802506673)
    ·
      refine ⟨241608904221092977351880005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322145205628123969802506673 241608904221092977351880005)
      ·
        refine ⟨45301669541454933253477501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241608904221092977351880005 45301669541454933253477501)
        ·
          refine ⟨16988126078045599970054063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45301669541454933253477501 16988126078045599970054063)
          ·
            refine ⟨25482189117068399955081095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16988126078045599970054063 25482189117068399955081095)
            ·
              refine ⟨38223283675602599932621643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25482189117068399955081095 38223283675602599932621643)
              ·
                refine ⟨57334925513403899898932465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38223283675602599932621643 57334925513403899898932465)
                ·
                  refine ⟨43001194135052924924199349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57334925513403899898932465 43001194135052924924199349)
                  ·
                    refine ⟨4031361950161211711643689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43001194135052924924199349 4031361950161211711643689)
                    ·
                      refine ⟨3023521462620908783732767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031361950161211711643689 3023521462620908783732767)
                      ·
                        rfl

theorem cell23_5888287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_5888287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888287 prefixEnd_5888287 := by exact prefixLift 5888287
  have htrace : WordTrace (prefixWord ++ tailWord_5888287) baseStart_5888287 baseEnd_5888287 := by
    simpa [prefixWord, tailWord_5888287, baseEnd_5888287] using wordTrace_append hprefix tailTrace_5888287
  have hstable : (prefixWord ++ tailWord_5888287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888287).length < 2 ^ (prefixWord ++ tailWord_5888287).sum := by decide
  have hdescent : baseEnd_5888287 < baseStart_5888287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888300 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_5888300 : Nat := 118140960795 + 5888300 * 2 ^ 59
def prefixEnd_5888300 : Nat := 4983230072969 + 3 ^ 40 * 5888300 * 2
def baseEnd_5888300 : Nat := 3023528137869417232870207

theorem tailTrace_5888300 : CollatzResearch.WordTrace tailWord_5888300 prefixEnd_5888300 3023528137869417232870207 := by
  unfold tailWord_5888300
  simp only [CollatzResearch.WordTrace]
  refine ⟨107381972283851108210947177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143175963045134810947929569 107381972283851108210947177)
  ·
    refine ⟨80536479212888331158210383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107381972283851108210947177 80536479212888331158210383)
    ·
      refine ⟨120804718819332496737315575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80536479212888331158210383 120804718819332496737315575)
      ·
        refine ⟨181207078228998745105973363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120804718819332496737315575 181207078228998745105973363)
        ·
          refine ⟨271810617343498117658960045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181207078228998745105973363 271810617343498117658960045)
          ·
            refine ⟨101928981503811794122110017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271810617343498117658960045 101928981503811794122110017)
            ·
              refine ⟨76446736127858845591582513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101928981503811794122110017 76446736127858845591582513)
              ·
                refine ⟨57335052095894134193686885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76446736127858845591582513 57335052095894134193686885)
                ·
                  refine ⟨10750322267980150161316291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57335052095894134193686885 10750322267980150161316291)
                  ·
                    refine ⟨16125483401970225241974437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10750322267980150161316291 16125483401970225241974437)
                    ·
                      refine ⟨3023528137869417232870207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16125483401970225241974437 3023528137869417232870207)
                      ·
                        rfl

theorem cell23_5888300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_5888300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888300 prefixEnd_5888300 := by exact prefixLift 5888300
  have htrace : WordTrace (prefixWord ++ tailWord_5888300) baseStart_5888300 baseEnd_5888300 := by
    simpa [prefixWord, tailWord_5888300, baseEnd_5888300] using wordTrace_append hprefix tailTrace_5888300
  have hstable : (prefixWord ++ tailWord_5888300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888300).length < 2 ^ (prefixWord ++ tailWord_5888300).sum := by decide
  have hdescent : baseEnd_5888300 < baseStart_5888300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888367 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 5, 1, 3]
def baseStart_5888367 : Nat := 118140960795 + 5888367 * 2 ^ 59
def prefixEnd_5888367 : Nat := 4983230072969 + 3 ^ 40 * 5888367 * 2
def baseEnd_5888367 : Nat := 3023562541073268470732399

theorem tailTrace_5888367 : CollatzResearch.WordTrace tailWord_5888367 prefixEnd_5888367 3023562541073268470732399 := by
  unfold tailWord_5888367
  simp only [CollatzResearch.WordTrace]
  refine ⟨214766388258459486864583355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143177592172306324576388903 214766388258459486864583355)
  ·
    refine ⟨322149582387689230296875033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214766388258459486864583355 322149582387689230296875033)
    ·
      refine ⟨241612186790766922722656275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322149582387689230296875033 241612186790766922722656275)
      ·
        refine ⟨362418280186150384083984413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241612186790766922722656275 362418280186150384083984413)
        ·
          refine ⟨135906855069806394031494155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362418280186150384083984413 135906855069806394031494155)
          ·
            refine ⟨203860282604709591047241233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135906855069806394031494155 203860282604709591047241233)
            ·
              refine ⟨152895211953532193285430925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203860282604709591047241233 152895211953532193285430925)
              ·
                refine ⟨57335704482574572482036597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152895211953532193285430925 57335704482574572482036597)
                ·
                  refine ⟨5375222295241366170190931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57335704482574572482036597 5375222295241366170190931)
                  ·
                    refine ⟨8062833442862049255286397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5375222295241366170190931 8062833442862049255286397)
                    ·
                      refine ⟨3023562541073268470732399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8062833442862049255286397 3023562541073268470732399)
                      ·
                        rfl

theorem cell23_5888367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 1, 3].length) (baseStart_5888367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888367 prefixEnd_5888367 := by exact prefixLift 5888367
  have htrace : WordTrace (prefixWord ++ tailWord_5888367) baseStart_5888367 baseEnd_5888367 := by
    simpa [prefixWord, tailWord_5888367, baseEnd_5888367] using wordTrace_append hprefix tailTrace_5888367
  have hstable : (prefixWord ++ tailWord_5888367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888367).length < 2 ^ (prefixWord ++ tailWord_5888367).sum := by decide
  have hdescent : baseEnd_5888367 < baseStart_5888367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888441 : List Nat := [1, 2, 1, 4, 3, 2, 3, 1, 1, 1, 4]
def baseStart_5888441 : Nat := 118140960795 + 5888441 * 2 ^ 59
def prefixEnd_5888441 : Nat := 4983230072969 + 3 ^ 40 * 5888441 * 2
def baseEnd_5888441 : Nat := 3023600538641701181207059

theorem tailTrace_5888441 : CollatzResearch.WordTrace tailWord_5888441 prefixEnd_5888441 3023600538641701181207059 := by
  unfold tailWord_5888441
  simp only [CollatzResearch.WordTrace]
  refine ⟨214769087260191397502777177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143179391506794265001851451 214769087260191397502777177)
  ·
    refine ⟨161076815445143548127082883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214769087260191397502777177 161076815445143548127082883)
    ·
      refine ⟨241615223167715322190624325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161076815445143548127082883 241615223167715322190624325)
      ·
        refine ⟨45302854343946622910742061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241615223167715322190624325 45302854343946622910742061)
        ·
          refine ⟨16988570378979983591528273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45302854343946622910742061 16988570378979983591528273)
          ·
            refine ⟨12741427784234987693646205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16988570378979983591528273 12741427784234987693646205)
            ·
              refine ⟨4778035419088120385117327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12741427784234987693646205 4778035419088120385117327)
              ·
                refine ⟨7167053128632180577675991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4778035419088120385117327 7167053128632180577675991)
                ·
                  refine ⟨10750579692948270866513987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7167053128632180577675991 10750579692948270866513987)
                  ·
                    refine ⟨16125869539422406299770981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10750579692948270866513987 16125869539422406299770981)
                    ·
                      refine ⟨3023600538641701181207059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16125869539422406299770981 3023600538641701181207059)
                      ·
                        rfl

theorem cell23_5888441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_5888441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888441 prefixEnd_5888441 := by exact prefixLift 5888441
  have htrace : WordTrace (prefixWord ++ tailWord_5888441) baseStart_5888441 baseEnd_5888441 := by
    simpa [prefixWord, tailWord_5888441, baseEnd_5888441] using wordTrace_append hprefix tailTrace_5888441
  have hstable : (prefixWord ++ tailWord_5888441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888441).length < 2 ^ (prefixWord ++ tailWord_5888441).sum := by decide
  have hdescent : baseEnd_5888441 < baseStart_5888441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888444 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_5888444 : Nat := 118140960795 + 5888444 * 2 ^ 59
def prefixEnd_5888444 : Nat := 4983230072969 + 3 ^ 40 * 5888444 * 2
def baseEnd_5888444 : Nat := 3023602079083664669469545

theorem tailTrace_5888444 : CollatzResearch.WordTrace tailWord_5888444 prefixEnd_5888444 3023602079083664669469545 := by
  unfold tailWord_5888444
  simp only [CollatzResearch.WordTrace]
  refine ⟨107384598339590264507568193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143179464452787019343424257 107384598339590264507568193)
  ·
    refine ⟨80538448754692698380676145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107384598339590264507568193 80538448754692698380676145)
    ·
      refine ⟨60403836566019523785507109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80538448754692698380676145 60403836566019523785507109)
      ·
        refine ⟨11325719356128660709782583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60403836566019523785507109 11325719356128660709782583)
        ·
          refine ⟨16988579034192991064673875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11325719356128660709782583 16988579034192991064673875)
          ·
            refine ⟨25482868551289486597010813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16988579034192991064673875 25482868551289486597010813)
            ·
              refine ⟨9556075706733557473879055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25482868551289486597010813 9556075706733557473879055)
              ·
                refine ⟨14334113560100336210818583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9556075706733557473879055 14334113560100336210818583)
                ·
                  refine ⟨21501170340150504316227875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14334113560100336210818583 21501170340150504316227875)
                  ·
                    refine ⟨32251755510225756474341813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21501170340150504316227875 32251755510225756474341813)
                    ·
                      refine ⟨3023602079083664669469545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32251755510225756474341813 3023602079083664669469545)
                      ·
                        rfl

theorem cell23_5888444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_5888444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888444 prefixEnd_5888444 := by exact prefixLift 5888444
  have htrace : WordTrace (prefixWord ++ tailWord_5888444) baseStart_5888444 baseEnd_5888444 := by
    simpa [prefixWord, tailWord_5888444, baseEnd_5888444] using wordTrace_append hprefix tailTrace_5888444
  have hstable : (prefixWord ++ tailWord_5888444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888444).length < 2 ^ (prefixWord ++ tailWord_5888444).sum := by decide
  have hdescent : baseEnd_5888444 < baseStart_5888444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888452 : List Nat := [2, 3, 3, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_5888452 : Nat := 118140960795 + 5888452 * 2 ^ 59
def prefixEnd_5888452 : Nat := 4983230072969 + 3 ^ 40 * 5888452 * 2
def baseEnd_5888452 : Nat := 3023606186928900638169509

theorem tailTrace_5888452 : CollatzResearch.WordTrace tailWord_5888452 prefixEnd_5888452 3023606186928900638169509 := by
  unfold tailWord_5888452
  simp only [CollatzResearch.WordTrace]
  refine ⟨107384744231575773190713805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143179658975434364254285073 107384744231575773190713805)
  ·
    refine ⟨40269279086840914946517677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107384744231575773190713805 40269279086840914946517677)
    ·
      refine ⟨15100979657565343104944129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40269279086840914946517677 15100979657565343104944129)
      ·
        refine ⟨11325734743174007328708097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15100979657565343104944129 11325734743174007328708097)
        ·
          refine ⟨8494301057380505496531073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11325734743174007328708097 8494301057380505496531073)
          ·
            refine ⟨6370725793035379122398305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8494301057380505496531073 6370725793035379122398305)
            ·
              refine ⟨4778044344776534341798729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6370725793035379122398305 4778044344776534341798729)
              ·
                refine ⟨3583533258582400756349047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4778044344776534341798729 3583533258582400756349047)
                ·
                  refine ⟨5375299887873601134523571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583533258582400756349047 5375299887873601134523571)
                  ·
                    refine ⟨8062949831810401701785357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5375299887873601134523571 8062949831810401701785357)
                    ·
                      refine ⟨3023606186928900638169509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8062949831810401701785357 3023606186928900638169509)
                      ·
                        rfl

theorem cell23_5888452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_5888452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888452 prefixEnd_5888452 := by exact prefixLift 5888452
  have htrace : WordTrace (prefixWord ++ tailWord_5888452) baseStart_5888452 baseEnd_5888452 := by
    simpa [prefixWord, tailWord_5888452, baseEnd_5888452] using wordTrace_append hprefix tailTrace_5888452
  have hstable : (prefixWord ++ tailWord_5888452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888452).length < 2 ^ (prefixWord ++ tailWord_5888452).sum := by decide
  have hdescent : baseEnd_5888452 < baseStart_5888452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888458 : List Nat := [3, 1, 2, 1, 2, 2, 3, 4, 1, 2, 2]
def baseStart_5888458 : Nat := 118140960795 + 5888458 * 2 ^ 59
def prefixEnd_5888458 : Nat := 4983230072969 + 3 ^ 40 * 5888458 * 2
def baseEnd_5888458 : Nat := 3023609267812827614694481

theorem tailTrace_5888458 : CollatzResearch.WordTrace tailWord_5888458 prefixEnd_5888458 3023609267812827614694481 := by
  unfold tailWord_5888458
  simp only [CollatzResearch.WordTrace]
  refine ⟨53692426825282452351536507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143179804867419872937430685 53692426825282452351536507)
  ·
    refine ⟨80538640237923678527304761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53692426825282452351536507 80538640237923678527304761)
    ·
      refine ⟨60403980178442758895478571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80538640237923678527304761 60403980178442758895478571)
      ·
        refine ⟨90605970267664138343217857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60403980178442758895478571 90605970267664138343217857)
        ·
          refine ⟨67954477700748103757413393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90605970267664138343217857 67954477700748103757413393)
          ·
            refine ⟨50965858275561077818060045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67954477700748103757413393 50965858275561077818060045)
            ·
              refine ⟨19112196853335404181772517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50965858275561077818060045 19112196853335404181772517)
              ·
                refine ⟨3583536910000388284082347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19112196853335404181772517 3583536910000388284082347)
                ·
                  refine ⟨5375305365000582426123521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583536910000388284082347 5375305365000582426123521)
                  ·
                    refine ⟨4031479023750436819592641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5375305365000582426123521 4031479023750436819592641)
                    ·
                      refine ⟨3023609267812827614694481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031479023750436819592641 3023609267812827614694481)
                      ·
                        rfl

theorem cell23_5888458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_5888458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888458 prefixEnd_5888458 := by exact prefixLift 5888458
  have htrace : WordTrace (prefixWord ++ tailWord_5888458) baseStart_5888458 baseEnd_5888458 := by
    simpa [prefixWord, tailWord_5888458, baseEnd_5888458] using wordTrace_append hprefix tailTrace_5888458
  have hstable : (prefixWord ++ tailWord_5888458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888458).length < 2 ^ (prefixWord ++ tailWord_5888458).sum := by decide
  have hdescent : baseEnd_5888458 < baseStart_5888458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888474 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3]
def baseStart_5888474 : Nat := 118140960795 + 5888474 * 2 ^ 59
def prefixEnd_5888474 : Nat := 4983230072969 + 3 ^ 40 * 5888474 * 2
def baseEnd_5888474 : Nat := 3023617483503299552094407

theorem tailTrace_5888474 : CollatzResearch.WordTrace tailWord_5888474 prefixEnd_5888474 3023617483503299552094407 := by
  unfold tailWord_5888474
  simp only [CollatzResearch.WordTrace]
  refine ⟨53692572717267961034682119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143180193912714562759152317 53692572717267961034682119)
  ·
    refine ⟨80538859075901941552023179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53692572717267961034682119 80538859075901941552023179)
    ·
      refine ⟨120808288613852912328034769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80538859075901941552023179 120808288613852912328034769)
      ·
        refine ⟨90606216460389684246026077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120808288613852912328034769 90606216460389684246026077)
        ·
          refine ⟨33977331172646131592259779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90606216460389684246026077 33977331172646131592259779)
          ·
            refine ⟨50965996758969197388389669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33977331172646131592259779 50965996758969197388389669)
            ·
              refine ⟨9556124392306724510323063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50965996758969197388389669 9556124392306724510323063)
              ·
                refine ⟨14334186588460086765484595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9556124392306724510323063 14334186588460086765484595)
                ·
                  refine ⟨21501279882690130148226893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14334186588460086765484595 21501279882690130148226893)
                  ·
                    refine ⟨8062979956008798805585085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21501279882690130148226893 8062979956008798805585085)
                    ·
                      refine ⟨3023617483503299552094407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8062979956008798805585085 3023617483503299552094407)
                      ·
                        rfl

theorem cell23_5888474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_5888474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888474 prefixEnd_5888474 := by exact prefixLift 5888474
  have htrace : WordTrace (prefixWord ++ tailWord_5888474) baseStart_5888474 baseEnd_5888474 := by
    simpa [prefixWord, tailWord_5888474, baseEnd_5888474] using wordTrace_append hprefix tailTrace_5888474
  have hstable : (prefixWord ++ tailWord_5888474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888474).length < 2 ^ (prefixWord ++ tailWord_5888474).sum := by decide
  have hdescent : baseEnd_5888474 < baseStart_5888474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888477 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_5888477 : Nat := 118140960795 + 5888477 * 2 ^ 59
def prefixEnd_5888477 : Nat := 4983230072969 + 3 ^ 40 * 5888477 * 2
def baseEnd_5888477 : Nat := 1007873007981754346785631

theorem tailTrace_5888477 : CollatzResearch.WordTrace tailWord_5888477 prefixEnd_5888477 1007873007981754346785631 := by
  unfold tailWord_5888477
  simp only [CollatzResearch.WordTrace]
  refine ⟨214770400288060975651087685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143180266858707317100725123 214770400288060975651087685)
  ·
    refine ⟨40269450054011432934578941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214770400288060975651087685 40269450054011432934578941)
    ·
      refine ⟨15101043770254287350467103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40269450054011432934578941 15101043770254287350467103)
      ·
        refine ⟨22651565655381431025700655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15101043770254287350467103 22651565655381431025700655)
        ·
          refine ⟨33977348483072146538550983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22651565655381431025700655 33977348483072146538550983)
          ·
            refine ⟨50966022724608219807826475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33977348483072146538550983 50966022724608219807826475)
            ·
              refine ⟨76449034086912329711739713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50966022724608219807826475 76449034086912329711739713)
              ·
                refine ⟨57336775565184247283804785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76449034086912329711739713 57336775565184247283804785)
                ·
                  refine ⟨43002581673888185462853589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57336775565184247283804785 43002581673888185462853589)
                  ·
                    refine ⟨1007873007981754346785631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43002581673888185462853589 1007873007981754346785631)
                    ·
                      rfl

theorem cell23_5888477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_5888477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888477 prefixEnd_5888477 := by exact prefixLift 5888477
  have htrace : WordTrace (prefixWord ++ tailWord_5888477) baseStart_5888477 baseEnd_5888477 := by
    simpa [prefixWord, tailWord_5888477, baseEnd_5888477] using wordTrace_append hprefix tailTrace_5888477
  have hstable : (prefixWord ++ tailWord_5888477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888477).length < 2 ^ (prefixWord ++ tailWord_5888477).sum := by decide
  have hdescent : baseEnd_5888477 < baseStart_5888477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888487 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_5888487 : Nat := 118140960795 + 5888487 * 2 ^ 59
def prefixEnd_5888487 : Nat := 4983230072969 + 3 ^ 40 * 5888487 * 2
def baseEnd_5888487 : Nat := 3023624158751808001231847

theorem tailTrace_5888487 : CollatzResearch.WordTrace tailWord_5888487 prefixEnd_5888487 3023624158751808001231847 := by
  unfold tailWord_5888487
  simp only [CollatzResearch.WordTrace]
  refine ⟨214770765018024747358951715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143180510012016498239301143 214770765018024747358951715)
  ·
    refine ⟨322156147527037121038427573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214770765018024747358951715 322156147527037121038427573)
    ·
      refine ⟨30202138830659730097352585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 322156147527037121038427573 30202138830659730097352585)
      ·
        refine ⟨22651604122994797573014439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30202138830659730097352585 22651604122994797573014439)
        ·
          refine ⟨33977406184492196359521659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22651604122994797573014439 33977406184492196359521659)
          ·
            refine ⟨50966109276738294539282489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33977406184492196359521659 50966109276738294539282489)
            ·
              refine ⟨38224581957553720904461867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50966109276738294539282489 38224581957553720904461867)
              ·
                refine ⟨57336872936330581356692801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38224581957553720904461867 57336872936330581356692801)
                ·
                  refine ⟨43002654702247936017519601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57336872936330581356692801 43002654702247936017519601)
                  ·
                    refine ⟨32251991026685952013139701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43002654702247936017519601 32251991026685952013139701)
                    ·
                      refine ⟨3023624158751808001231847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32251991026685952013139701 3023624158751808001231847)
                      ·
                        rfl

theorem cell23_5888487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_5888487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888487 prefixEnd_5888487 := by exact prefixLift 5888487
  have htrace : WordTrace (prefixWord ++ tailWord_5888487) baseStart_5888487 baseEnd_5888487 := by
    simpa [prefixWord, tailWord_5888487, baseEnd_5888487] using wordTrace_append hprefix tailTrace_5888487
  have hstable : (prefixWord ++ tailWord_5888487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888487).length < 2 ^ (prefixWord ++ tailWord_5888487).sum := by decide
  have hdescent : baseEnd_5888487 < baseStart_5888487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888517 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 1, 6, 3]
def baseStart_5888517 : Nat := 118140960795 + 5888517 * 2 ^ 59
def prefixEnd_5888517 : Nat := 4983230072969 + 3 ^ 40 * 5888517 * 2
def baseEnd_5888517 : Nat := 3023639563171442883856709

theorem tailTrace_5888517 : CollatzResearch.WordTrace tailWord_5888517 prefixEnd_5888517 3023639563171442883856709 := by
  unfold tailWord_5888517
  simp only [CollatzResearch.WordTrace]
  refine ⟨214771859207916062482543805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143181239471944041655029203 214771859207916062482543805)
  ·
    refine ⟨80539447202968523430953927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214771859207916062482543805 80539447202968523430953927)
    ·
      refine ⟨120809170804452785146430891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80539447202968523430953927 120809170804452785146430891)
      ·
        refine ⟨181213756206679177719646337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120809170804452785146430891 181213756206679177719646337)
        ·
          refine ⟨135910317155009383289734753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181213756206679177719646337 135910317155009383289734753)
          ·
            refine ⟨101932737866257037467301065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135910317155009383289734753 101932737866257037467301065)
            ·
              refine ⟨76449553399692778100475799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101932737866257037467301065 76449553399692778100475799)
              ·
                refine ⟨114674330099539167150713699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76449553399692778100475799 114674330099539167150713699)
                ·
                  refine ⟨172011495149308750726070549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114674330099539167150713699 172011495149308750726070549)
                  ·
                    refine ⟨8063038835123847690284557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 172011495149308750726070549 8063038835123847690284557)
                    ·
                      refine ⟨3023639563171442883856709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8063038835123847690284557 3023639563171442883856709)
                      ·
                        rfl

theorem cell23_5888517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_5888517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888517 prefixEnd_5888517 := by exact prefixLift 5888517
  have htrace : WordTrace (prefixWord ++ tailWord_5888517) baseStart_5888517 baseEnd_5888517 := by
    simpa [prefixWord, tailWord_5888517, baseEnd_5888517] using wordTrace_append hprefix tailTrace_5888517
  have hstable : (prefixWord ++ tailWord_5888517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888517).length < 2 ^ (prefixWord ++ tailWord_5888517).sum := by decide
  have hdescent : baseEnd_5888517 < baseStart_5888517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888525 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_5888525 : Nat := 118140960795 + 5888525 * 2 ^ 59
def prefixEnd_5888525 : Nat := 4983230072969 + 3 ^ 40 * 5888525 * 2
def baseEnd_5888525 : Nat := 3023643671016678852556673

theorem tailTrace_5888525 : CollatzResearch.WordTrace tailWord_5888525 prefixEnd_5888525 3023643671016678852556673 := by
  unfold tailWord_5888525
  simp only [CollatzResearch.WordTrace]
  refine ⟨214772150991887079848835029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143181433994591386565890019 214772150991887079848835029)
  ·
    refine ⟨5033722288872353433957071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 214772150991887079848835029 5033722288872353433957071)
    ·
      refine ⟨7550583433308530150935607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5033722288872353433957071 7550583433308530150935607)
      ·
        refine ⟨11325875149962795226403411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7550583433308530150935607 11325875149962795226403411)
        ·
          refine ⟨16988812724944192839605117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11325875149962795226403411 16988812724944192839605117)
          ·
            refine ⟨6370804771854072314851919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16988812724944192839605117 6370804771854072314851919)
            ·
              refine ⟨9556207157781108472277879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6370804771854072314851919 9556207157781108472277879)
              ·
                refine ⟨14334310736671662708416819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9556207157781108472277879 14334310736671662708416819)
                ·
                  refine ⟨21501466105007494062625229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14334310736671662708416819 21501466105007494062625229)
                  ·
                    refine ⟨8063049789377810273484461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21501466105007494062625229 8063049789377810273484461)
                    ·
                      refine ⟨3023643671016678852556673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8063049789377810273484461 3023643671016678852556673)
                      ·
                        rfl

theorem cell23_5888525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_5888525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888525 prefixEnd_5888525 := by exact prefixLift 5888525
  have htrace : WordTrace (prefixWord ++ tailWord_5888525) baseStart_5888525 baseEnd_5888525 := by
    simpa [prefixWord, tailWord_5888525, baseEnd_5888525] using wordTrace_append hprefix tailTrace_5888525
  have hstable : (prefixWord ++ tailWord_5888525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888525).length < 2 ^ (prefixWord ++ tailWord_5888525).sum := by decide
  have hdescent : baseEnd_5888525 < baseStart_5888525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888535 : List Nat := [1, 1, 3, 6, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5888535 : Nat := 118140960795 + 5888535 * 2 ^ 59
def prefixEnd_5888535 : Nat := 4983230072969 + 3 ^ 40 * 5888535 * 2
def baseEnd_5888535 : Nat := 3023648805823223813431627

theorem tailTrace_5888535 : CollatzResearch.WordTrace tailWord_5888535 prefixEnd_5888535 3023648805823223813431627 := by
  unfold tailWord_5888535
  simp only [CollatzResearch.WordTrace]
  refine ⟨214772515721850851556699059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143181677147900567704466039 214772515721850851556699059)
  ·
    refine ⟨322158773582776277335048589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214772515721850851556699059 322158773582776277335048589)
    ·
      refine ⟨120809540093541104000643221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322158773582776277335048589 120809540093541104000643221)
      ·
        refine ⟨5662947191884739250030151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120809540093541104000643221 5662947191884739250030151)
        ·
          refine ⟨8494420787827108875045227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662947191884739250030151 8494420787827108875045227)
          ·
            refine ⟨12741631181740663312567841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8494420787827108875045227 12741631181740663312567841)
            ·
              refine ⟨9556223386305497484425881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12741631181740663312567841 9556223386305497484425881)
              ·
                refine ⟨7167167539729123113319411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9556223386305497484425881 7167167539729123113319411)
                ·
                  refine ⟨10750751309593684669979117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7167167539729123113319411 10750751309593684669979117)
                  ·
                    refine ⟨4031531741097631751242169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10750751309593684669979117 4031531741097631751242169)
                    ·
                      refine ⟨3023648805823223813431627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031531741097631751242169 3023648805823223813431627)
                      ·
                        rfl

theorem cell23_5888535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5888535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888535 prefixEnd_5888535 := by exact prefixLift 5888535
  have htrace : WordTrace (prefixWord ++ tailWord_5888535) baseStart_5888535 baseEnd_5888535 := by
    simpa [prefixWord, tailWord_5888535, baseEnd_5888535] using wordTrace_append hprefix tailTrace_5888535
  have hstable : (prefixWord ++ tailWord_5888535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888535).length < 2 ^ (prefixWord ++ tailWord_5888535).sum := by decide
  have hdescent : baseEnd_5888535 < baseStart_5888535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888582 : List Nat := [6, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_5888582 : Nat := 118140960795 + 5888582 * 2 ^ 59
def prefixEnd_5888582 : Nat := 4983230072969 + 3 ^ 40 * 5888582 * 2
def baseEnd_5888582 : Nat := 3023672939413985129543911

theorem tailTrace_5888582 : CollatzResearch.WordTrace tailWord_5888582 prefixEnd_5888582 3023672939413985129543911 := by
  unfold tailWord_5888582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6711694686021268080739375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143182819968453719055773333 6711694686021268080739375)
  ·
    refine ⟨10067542029031902121109063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6711694686021268080739375 10067542029031902121109063)
    ·
      refine ⟨15101313043547853181663595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10067542029031902121109063 15101313043547853181663595)
      ·
        refine ⟨22651969565321779772495393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15101313043547853181663595 22651969565321779772495393)
        ·
          refine ⟨16988977173991334829371545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22651969565321779772495393 16988977173991334829371545)
          ·
            refine ⟨12741732880493501122028659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16988977173991334829371545 12741732880493501122028659)
            ·
              refine ⟨19112599320740251683042989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12741732880493501122028659 19112599320740251683042989)
              ·
                refine ⟨7167224745277594381141121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19112599320740251683042989 7167224745277594381141121)
                ·
                  refine ⟨5375418558958195785855841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7167224745277594381141121 5375418558958195785855841)
                  ·
                    refine ⟨4031563919218646839391881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5375418558958195785855841 4031563919218646839391881)
                    ·
                      refine ⟨3023672939413985129543911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031563919218646839391881 3023672939413985129543911)
                      ·
                        rfl

theorem cell23_5888582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_5888582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888582 prefixEnd_5888582 := by exact prefixLift 5888582
  have htrace : WordTrace (prefixWord ++ tailWord_5888582) baseStart_5888582 baseEnd_5888582 := by
    simpa [prefixWord, tailWord_5888582, baseEnd_5888582] using wordTrace_append hprefix tailTrace_5888582
  have hstable : (prefixWord ++ tailWord_5888582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888582).length < 2 ^ (prefixWord ++ tailWord_5888582).sum := by decide
  have hdescent : baseEnd_5888582 < baseStart_5888582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888587 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 4]
def baseStart_5888587 : Nat := 118140960795 + 5888587 * 2 ^ 59
def prefixEnd_5888587 : Nat := 4983230072969 + 3 ^ 40 * 5888587 * 2
def baseEnd_5888587 : Nat := 3023675506817257609981387

theorem tailTrace_5888587 : CollatzResearch.WordTrace tailWord_5888587 prefixEnd_5888587 3023675506817257609981387 := by
  unfold tailWord_5888587
  simp only [CollatzResearch.WordTrace]
  refine ⟨214774412317662464437592015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143182941545108309625061343 214774412317662464437592015)
  ·
    refine ⟨322161618476493696656388023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214774412317662464437592015 322161618476493696656388023)
    ·
      refine ⟨483242427714740544984582035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322161618476493696656388023 483242427714740544984582035)
      ·
        refine ⟨724863641572110817476873053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483242427714740544984582035 724863641572110817476873053)
        ·
          refine ⟨271823865589541556553827395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 724863641572110817476873053 271823865589541556553827395)
          ·
            refine ⟨407735798384312334830741093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271823865589541556553827395 407735798384312334830741093)
            ·
              refine ⟨76450462197058562780763955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 407735798384312334830741093 76450462197058562780763955)
              ·
                refine ⟨114675693295587844171145933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76450462197058562780763955 114675693295587844171145933)
                ·
                  refine ⟨43003384985845441564179725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114675693295587844171145933 43003384985845441564179725)
                  ·
                    refine ⟨16126269369692040586567397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43003384985845441564179725 16126269369692040586567397)
                    ·
                      refine ⟨3023675506817257609981387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16126269369692040586567397 3023675506817257609981387)
                      ·
                        rfl

theorem cell23_5888587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 4].length) (baseStart_5888587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888587 prefixEnd_5888587 := by exact prefixLift 5888587
  have htrace : WordTrace (prefixWord ++ tailWord_5888587) baseStart_5888587 baseEnd_5888587 := by
    simpa [prefixWord, tailWord_5888587, baseEnd_5888587] using wordTrace_append hprefix tailTrace_5888587
  have hstable : (prefixWord ++ tailWord_5888587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888587).length < 2 ^ (prefixWord ++ tailWord_5888587).sum := by decide
  have hdescent : baseEnd_5888587 < baseStart_5888587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888597 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 2, 8]
def baseStart_5888597 : Nat := 118140960795 + 5888597 * 2 ^ 59
def prefixEnd_5888597 : Nat := 4983230072969 + 3 ^ 40 * 5888597 * 2
def baseEnd_5888597 : Nat := 1007893547207934190285447

theorem tailTrace_5888597 : CollatzResearch.WordTrace tailWord_5888597 prefixEnd_5888597 1007893547207934190285447 := by
  unfold tailWord_5888597
  simp only [CollatzResearch.WordTrace]
  refine ⟨214774777047626236145456045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143183184698417490763637363 214774777047626236145456045)
  ·
    refine ⟨80540541392859838554546017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214774777047626236145456045 80540541392859838554546017)
    ·
      refine ⟨60405406044644878915909513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80540541392859838554546017 60405406044644878915909513)
      ·
        refine ⟨45304054533483659186932135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60405406044644878915909513 45304054533483659186932135)
        ·
          refine ⟨67956081800225488780398203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45304054533483659186932135 67956081800225488780398203)
          ·
            refine ⟨101934122700338233170597305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67956081800225488780398203 101934122700338233170597305)
            ·
              refine ⟨76450592025253674877947979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101934122700338233170597305 76450592025253674877947979)
              ·
                refine ⟨114675888037880512316921969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76450592025253674877947979 114675888037880512316921969)
                ·
                  refine ⟨86006916028410384237691477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114675888037880512316921969 86006916028410384237691477)
                  ·
                    refine ⟨1007893547207934190285447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86006916028410384237691477 1007893547207934190285447)
                    ·
                      rfl

theorem cell23_5888597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_5888597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888597 prefixEnd_5888597 := by exact prefixLift 5888597
  have htrace : WordTrace (prefixWord ++ tailWord_5888597) baseStart_5888597 baseEnd_5888597 := by
    simpa [prefixWord, tailWord_5888597, baseEnd_5888597] using wordTrace_append hprefix tailTrace_5888597
  have hstable : (prefixWord ++ tailWord_5888597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888597).length < 2 ^ (prefixWord ++ tailWord_5888597).sum := by decide
  have hdescent : baseEnd_5888597 < baseStart_5888597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888617 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 6]
def baseStart_5888617 : Nat := 118140960795 + 5888617 * 2 ^ 59
def prefixEnd_5888617 : Nat := 4983230072969 + 3 ^ 40 * 5888617 * 2
def baseEnd_5888617 : Nat := 3023690911236892492606249

theorem tailTrace_5888617 : CollatzResearch.WordTrace tailWord_5888617 prefixEnd_5888617 3023690911236892492606249 := by
  unfold tailWord_5888617
  simp only [CollatzResearch.WordTrace]
  refine ⟨214775506507553779561184105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143183671005035853040789403 214775506507553779561184105)
  ·
    refine ⟨161081629880665334670888079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214775506507553779561184105 161081629880665334670888079)
    ·
      refine ⟨241622444820998002006332119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161081629880665334670888079 241622444820998002006332119)
      ·
        refine ⟨362433667231497003009498179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241622444820998002006332119 362433667231497003009498179)
        ·
          refine ⟨543650500847245504514247269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362433667231497003009498179 543650500847245504514247269)
          ·
            refine ⟨101934468908858532096421363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 543650500847245504514247269 101934468908858532096421363)
            ·
              refine ⟨152901703363287798144632045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101934468908858532096421363 152901703363287798144632045)
              ·
                refine ⟨57338138761232924304237017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152901703363287798144632045 57338138761232924304237017)
                ·
                  refine ⟨43003604070924693228177763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57338138761232924304237017 43003604070924693228177763)
                  ·
                    refine ⟨64505406106387039842266645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43003604070924693228177763 64505406106387039842266645)
                    ·
                      refine ⟨3023690911236892492606249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64505406106387039842266645 3023690911236892492606249)
                      ·
                        rfl

theorem cell23_5888617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_5888617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888617 prefixEnd_5888617 := by exact prefixLift 5888617
  have htrace : WordTrace (prefixWord ++ tailWord_5888617) baseStart_5888617 baseEnd_5888617 := by
    simpa [prefixWord, tailWord_5888617, baseEnd_5888617] using wordTrace_append hprefix tailTrace_5888617
  have hstable : (prefixWord ++ tailWord_5888617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888617).length < 2 ^ (prefixWord ++ tailWord_5888617).sum := by decide
  have hdescent : baseEnd_5888617 < baseStart_5888617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888621 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_5888621 : Nat := 118140960795 + 5888621 * 2 ^ 59
def prefixEnd_5888621 : Nat := 4983230072969 + 3 ^ 40 * 5888621 * 2
def baseEnd_5888621 : Nat := 3023692965159510476956231

theorem tailTrace_5888621 : CollatzResearch.WordTrace tailWord_5888621 prefixEnd_5888621 3023692965159510476956231 := by
  unfold tailWord_5888621
  simp only [CollatzResearch.WordTrace]
  refine ⟨214775652399539288244329717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143183768266359525496219811 214775652399539288244329717)
  ·
    refine ⟨20135217412456808272905911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214775652399539288244329717 20135217412456808272905911)
    ·
      refine ⟨30202826118685212409358867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20135217412456808272905911 30202826118685212409358867)
      ·
        refine ⟨45304239178027818614038301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30202826118685212409358867 45304239178027818614038301)
        ·
          refine ⟨16989089691760431980264363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45304239178027818614038301 16989089691760431980264363)
          ·
            refine ⟨25483634537640647970396545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16989089691760431980264363 25483634537640647970396545)
            ·
              refine ⟨19112725903230485977797409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25483634537640647970396545 19112725903230485977797409)
              ·
                refine ⟨14334544427422864483348057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19112725903230485977797409 14334544427422864483348057)
                ·
                  refine ⟨10750908320567148362511043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14334544427422864483348057 10750908320567148362511043)
                  ·
                    refine ⟨16126362480850722543766565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10750908320567148362511043 16126362480850722543766565)
                    ·
                      refine ⟨3023692965159510476956231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16126362480850722543766565 3023692965159510476956231)
                      ·
                        rfl

theorem cell23_5888621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_5888621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888621 prefixEnd_5888621 := by exact prefixLift 5888621
  have htrace : WordTrace (prefixWord ++ tailWord_5888621) baseStart_5888621 baseEnd_5888621 := by
    simpa [prefixWord, tailWord_5888621, baseEnd_5888621] using wordTrace_append hprefix tailTrace_5888621
  have hstable : (prefixWord ++ tailWord_5888621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888621).length < 2 ^ (prefixWord ++ tailWord_5888621).sum := by decide
  have hdescent : baseEnd_5888621 < baseStart_5888621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888658 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_5888658 : Nat := 118140960795 + 5888658 * 2 ^ 59
def prefixEnd_5888658 : Nat := 4983230072969 + 3 ^ 40 * 5888658 * 2
def baseEnd_5888658 : Nat := 3023711963943726832193561

theorem tailTrace_5888658 : CollatzResearch.WordTrace tailWord_5888658 prefixEnd_5888658 3023711963943726832193561 := by
  unfold tailWord_5888658
  simp only [CollatzResearch.WordTrace]
  refine ⟨53694250475101310890856657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143184667933603495708951085 53694250475101310890856657)
  ·
    refine ⟨40270687856325983168142493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53694250475101310890856657 40270687856325983168142493)
    ·
      refine ⟨15101507946122243688053435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40270687856325983168142493 15101507946122243688053435)
      ·
        refine ⟨22652261919183365532080153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15101507946122243688053435 22652261919183365532080153)
        ·
          refine ⟨16989196439387524149060115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22652261919183365532080153 16989196439387524149060115)
          ·
            refine ⟨25483794659081286223590173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16989196439387524149060115 25483794659081286223590173)
            ·
              refine ⟨9556422997155482333846315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25483794659081286223590173 9556422997155482333846315)
              ·
                refine ⟨14334634495733223500769473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9556422997155482333846315 14334634495733223500769473)
                ·
                  refine ⟨10750975871799917625577105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14334634495733223500769473 10750975871799917625577105)
                  ·
                    refine ⟨8063231903849938219182829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10750975871799917625577105 8063231903849938219182829)
                    ·
                      refine ⟨3023711963943726832193561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8063231903849938219182829 3023711963943726832193561)
                      ·
                        rfl

theorem cell23_5888658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_5888658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888658 prefixEnd_5888658 := by exact prefixLift 5888658
  have htrace : WordTrace (prefixWord ++ tailWord_5888658) baseStart_5888658 baseEnd_5888658 := by
    simpa [prefixWord, tailWord_5888658, baseEnd_5888658] using wordTrace_append hprefix tailTrace_5888658
  have hstable : (prefixWord ++ tailWord_5888658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888658).length < 2 ^ (prefixWord ++ tailWord_5888658).sum := by decide
  have hdescent : baseEnd_5888658 < baseStart_5888658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888708 : List Nat := [2, 3, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_5888708 : Nat := 118140960795 + 5888708 * 2 ^ 59
def prefixEnd_5888708 : Nat := 4983230072969 + 3 ^ 40 * 5888708 * 2
def baseEnd_5888708 : Nat := 1007912545992150545522777

theorem tailTrace_5888708 : CollatzResearch.WordTrace tailWord_5888708 prefixEnd_5888708 1007912545992150545522777 := by
  unfold tailWord_5888708
  simp only [CollatzResearch.WordTrace]
  refine ⟨107389412775112051051373389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143185883700149401401831185 107389412775112051051373389)
  ·
    refine ⟨40271029790667019144265021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107389412775112051051373389 40271029790667019144265021)
    ·
      refine ⟨15101636171500132179099383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40271029790667019144265021 15101636171500132179099383)
      ·
        refine ⟨22652454257250198268649075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15101636171500132179099383 22652454257250198268649075)
        ·
          refine ⟨33978681385875297402973613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22652454257250198268649075 33978681385875297402973613)
          ·
            refine ⟨12742005519703236526115105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33978681385875297402973613 12742005519703236526115105)
            ·
              refine ⟨9556504139777427394586329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12742005519703236526115105 9556504139777427394586329)
              ·
                refine ⟨7167378104833070545939747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9556504139777427394586329 7167378104833070545939747)
                ·
                  refine ⟨10751067157249605818909621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7167378104833070545939747 10751067157249605818909621)
                  ·
                    refine ⟨1007912545992150545522777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10751067157249605818909621 1007912545992150545522777)
                    ·
                      rfl

theorem cell23_5888708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_5888708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888708 prefixEnd_5888708 := by exact prefixLift 5888708
  have htrace : WordTrace (prefixWord ++ tailWord_5888708) baseStart_5888708 baseEnd_5888708 := by
    simpa [prefixWord, tailWord_5888708, baseEnd_5888708] using wordTrace_append hprefix tailTrace_5888708
  have hstable : (prefixWord ++ tailWord_5888708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888708).length < 2 ^ (prefixWord ++ tailWord_5888708).sum := by decide
  have hdescent : baseEnd_5888708 < baseStart_5888708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888745 : List Nat := [1, 2, 1, 1, 1, 2, 4, 6, 1, 2, 2]
def baseStart_5888745 : Nat := 118140960795 + 5888745 * 2 ^ 59
def prefixEnd_5888745 : Nat := 4983230072969 + 3 ^ 40 * 5888745 * 2
def baseEnd_5888745 : Nat := 3023756636760667991805661

theorem tailTrace_5888745 : CollatzResearch.WordTrace tailWord_5888745 prefixEnd_5888745 3023756636760667991805661 := by
  unfold tailWord_5888745
  simp only [CollatzResearch.WordTrace]
  refine ⟨214780175051090057421843689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143186783367393371614562459 214780175051090057421843689)
  ·
    refine ⟨161085131288317543066382767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214780175051090057421843689 161085131288317543066382767)
    ·
      refine ⟨241627696932476314599574151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161085131288317543066382767 241627696932476314599574151)
      ·
        refine ⟨362441545398714471899361227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241627696932476314599574151 362441545398714471899361227)
        ·
          refine ⟨543662318098071707849041841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362441545398714471899361227 543662318098071707849041841)
          ·
            refine ⟨407746738573553780886781381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543662318098071707849041841 407746738573553780886781381)
            ·
              refine ⟨76452513482541333916271509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 407746738573553780886781381 76452513482541333916271509)
              ·
                refine ⟨3583711569494125027325227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76452513482541333916271509 3583711569494125027325227)
                ·
                  refine ⟨5375567354241187540987841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583711569494125027325227 5375567354241187540987841)
                  ·
                    refine ⟨4031675515680890655740881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5375567354241187540987841 4031675515680890655740881)
                    ·
                      refine ⟨3023756636760667991805661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031675515680890655740881 3023756636760667991805661)
                      ·
                        rfl

theorem cell23_5888745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 1, 2, 2].length) (baseStart_5888745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888745 prefixEnd_5888745 := by exact prefixLift 5888745
  have htrace : WordTrace (prefixWord ++ tailWord_5888745) baseStart_5888745 baseEnd_5888745 := by
    simpa [prefixWord, tailWord_5888745, baseEnd_5888745] using wordTrace_append hprefix tailTrace_5888745
  have hstable : (prefixWord ++ tailWord_5888745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888745).length < 2 ^ (prefixWord ++ tailWord_5888745).sum := by decide
  have hdescent : baseEnd_5888745 < baseStart_5888745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888852 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_5888852 : Nat := 118140960795 + 5888852 * 2 ^ 59
def prefixEnd_5888852 : Nat := 4983230072969 + 3 ^ 40 * 5888852 * 2
def baseEnd_5888852 : Nat := 3023811579190699073167669

theorem tailTrace_5888852 : CollatzResearch.WordTrace tailWord_5888852 prefixEnd_5888852 3023811579190699073167669 := by
  unfold tailWord_5888852
  simp only [CollatzResearch.WordTrace]
  refine ⟨107392038830851207347994405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143189385107801609797325873 107392038830851207347994405)
  ·
    refine ⟨20136007280784601377748951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107392038830851207347994405 20136007280784601377748951)
    ·
      refine ⟨30204010921176902066623427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20136007280784601377748951 30204010921176902066623427)
      ·
        refine ⟨45306016381765353099935141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30204010921176902066623427 45306016381765353099935141)
        ·
          refine ⟨8494878071581003706237839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45306016381765353099935141 8494878071581003706237839)
          ·
            refine ⟨12742317107371505559356759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8494878071581003706237839 12742317107371505559356759)
            ·
              refine ⟨19113475661057258339035139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12742317107371505559356759 19113475661057258339035139)
              ·
                refine ⟨28670213491585887508552709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19113475661057258339035139 28670213491585887508552709)
                ·
                  refine ⟨5375665029672353907853633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28670213491585887508552709 5375665029672353907853633)
                  ·
                    refine ⟨4031748772254265430890225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5375665029672353907853633 4031748772254265430890225)
                    ·
                      refine ⟨3023811579190699073167669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031748772254265430890225 3023811579190699073167669)
                      ·
                        rfl

theorem cell23_5888852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_5888852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888852 prefixEnd_5888852 := by exact prefixLift 5888852
  have htrace : WordTrace (prefixWord ++ tailWord_5888852) baseStart_5888852 baseEnd_5888852 := by
    simpa [prefixWord, tailWord_5888852, baseEnd_5888852] using wordTrace_append hprefix tailTrace_5888852
  have hstable : (prefixWord ++ tailWord_5888852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888852).length < 2 ^ (prefixWord ++ tailWord_5888852).sum := by decide
  have hdescent : baseEnd_5888852 < baseStart_5888852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888858 : List Nat := [3, 1, 1, 2, 1, 4, 2, 4, 5]
def baseStart_5888858 : Nat := 118140960795 + 5888858 * 2 ^ 59
def prefixEnd_5888858 : Nat := 4983230072969 + 3 ^ 40 * 5888858 * 2
def baseEnd_5888858 : Nat := 335979406674958449965849

theorem tailTrace_5888858 : CollatzResearch.WordTrace tailWord_5888858 prefixEnd_5888858 335979406674958449965849 := by
  unfold tailWord_5888858
  simp only [CollatzResearch.WordTrace]
  refine ⟨53696074124920169430176807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143189530999787118480471485 53696074124920169430176807)
  ·
    refine ⟨80544111187380254145265211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53696074124920169430176807 80544111187380254145265211)
    ·
      refine ⟨120816166781070381217897817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80544111187380254145265211 120816166781070381217897817)
      ·
        refine ⟨90612125085802785913423363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120816166781070381217897817 90612125085802785913423363)
        ·
          refine ⟨135918187628704178870135045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90612125085802785913423363 135918187628704178870135045)
          ·
            refine ⟨25484660180382033538150321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135918187628704178870135045 25484660180382033538150321)
            ·
              refine ⟨19113495135286525153612741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25484660180382033538150321 19113495135286525153612741)
              ·
                refine ⟨3583780337866223466302389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19113495135286525153612741 3583780337866223466302389)
                ·
                  refine ⟨335979406674958449965849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3583780337866223466302389 335979406674958449965849)
                  ·
                    rfl

theorem cell23_5888858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_5888858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888858 prefixEnd_5888858 := by exact prefixLift 5888858
  have htrace : WordTrace (prefixWord ++ tailWord_5888858) baseStart_5888858 baseEnd_5888858 := by
    simpa [prefixWord, tailWord_5888858, baseEnd_5888858] using wordTrace_append hprefix tailTrace_5888858
  have hstable : (prefixWord ++ tailWord_5888858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888858).length < 2 ^ (prefixWord ++ tailWord_5888858).sum := by decide
  have hdescent : baseEnd_5888858 < baseStart_5888858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888868 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_5888868 : Nat := 118140960795 + 5888868 * 2 ^ 59
def prefixEnd_5888868 : Nat := 4983230072969 + 3 ^ 40 * 5888868 * 2
def baseEnd_5888868 : Nat := 3023819794881171010567595

theorem tailTrace_5888868 : CollatzResearch.WordTrace tailWord_5888868 prefixEnd_5888868 3023819794881171010567595 := by
  unfold tailWord_5888868
  simp only [CollatzResearch.WordTrace]
  refine ⟨107392330614822224714285629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143189774153096299619047505 107392330614822224714285629)
  ·
    refine ⟨40272123980558334267857111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107392330614822224714285629 40272123980558334267857111)
    ·
      refine ⟨60408185970837501401785667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40272123980558334267857111 60408185970837501401785667)
      ·
        refine ⟨90612278956256252102678501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60408185970837501401785667 90612278956256252102678501)
        ·
          refine ⟨16989802304298047269252219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90612278956256252102678501 16989802304298047269252219)
          ·
            refine ⟨25484703456447070903878329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16989802304298047269252219 25484703456447070903878329)
            ·
              refine ⟨19113527592335303177908747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25484703456447070903878329 19113527592335303177908747)
              ·
                refine ⟨28670291388502954766863121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19113527592335303177908747 28670291388502954766863121)
                ·
                  refine ⟨21502718541377216075147341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28670291388502954766863121 21502718541377216075147341)
                  ·
                    refine ⟨8063519453016456028180253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21502718541377216075147341 8063519453016456028180253)
                    ·
                      refine ⟨3023819794881171010567595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8063519453016456028180253 3023819794881171010567595)
                      ·
                        rfl

theorem cell23_5888868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_5888868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888868 prefixEnd_5888868 := by exact prefixLift 5888868
  have htrace : WordTrace (prefixWord ++ tailWord_5888868) baseStart_5888868 baseEnd_5888868 := by
    simpa [prefixWord, tailWord_5888868, baseEnd_5888868] using wordTrace_append hprefix tailTrace_5888868
  have hstable : (prefixWord ++ tailWord_5888868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888868).length < 2 ^ (prefixWord ++ tailWord_5888868).sum := by decide
  have hdescent : baseEnd_5888868 < baseStart_5888868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888871 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 1, 7]
def baseStart_5888871 : Nat := 118140960795 + 5888871 * 2 ^ 59
def prefixEnd_5888871 : Nat := 4983230072969 + 3 ^ 40 * 5888871 * 2
def baseEnd_5888871 : Nat := 1007940445107711499610027

theorem tailTrace_5888871 : CollatzResearch.WordTrace tailWord_5888871 prefixEnd_5888871 1007940445107711499610027 := by
  unfold tailWord_5888871
  simp only [CollatzResearch.WordTrace]
  refine ⟨214784770648633580940930467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143189847099089053960620311 214784770648633580940930467)
  ·
    refine ⟨322177155972950371411395701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214784770648633580940930467 322177155972950371411395701)
    ·
      refine ⟨30204108372464097319818347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 322177155972950371411395701 30204108372464097319818347)
      ·
        refine ⟨45306162558696145979727521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30204108372464097319818347 45306162558696145979727521)
        ·
          refine ⟨33979621919022109484795641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45306162558696145979727521 33979621919022109484795641)
          ·
            refine ⟨25484716439266582113596731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33979621919022109484795641 25484716439266582113596731)
            ·
              refine ⟨38227074658899873170395097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25484716439266582113596731 38227074658899873170395097)
              ·
                refine ⟨28670305994174904877796323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38227074658899873170395097 28670305994174904877796323)
                ·
                  refine ⟨43005458991262357316694485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28670305994174904877796323 43005458991262357316694485)
                  ·
                    refine ⟨1007940445107711499610027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43005458991262357316694485 1007940445107711499610027)
                    ·
                      rfl

theorem cell23_5888871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_5888871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888871 prefixEnd_5888871 := by exact prefixLift 5888871
  have htrace : WordTrace (prefixWord ++ tailWord_5888871) baseStart_5888871 baseEnd_5888871 := by
    simpa [prefixWord, tailWord_5888871, baseEnd_5888871] using wordTrace_append hprefix tailTrace_5888871
  have hstable : (prefixWord ++ tailWord_5888871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888871).length < 2 ^ (prefixWord ++ tailWord_5888871).sum := by decide
  have hdescent : baseEnd_5888871 < baseStart_5888871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888891 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 4]
def baseStart_5888891 : Nat := 118140960795 + 5888891 * 2 ^ 59
def prefixEnd_5888891 : Nat := 4983230072969 + 3 ^ 40 * 5888891 * 2
def baseEnd_5888891 : Nat := 3023831604936224420579989

theorem tailTrace_5888891 : CollatzResearch.WordTrace tailWord_5888891 prefixEnd_5888891 3023831604936224420579989 := by
  unfold tailWord_5888891
  simp only [CollatzResearch.WordTrace]
  refine ⟨214785500108561124356658527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143190333405707416237772351 214785500108561124356658527)
  ·
    refine ⟨322178250162841686534987791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214785500108561124356658527 322178250162841686534987791)
    ·
      refine ⟨483267375244262529802481687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322178250162841686534987791 483267375244262529802481687)
      ·
        refine ⟨724901062866393794703722531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483267375244262529802481687 724901062866393794703722531)
        ·
          refine ⟨1087351594299590692055583797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724901062866393794703722531 1087351594299590692055583797)
          ·
            refine ⟨101939211965586627380210981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1087351594299590692055583797 101939211965586627380210981)
            ·
              refine ⟨19113602243547492633789559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101939211965586627380210981 19113602243547492633789559)
              ·
                refine ⟨28670403365321238950684339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19113602243547492633789559 28670403365321238950684339)
                ·
                  refine ⟨43005605047981858426026509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28670403365321238950684339 43005605047981858426026509)
                  ·
                    refine ⟨16127101892993196909759941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43005605047981858426026509 16127101892993196909759941)
                    ·
                      refine ⟨3023831604936224420579989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16127101892993196909759941 3023831604936224420579989)
                      ·
                        rfl

theorem cell23_5888891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 4].length) (baseStart_5888891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888891 prefixEnd_5888891 := by exact prefixLift 5888891
  have htrace : WordTrace (prefixWord ++ tailWord_5888891) baseStart_5888891 baseEnd_5888891 := by
    simpa [prefixWord, tailWord_5888891, baseEnd_5888891] using wordTrace_append hprefix tailTrace_5888891
  have hstable : (prefixWord ++ tailWord_5888891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888891).length < 2 ^ (prefixWord ++ tailWord_5888891).sum := by decide
  have hdescent : baseEnd_5888891 < baseStart_5888891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5888908 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 4, 4, 2]
def baseStart_5888908 : Nat := 118140960795 + 5888908 * 2 ^ 59
def prefixEnd_5888908 : Nat := 4983230072969 + 3 ^ 40 * 5888908 * 2
def baseEnd_5888908 : Nat := 3023840334107350854067411

theorem tailTrace_5888908 : CollatzResearch.WordTrace tailWord_5888908 prefixEnd_5888908 3023840334107350854067411 := by
  unfold tailWord_5888908
  simp only [CollatzResearch.WordTrace]
  refine ⟨107393060074749768130013689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143190746766333024173351585 107393060074749768130013689)
  ·
    refine ⟨80544795056062326097510267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107393060074749768130013689 80544795056062326097510267)
    ·
      refine ⟨120817192584093489146265401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80544795056062326097510267 120817192584093489146265401)
      ·
        refine ⟨90612894438070116859699051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120817192584093489146265401 90612894438070116859699051)
        ·
          refine ⟨135919341657105175289548577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90612894438070116859699051 135919341657105175289548577)
          ·
            refine ⟨101939506242828881467161433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135919341657105175289548577 101939506242828881467161433)
            ·
              refine ⟨76454629682121661100371075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101939506242828881467161433 76454629682121661100371075)
              ·
                refine ⟨114681944523182491650556613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76454629682121661100371075 114681944523182491650556613)
                ·
                  refine ⟨21502864598096717184479365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114681944523182491650556613 21502864598096717184479365)
                  ·
                    refine ⟨4031787112143134472089881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21502864598096717184479365 4031787112143134472089881)
                    ·
                      refine ⟨3023840334107350854067411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031787112143134472089881 3023840334107350854067411)
                      ·
                        rfl

theorem cell23_5888908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_5888908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5888908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5888908 prefixEnd_5888908 := by exact prefixLift 5888908
  have htrace : WordTrace (prefixWord ++ tailWord_5888908) baseStart_5888908 baseEnd_5888908 := by
    simpa [prefixWord, tailWord_5888908, baseEnd_5888908] using wordTrace_append hprefix tailTrace_5888908
  have hstable : (prefixWord ++ tailWord_5888908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5888908).length < 2 ^ (prefixWord ++ tailWord_5888908).sum := by decide
  have hdescent : baseEnd_5888908 < baseStart_5888908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5888908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889002 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_5889002 : Nat := 118140960795 + 5889002 * 2 ^ 59
def prefixEnd_5889002 : Nat := 4983230072969 + 3 ^ 40 * 5889002 * 2
def baseEnd_5889002 : Nat := 3023888601288873486291979

theorem tailTrace_5889002 : CollatzResearch.WordTrace tailWord_5889002 prefixEnd_5889002 3023888601288873486291979 := by
  unfold tailWord_5889002
  simp only [CollatzResearch.WordTrace]
  refine ⟨53697387152789747578487315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143193032407439326875966173 53697387152789747578487315)
  ·
    refine ⟨80546080729184621367730973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53697387152789747578487315 80546080729184621367730973)
    ·
      refine ⟨30204780273444233012899115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80546080729184621367730973 30204780273444233012899115)
      ·
        refine ⟨45307170410166349519348673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30204780273444233012899115 45307170410166349519348673)
        ·
          refine ⟨33980377807624762139511505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45307170410166349519348673 33980377807624762139511505)
          ·
            refine ⟨25485283355718571604633629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33980377807624762139511505 25485283355718571604633629)
            ·
              refine ⟨9556981258394464351737611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25485283355718571604633629 9556981258394464351737611)
              ·
                refine ⟨14335471887591696527606417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9556981258394464351737611 14335471887591696527606417)
                ·
                  refine ⟨10751603915693772395704813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14335471887591696527606417 10751603915693772395704813)
                  ·
                    refine ⟨4031851468385164648389305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10751603915693772395704813 4031851468385164648389305)
                    ·
                      refine ⟨3023888601288873486291979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031851468385164648389305 3023888601288873486291979)
                      ·
                        rfl

theorem cell23_5889002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_5889002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889002 prefixEnd_5889002 := by exact prefixLift 5889002
  have htrace : WordTrace (prefixWord ++ tailWord_5889002) baseStart_5889002 baseEnd_5889002 := by
    simpa [prefixWord, tailWord_5889002, baseEnd_5889002] using wordTrace_append hprefix tailTrace_5889002
  have hstable : (prefixWord ++ tailWord_5889002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889002).length < 2 ^ (prefixWord ++ tailWord_5889002).sum := by decide
  have hdescent : baseEnd_5889002 < baseStart_5889002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889008 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 4, 4]
def baseStart_5889008 : Nat := 118140960795 + 5889008 * 2 ^ 59
def prefixEnd_5889008 : Nat := 4983230072969 + 3 ^ 40 * 5889008 * 2
def baseEnd_5889008 : Nat := 1007963894057600154272317

theorem tailTrace_5889008 : CollatzResearch.WordTrace tailWord_5889008 prefixEnd_5889008 1007963894057600154272317 := by
  unfold tailWord_5889008
  simp only [CollatzResearch.WordTrace]
  refine ⟨107394883724568626669333839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143193178299424835559111785 107394883724568626669333839)
  ·
    refine ⟨161092325586852940004000759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107394883724568626669333839 161092325586852940004000759)
    ·
      refine ⟨241638488380279410006001139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161092325586852940004000759 241638488380279410006001139)
      ·
        refine ⟨362457732570419115009001709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241638488380279410006001139 362457732570419115009001709)
        ·
          refine ⟨135921649713907168128375641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362457732570419115009001709 135921649713907168128375641)
          ·
            refine ⟨101941237285430376096281731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135921649713907168128375641 101941237285430376096281731)
            ·
              refine ⟨152911855928145564144422597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101941237285430376096281731 152911855928145564144422597)
              ·
                refine ⟨28670972986527293277079237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152911855928145564144422597 28670972986527293277079237)
                ·
                  refine ⟨5375807434973867489452357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28670972986527293277079237 5375807434973867489452357)
                  ·
                    refine ⟨1007963894057600154272317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5375807434973867489452357 1007963894057600154272317)
                    ·
                      rfl

theorem cell23_5889008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 4, 4].length) (baseStart_5889008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889008 prefixEnd_5889008 := by exact prefixLift 5889008
  have htrace : WordTrace (prefixWord ++ tailWord_5889008) baseStart_5889008 baseEnd_5889008 := by
    simpa [prefixWord, tailWord_5889008, baseEnd_5889008] using wordTrace_append hprefix tailTrace_5889008
  have hstable : (prefixWord ++ tailWord_5889008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889008).length < 2 ^ (prefixWord ++ tailWord_5889008).sum := by decide
  have hdescent : baseEnd_5889008 < baseStart_5889008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889009 : List Nat := [1, 2, 2, 2, 4, 2, 2, 3, 1, 1, 3]
def baseStart_5889009 : Nat := 118140960795 + 5889009 * 2 ^ 59
def prefixEnd_5889009 : Nat := 4983230072969 + 3 ^ 40 * 5889009 * 2
def baseEnd_5889009 : Nat := 3023892195653454958904447

theorem tailTrace_5889009 : CollatzResearch.WordTrace tailWord_5889009 prefixEnd_5889009 3023892195653454958904447 := by
  unfold tailWord_5889009
  simp only [CollatzResearch.WordTrace]
  refine ⟨214789803922133630509454081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143193202614755753672969387 214789803922133630509454081)
  ·
    refine ⟨161092352941600222882090561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214789803922133630509454081 161092352941600222882090561)
    ·
      refine ⟨120819264706200167161567921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161092352941600222882090561 120819264706200167161567921)
      ·
        refine ⟨90614448529650125371175941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120819264706200167161567921 90614448529650125371175941)
        ·
          refine ⟨16990209099309398507095489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90614448529650125371175941 16990209099309398507095489)
          ·
            refine ⟨12742656824482048880321617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16990209099309398507095489 12742656824482048880321617)
            ·
              refine ⟨9556992618361536660241213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12742656824482048880321617 9556992618361536660241213)
              ·
                refine ⟨3583872231885576247590455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9556992618361536660241213 3583872231885576247590455)
                ·
                  refine ⟨5375808347828364371385683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583872231885576247590455 5375808347828364371385683)
                  ·
                    refine ⟨8063712521742546557078525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5375808347828364371385683 8063712521742546557078525)
                    ·
                      refine ⟨3023892195653454958904447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8063712521742546557078525 3023892195653454958904447)
                      ·
                        rfl

theorem cell23_5889009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_5889009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889009 prefixEnd_5889009 := by exact prefixLift 5889009
  have htrace : WordTrace (prefixWord ++ tailWord_5889009) baseStart_5889009 baseEnd_5889009 := by
    simpa [prefixWord, tailWord_5889009, baseEnd_5889009] using wordTrace_append hprefix tailTrace_5889009
  have hstable : (prefixWord ++ tailWord_5889009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889009).length < 2 ^ (prefixWord ++ tailWord_5889009).sum := by decide
  have hdescent : baseEnd_5889009 < baseStart_5889009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889011 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 6]
def baseStart_5889011 : Nat := 118140960795 + 5889011 * 2 ^ 59
def prefixEnd_5889011 : Nat := 4983230072969 + 3 ^ 40 * 5889011 * 2
def baseEnd_5889011 : Nat := 3023893222614763951079437

theorem tailTrace_5889011 : CollatzResearch.WordTrace tailWord_5889011 prefixEnd_5889011 3023893222614763951079437 := by
  unfold tailWord_5889011
  simp only [CollatzResearch.WordTrace]
  refine ⟨214789876868126384851026887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143193251245417589900684591 214789876868126384851026887)
  ·
    refine ⟨322184815302189577276540331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214789876868126384851026887 322184815302189577276540331)
    ·
      refine ⟨483277222953284365914810497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322184815302189577276540331 483277222953284365914810497)
      ·
        refine ⟨362457917214963274436107873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483277222953284365914810497 362457917214963274436107873)
        ·
          refine ⟨271843437911222455827080905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362457917214963274436107873 271843437911222455827080905)
          ·
            refine ⟨203882578433416841870310679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271843437911222455827080905 203882578433416841870310679)
            ·
              refine ⟨305823867650125262805466019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203882578433416841870310679 305823867650125262805466019)
              ·
                refine ⟨458735801475187894208199029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305823867650125262805466019 458735801475187894208199029)
                ·
                  refine ⟨43006481388298865082018659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 458735801475187894208199029 43006481388298865082018659)
                  ·
                    refine ⟨64509722082448297623027989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43006481388298865082018659 64509722082448297623027989)
                    ·
                      refine ⟨3023893222614763951079437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64509722082448297623027989 3023893222614763951079437)
                      ·
                        rfl

theorem cell23_5889011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_5889011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889011 prefixEnd_5889011 := by exact prefixLift 5889011
  have htrace : WordTrace (prefixWord ++ tailWord_5889011) baseStart_5889011 baseEnd_5889011 := by
    simpa [prefixWord, tailWord_5889011, baseEnd_5889011] using wordTrace_append hprefix tailTrace_5889011
  have hstable : (prefixWord ++ tailWord_5889011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889011).length < 2 ^ (prefixWord ++ tailWord_5889011).sum := by decide
  have hdescent : baseEnd_5889011 < baseStart_5889011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889025 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 4, 4]
def baseStart_5889025 : Nat := 118140960795 + 5889025 * 2 ^ 59
def prefixEnd_5889025 : Nat := 4983230072969 + 3 ^ 40 * 5889025 * 2
def baseEnd_5889025 : Nat := 1007966803781308965434791

theorem tailTrace_5889025 : CollatzResearch.WordTrace tailWord_5889025 prefixEnd_5889025 1007966803781308965434791 := by
  unfold tailWord_5889025
  simp only [CollatzResearch.WordTrace]
  refine ⟨214790387490075665242036529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143193591660050443494691019 214790387490075665242036529)
  ·
    refine ⟨161092790617556748931527397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214790387490075665242036529 161092790617556748931527397)
    ·
      refine ⟨30204898240791890424661387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161092790617556748931527397 30204898240791890424661387)
      ·
        refine ⟨45307347361187835636992081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30204898240791890424661387 45307347361187835636992081)
        ·
          refine ⟨33980510520890876727744061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45307347361187835636992081 33980510520890876727744061)
          ·
            refine ⟨12742691445334078772904023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33980510520890876727744061 12742691445334078772904023)
            ·
              refine ⟨19114037168001118159356035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12742691445334078772904023 19114037168001118159356035)
              ·
                refine ⟨28671055752001677239034053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19114037168001118159356035 28671055752001677239034053)
                ·
                  refine ⟨5375822953500314482318885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28671055752001677239034053 5375822953500314482318885)
                  ·
                    refine ⟨1007966803781308965434791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5375822953500314482318885 1007966803781308965434791)
                    ·
                      rfl

theorem cell23_5889025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_5889025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889025 prefixEnd_5889025 := by exact prefixLift 5889025
  have htrace : WordTrace (prefixWord ++ tailWord_5889025) baseStart_5889025 baseEnd_5889025 := by
    simpa [prefixWord, tailWord_5889025, baseEnd_5889025] using wordTrace_append hprefix tailTrace_5889025
  have hstable : (prefixWord ++ tailWord_5889025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889025).length < 2 ^ (prefixWord ++ tailWord_5889025).sum := by decide
  have hdescent : baseEnd_5889025 < baseStart_5889025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889026 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_5889026 : Nat := 118140960795 + 5889026 * 2 ^ 59
def prefixEnd_5889026 : Nat := 4983230072969 + 3 ^ 40 * 5889026 * 2
def baseEnd_5889026 : Nat := 3023900924824581392391869

theorem tailTrace_5889026 : CollatzResearch.WordTrace tailWord_5889026 prefixEnd_5889026 3023900924824581392391869 := by
  unfold tailWord_5889026
  simp only [CollatzResearch.WordTrace]
  refine ⟨53697605990768010603205733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143193615975381361608548621 53697605990768010603205733)
  ·
    refine ⟨10068301123269001988101075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53697605990768010603205733 10068301123269001988101075)
    ·
      refine ⟨15102451684903502982151613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10068301123269001988101075 15102451684903502982151613)
      ·
        refine ⟨5663419381838813618306855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15102451684903502982151613 5663419381838813618306855)
        ·
          refine ⟨8495129072758220427460283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5663419381838813618306855 8495129072758220427460283)
          ·
            refine ⟨12742693609137330641190425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8495129072758220427460283 12742693609137330641190425)
            ·
              refine ⟨9557020206852997980892819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12742693609137330641190425 9557020206852997980892819)
              ·
                refine ⟨14335530310279496971339229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9557020206852997980892819 14335530310279496971339229)
                ·
                  refine ⟨5375823866354811364252211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14335530310279496971339229 5375823866354811364252211)
                  ·
                    refine ⟨8063735799532217046378317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5375823866354811364252211 8063735799532217046378317)
                    ·
                      refine ⟨3023900924824581392391869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8063735799532217046378317 3023900924824581392391869)
                      ·
                        rfl

theorem cell23_5889026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_5889026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889026 prefixEnd_5889026 := by exact prefixLift 5889026
  have htrace : WordTrace (prefixWord ++ tailWord_5889026) baseStart_5889026 baseEnd_5889026 := by
    simpa [prefixWord, tailWord_5889026, baseEnd_5889026] using wordTrace_append hprefix tailTrace_5889026
  have hstable : (prefixWord ++ tailWord_5889026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889026).length < 2 ^ (prefixWord ++ tailWord_5889026).sum := by decide
  have hdescent : baseEnd_5889026 < baseStart_5889026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889032 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 3, 2, 2]
def baseStart_5889032 : Nat := 118140960795 + 5889032 * 2 ^ 59
def prefixEnd_5889032 : Nat := 4983230072969 + 3 ^ 40 * 5889032 * 2
def baseEnd_5889032 : Nat := 3023904005708508368916841

theorem tailTrace_5889032 : CollatzResearch.WordTrace tailWord_5889032 prefixEnd_5889032 3023904005708508368916841 := by
  unfold tailWord_5889032
  simp only [CollatzResearch.WordTrace]
  refine ⟨107395321400525152718770675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143193761867366870291694233 107395321400525152718770675)
  ·
    refine ⟨161092982100787729078156013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107395321400525152718770675 161092982100787729078156013)
    ·
      refine ⟨60409868287795398404308505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161092982100787729078156013 60409868287795398404308505)
      ·
        refine ⟨45307401215846548803231379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60409868287795398404308505 45307401215846548803231379)
        ·
          refine ⟨67961101823769823204847069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45307401215846548803231379 67961101823769823204847069)
          ·
            refine ⟨25485413183913683701817651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67961101823769823204847069 25485413183913683701817651)
            ·
              refine ⟨38228119775870525552726477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25485413183913683701817651 38228119775870525552726477)
              ·
                refine ⟨14335544915951447082272429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38228119775870525552726477 14335544915951447082272429)
                ·
                  refine ⟨5375829343481792655852161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14335544915951447082272429 5375829343481792655852161)
                  ·
                    refine ⟨4031872007611344491889121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5375829343481792655852161 4031872007611344491889121)
                    ·
                      refine ⟨3023904005708508368916841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031872007611344491889121 3023904005708508368916841)
                      ·
                        rfl

theorem cell23_5889032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_5889032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889032 prefixEnd_5889032 := by exact prefixLift 5889032
  have htrace : WordTrace (prefixWord ++ tailWord_5889032) baseStart_5889032 baseEnd_5889032 := by
    simpa [prefixWord, tailWord_5889032, baseEnd_5889032] using wordTrace_append hprefix tailTrace_5889032
  have hstable : (prefixWord ++ tailWord_5889032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889032).length < 2 ^ (prefixWord ++ tailWord_5889032).sum := by decide
  have hdescent : baseEnd_5889032 < baseStart_5889032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889045 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_5889045 : Nat := 118140960795 + 5889045 * 2 ^ 59
def prefixEnd_5889045 : Nat := 4983230072969 + 3 ^ 40 * 5889045 * 2
def baseEnd_5889045 : Nat := 3023910680957016818054281

theorem tailTrace_5889045 : CollatzResearch.WordTrace tailWord_5889045 prefixEnd_5889045 3023910680957016818054281 := by
  unfold tailWord_5889045
  simp only [CollatzResearch.WordTrace]
  refine ⟨214791116950003208657764589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143194077966668805771843059 214791116950003208657764589)
  ·
    refine ⟨80546668856251203246661721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214791116950003208657764589 80546668856251203246661721)
    ·
      refine ⟨60410001642188402434996291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80546668856251203246661721 60410001642188402434996291)
      ·
        refine ⟨90615002463282603652494437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60410001642188402434996291 90615002463282603652494437)
        ·
          refine ⟨16990312961865488184842707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90615002463282603652494437 16990312961865488184842707)
          ·
            refine ⟨25485469442798232277264061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16990312961865488184842707 25485469442798232277264061)
            ·
              refine ⟨9557051041049337103974023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25485469442798232277264061 9557051041049337103974023)
              ·
                refine ⟨14335576561574005655961035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9557051041049337103974023 14335576561574005655961035)
                ·
                  refine ⟨21503364842361008483941553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14335576561574005655961035 21503364842361008483941553)
                  ·
                    refine ⟨16127523631770756362956165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21503364842361008483941553 16127523631770756362956165)
                    ·
                      refine ⟨3023910680957016818054281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16127523631770756362956165 3023910680957016818054281)
                      ·
                        rfl

theorem cell23_5889045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_5889045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889045 prefixEnd_5889045 := by exact prefixLift 5889045
  have htrace : WordTrace (prefixWord ++ tailWord_5889045) baseStart_5889045 baseEnd_5889045 := by
    simpa [prefixWord, tailWord_5889045, baseEnd_5889045] using wordTrace_append hprefix tailTrace_5889045
  have hstable : (prefixWord ++ tailWord_5889045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889045).length < 2 ^ (prefixWord ++ tailWord_5889045).sum := by decide
  have hdescent : baseEnd_5889045 < baseStart_5889045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889051 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 3, 9]
def baseStart_5889051 : Nat := 118140960795 + 5889051 * 2 ^ 59
def prefixEnd_5889051 : Nat := 4983230072969 + 3 ^ 40 * 5889051 * 2
def baseEnd_5889051 : Nat := 1007971253946981264859751

theorem tailTrace_5889051 : CollatzResearch.WordTrace tailWord_5889051 prefixEnd_5889051 1007971253946981264859751 := by
  unfold tailWord_5889051
  simp only [CollatzResearch.WordTrace]
  refine ⟨214791335787981471682483007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143194223858654314454988671 214791335787981471682483007)
  ·
    refine ⟨322187003681972207523724511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214791335787981471682483007 322187003681972207523724511)
    ·
      refine ⟨483280505522958311285586767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322187003681972207523724511 483280505522958311285586767)
      ·
        refine ⟨724920758284437466928380151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483280505522958311285586767 724920758284437466928380151)
        ·
          refine ⟨1087381137426656200392570227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724920758284437466928380151 1087381137426656200392570227)
          ·
            refine ⟨1631071706139984300588855341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087381137426656200392570227 1631071706139984300588855341)
            ·
              refine ⟨611651889802494112720820753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1631071706139984300588855341 611651889802494112720820753)
              ·
                refine ⟨458738917351870584540615565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611651889802494112720820753 458738917351870584540615565)
                ·
                  refine ⟨172027094006951469202730837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458738917351870584540615565 172027094006951469202730837)
                  ·
                    refine ⟨1007971253946981264859751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 172027094006951469202730837 1007971253946981264859751)
                    ·
                      rfl

theorem cell23_5889051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 9].length) (baseStart_5889051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889051 prefixEnd_5889051 := by exact prefixLift 5889051
  have htrace : WordTrace (prefixWord ++ tailWord_5889051) baseStart_5889051 baseEnd_5889051 := by
    simpa [prefixWord, tailWord_5889051, baseEnd_5889051] using wordTrace_append hprefix tailTrace_5889051
  have hstable : (prefixWord ++ tailWord_5889051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889051).length < 2 ^ (prefixWord ++ tailWord_5889051).sum := by decide
  have hdescent : baseEnd_5889051 < baseStart_5889051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889055 : List Nat := [1, 1, 2, 4, 1, 5, 2, 7]
def baseStart_5889055 : Nat := 118140960795 + 5889055 * 2 ^ 59
def prefixEnd_5889055 : Nat := 4983230072969 + 3 ^ 40 * 5889055 * 2
def baseEnd_5889055 : Nat := 111996882065317102923305

theorem tailTrace_5889055 : CollatzResearch.WordTrace tailWord_5889055 prefixEnd_5889055 111996882065317102923305 := by
  unfold tailWord_5889055
  simp only [CollatzResearch.WordTrace]
  refine ⟨214791481679966980365628619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143194321119977986910419079 214791481679966980365628619)
  ·
    refine ⟨322187222519950470548442929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214791481679966980365628619 322187222519950470548442929)
    ·
      refine ⟨241640416889962852911332197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322187222519950470548442929 241640416889962852911332197)
      ·
        refine ⟨45307578166868034920874787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241640416889962852911332197 45307578166868034920874787)
        ·
          refine ⟨67961367250302052381312181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45307578166868034920874787 67961367250302052381312181)
          ·
            refine ⟨6371378179715817410748017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67961367250302052381312181 6371378179715817410748017)
            ·
              refine ⟨4778533634786863058061013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6371378179715817410748017 4778533634786863058061013)
              ·
                refine ⟨111996882065317102923305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4778533634786863058061013 111996882065317102923305)
                ·
                  rfl

theorem cell23_5889055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 7].length) (baseStart_5889055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889055 prefixEnd_5889055 := by exact prefixLift 5889055
  have htrace : WordTrace (prefixWord ++ tailWord_5889055) baseStart_5889055 baseEnd_5889055 := by
    simpa [prefixWord, tailWord_5889055, baseEnd_5889055] using wordTrace_append hprefix tailTrace_5889055
  have hstable : (prefixWord ++ tailWord_5889055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889055).length < 2 ^ (prefixWord ++ tailWord_5889055).sum := by decide
  have hdescent : baseEnd_5889055 < baseStart_5889055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889075 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 5, 3, 2]
def baseStart_5889075 : Nat := 118140960795 + 5889075 * 2 ^ 59
def prefixEnd_5889075 : Nat := 4983230072969 + 3 ^ 40 * 5889075 * 2
def baseEnd_5889075 : Nat := 3023926085376651700679143

theorem tailTrace_5889075 : CollatzResearch.WordTrace tailWord_5889075 prefixEnd_5889075 3023926085376651700679143 := by
  unfold tailWord_5889075
  simp only [CollatzResearch.WordTrace]
  refine ⟨214792211139894523781356679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143194807426596349187571119 214792211139894523781356679)
  ·
    refine ⟨322188316709841785672035019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214792211139894523781356679 322188316709841785672035019)
    ·
      refine ⟨483282475064762678508052529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322188316709841785672035019 483282475064762678508052529)
      ·
        refine ⟨362461856298572008881039397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483282475064762678508052529 362461856298572008881039397)
        ·
          refine ⟨67961598055982251665194887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362461856298572008881039397 67961598055982251665194887)
          ·
            refine ⟨101942397083973377497792331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67961598055982251665194887 101942397083973377497792331)
            ·
              refine ⟨152913595625960066246688497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101942397083973377497792331 152913595625960066246688497)
              ·
                refine ⟨114685196719470049685016373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152913595625960066246688497 114685196719470049685016373)
                ·
                  refine ⟨10751737192450317157970285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114685196719470049685016373 10751737192450317157970285)
                  ·
                    refine ⟨4031901447168868934238857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10751737192450317157970285 4031901447168868934238857)
                    ·
                      refine ⟨3023926085376651700679143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031901447168868934238857 3023926085376651700679143)
                      ·
                        rfl

theorem cell23_5889075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 3, 2].length) (baseStart_5889075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889075 prefixEnd_5889075 := by exact prefixLift 5889075
  have htrace : WordTrace (prefixWord ++ tailWord_5889075) baseStart_5889075 baseEnd_5889075 := by
    simpa [prefixWord, tailWord_5889075, baseEnd_5889075] using wordTrace_append hprefix tailTrace_5889075
  have hstable : (prefixWord ++ tailWord_5889075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889075).length < 2 ^ (prefixWord ++ tailWord_5889075).sum := by decide
  have hdescent : baseEnd_5889075 < baseStart_5889075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889088 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 4]
def baseStart_5889088 : Nat := 118140960795 + 5889088 * 2 ^ 59
def prefixEnd_5889088 : Nat := 4983230072969 + 3 ^ 40 * 5889088 * 2
def baseEnd_5889088 : Nat := 3023932760625160149816583

theorem tailTrace_5889088 : CollatzResearch.WordTrace tailWord_5889088 prefixEnd_5889088 3023932760625160149816583 := by
  unfold tailWord_5889088
  simp only [CollatzResearch.WordTrace]
  refine ⟨107396342644423713500789959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143195123525898284667719945 107396342644423713500789959)
  ·
    refine ⟨161094513966635570251184939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107396342644423713500789959 161094513966635570251184939)
    ·
      refine ⟨241641770949953355376777409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161094513966635570251184939 241641770949953355376777409)
      ·
        refine ⟨181231328212465016532583057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241641770949953355376777409 181231328212465016532583057)
        ·
          refine ⟨135923496159348762399437293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181231328212465016532583057 135923496159348762399437293)
          ·
            refine ⟨50971311059755785899788985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135923496159348762399437293 50971311059755785899788985)
            ·
              refine ⟨38228483294816839424841739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50971311059755785899788985 38228483294816839424841739)
              ·
                refine ⟨57342724942225259137262609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38228483294816839424841739 57342724942225259137262609)
                ·
                  refine ⟨43007043706668944352946957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57342724942225259137262609 43007043706668944352946957)
                  ·
                    refine ⟨16127641390000854132355109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43007043706668944352946957 16127641390000854132355109)
                    ·
                      refine ⟨3023932760625160149816583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16127641390000854132355109 3023932760625160149816583)
                      ·
                        rfl

theorem cell23_5889088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_5889088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889088 prefixEnd_5889088 := by exact prefixLift 5889088
  have htrace : WordTrace (prefixWord ++ tailWord_5889088) baseStart_5889088 baseEnd_5889088 := by
    simpa [prefixWord, tailWord_5889088, baseEnd_5889088] using wordTrace_append hprefix tailTrace_5889088
  have hstable : (prefixWord ++ tailWord_5889088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889088).length < 2 ^ (prefixWord ++ tailWord_5889088).sum := by decide
  have hdescent : baseEnd_5889088 < baseStart_5889088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889098 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 2, 6]
def baseStart_5889098 : Nat := 118140960795 + 5889098 * 2 ^ 59
def prefixEnd_5889098 : Nat := 4983230072969 + 3 ^ 40 * 5889098 * 2
def baseEnd_5889098 : Nat := 1007979298477235036897179

theorem tailTrace_5889098 : CollatzResearch.WordTrace tailWord_5889098 prefixEnd_5889098 1007979298477235036897179 := by
  unfold tailWord_5889098
  simp only [CollatzResearch.WordTrace]
  refine ⟨53698262504702799677360987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143195366679207465806295965 53698262504702799677360987)
  ·
    refine ⟨80547393757054199516041481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53698262504702799677360987 80547393757054199516041481)
    ·
      refine ⟨60410545317790649637031111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80547393757054199516041481 60410545317790649637031111)
      ·
        refine ⟨90615817976685974455546667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60410545317790649637031111 90615817976685974455546667)
        ·
          refine ⟨135923726965028961683320001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90615817976685974455546667 135923726965028961683320001)
          ·
            refine ⟨101942795223771721262490001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135923726965028961683320001 101942795223771721262490001)
            ·
              refine ⟨76457096417828790946867501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101942795223771721262490001 76457096417828790946867501)
              ·
                refine ⟨28671411156685796605075313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76457096417828790946867501 28671411156685796605075313)
                ·
                  refine ⟨21503558367514347453806485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28671411156685796605075313 21503558367514347453806485)
                  ·
                    refine ⟨1007979298477235036897179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21503558367514347453806485 1007979298477235036897179)
                    ·
                      rfl

theorem cell23_5889098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_5889098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889098 prefixEnd_5889098 := by exact prefixLift 5889098
  have htrace : WordTrace (prefixWord ++ tailWord_5889098) baseStart_5889098 baseEnd_5889098 := by
    simpa [prefixWord, tailWord_5889098, baseEnd_5889098] using wordTrace_append hprefix tailTrace_5889098
  have hstable : (prefixWord ++ tailWord_5889098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889098).length < 2 ^ (prefixWord ++ tailWord_5889098).sum := by decide
  have hdescent : baseEnd_5889098 < baseStart_5889098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889155 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 3]
def baseStart_5889155 : Nat := 118140960795 + 5889155 * 2 ^ 59
def prefixEnd_5889155 : Nat := 4983230072969 + 3 ^ 40 * 5889155 * 2
def baseEnd_5889155 : Nat := 3023967163829011387678775

theorem tailTrace_5889155 : CollatzResearch.WordTrace tailWord_5889155 prefixEnd_5889155 3023967163829011387678775 := by
  unfold tailWord_5889155
  simp only [CollatzResearch.WordTrace]
  refine ⟨214795128979604697444268919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143196752653069798296179279 214795128979604697444268919)
  ·
    refine ⟨322192693469407046166403379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214795128979604697444268919 322192693469407046166403379)
    ·
      refine ⟨483289040204110569249605069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322192693469407046166403379 483289040204110569249605069)
      ·
        refine ⟨181233390076541463468601901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 483289040204110569249605069 181233390076541463468601901)
        ·
          refine ⟨67962521278703048800725713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181233390076541463468601901 67962521278703048800725713)
          ·
            refine ⟨50971890959027286600544285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67962521278703048800725713 50971890959027286600544285)
            ·
              refine ⟨19114459109635232475204107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50971890959027286600544285 19114459109635232475204107)
              ·
                refine ⟨28671688664452848712806161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19114459109635232475204107 28671688664452848712806161)
                ·
                  refine ⟨21503766498339636534604621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28671688664452848712806161 21503766498339636534604621)
                  ·
                    refine ⟨8063912436877363700476733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21503766498339636534604621 8063912436877363700476733)
                    ·
                      refine ⟨3023967163829011387678775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8063912436877363700476733 3023967163829011387678775)
                      ·
                        rfl

theorem cell23_5889155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_5889155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889155 prefixEnd_5889155 := by exact prefixLift 5889155
  have htrace : WordTrace (prefixWord ++ tailWord_5889155) baseStart_5889155 baseEnd_5889155 := by
    simpa [prefixWord, tailWord_5889155, baseEnd_5889155] using wordTrace_append hprefix tailTrace_5889155
  have hstable : (prefixWord ++ tailWord_5889155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889155).length < 2 ^ (prefixWord ++ tailWord_5889155).sum := by decide
  have hdescent : baseEnd_5889155 < baseStart_5889155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889168 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 5]
def baseStart_5889168 : Nat := 118140960795 + 5889168 * 2 ^ 59
def prefixEnd_5889168 : Nat := 4983230072969 + 3 ^ 40 * 5889168 * 2
def baseEnd_5889168 : Nat := 3023973839077519836816215

theorem tailTrace_5889168 : CollatzResearch.WordTrace tailWord_5889168 prefixEnd_5889168 3023973839077519836816215 := by
  unfold tailWord_5889168
  simp only [CollatzResearch.WordTrace]
  refine ⟨107397801564278800332246079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143197068752371733776328105 107397801564278800332246079)
  ·
    refine ⟨161096702346418200498369119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107397801564278800332246079 161096702346418200498369119)
    ·
      refine ⟨241645053519627300747553679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161096702346418200498369119 241645053519627300747553679)
      ·
        refine ⟨362467580279440951121330519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241645053519627300747553679 362467580279440951121330519)
        ·
          refine ⟨543701370419161426681995779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362467580279440951121330519 543701370419161426681995779)
          ·
            refine ⟨815552055628742140022993669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543701370419161426681995779 815552055628742140022993669)
            ·
              refine ⟨152916010430389151254311313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 815552055628742140022993669 152916010430389151254311313)
              ·
                refine ⟨114687007822791863440733485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152916010430389151254311313 114687007822791863440733485)
                ·
                  refine ⟨43007627933546948790275057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114687007822791863440733485 43007627933546948790275057)
                  ·
                    refine ⟨32255720950160211592706293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43007627933546948790275057 32255720950160211592706293)
                    ·
                      refine ⟨3023973839077519836816215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32255720950160211592706293 3023973839077519836816215)
                      ·
                        rfl

theorem cell23_5889168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_5889168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889168 prefixEnd_5889168 := by exact prefixLift 5889168
  have htrace : WordTrace (prefixWord ++ tailWord_5889168) baseStart_5889168 baseEnd_5889168 := by
    simpa [prefixWord, tailWord_5889168, baseEnd_5889168] using wordTrace_append hprefix tailTrace_5889168
  have hstable : (prefixWord ++ tailWord_5889168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889168).length < 2 ^ (prefixWord ++ tailWord_5889168).sum := by decide
  have hdescent : baseEnd_5889168 < baseStart_5889168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889175 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 1, 7]
def baseStart_5889175 : Nat := 118140960795 + 5889175 * 2 ^ 59
def prefixEnd_5889175 : Nat := 4983230072969 + 3 ^ 40 * 5889175 * 2
def baseEnd_5889175 : Nat := 1007992477814033769809561

theorem tailTrace_5889175 : CollatzResearch.WordTrace tailWord_5889175 prefixEnd_5889175 1007992477814033769809561 := by
  unfold tailWord_5889175
  simp only [CollatzResearch.WordTrace]
  refine ⟨214795858439532240859996979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143197238959688160573331319 214795858439532240859996979)
  ·
    refine ⟨322193787659298361289995469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214795858439532240859996979 322193787659298361289995469)
    ·
      refine ⟨120822670372236885483748301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322193787659298361289995469 120822670372236885483748301)
      ·
        refine ⟨45308501389588832056405613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120822670372236885483748301 45308501389588832056405613)
        ·
          refine ⟨16990688021095812021152105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45308501389588832056405613 16990688021095812021152105)
          ·
            refine ⟨12743016015821859015864079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16990688021095812021152105 12743016015821859015864079)
            ·
              refine ⟨19114524023732788523796119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12743016015821859015864079 19114524023732788523796119)
              ·
                refine ⟨28671786035599182785694179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19114524023732788523796119 28671786035599182785694179)
                ·
                  refine ⟨43007679053398774178541269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28671786035599182785694179 43007679053398774178541269)
                  ·
                    refine ⟨1007992477814033769809561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43007679053398774178541269 1007992477814033769809561)
                    ·
                      rfl

theorem cell23_5889175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_5889175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889175 prefixEnd_5889175 := by exact prefixLift 5889175
  have htrace : WordTrace (prefixWord ++ tailWord_5889175) baseStart_5889175 baseEnd_5889175 := by
    simpa [prefixWord, tailWord_5889175, baseEnd_5889175] using wordTrace_append hprefix tailTrace_5889175
  have hstable : (prefixWord ++ tailWord_5889175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889175).length < 2 ^ (prefixWord ++ tailWord_5889175).sum := by decide
  have hdescent : baseEnd_5889175 < baseStart_5889175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889195 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 2, 10, 2]
def baseStart_5889195 : Nat := 118140960795 + 5889195 * 2 ^ 59
def prefixEnd_5889195 : Nat := 4983230072969 + 3 ^ 40 * 5889195 * 2
def baseEnd_5889195 : Nat := 3023987703055191231178591

theorem tailTrace_5889195 : CollatzResearch.WordTrace tailWord_5889195 prefixEnd_5889195 3023987703055191231178591 := by
  unfold tailWord_5889195
  simp only [CollatzResearch.WordTrace]
  refine ⟨214796587899459784275725039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143197725266306522850483359 214796587899459784275725039)
  ·
    refine ⟨322194881849189676413587559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214796587899459784275725039 322194881849189676413587559)
    ·
      refine ⟨483292322773784514620381339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322194881849189676413587559 483292322773784514620381339)
      ·
        refine ⟨724938484160676771930572009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483292322773784514620381339 724938484160676771930572009)
        ·
          refine ⟨543703863120507578947929007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724938484160676771930572009 543703863120507578947929007)
          ·
            refine ⟨815555794680761368421893511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543703863120507578947929007 815555794680761368421893511)
            ·
              refine ⟨1223333692021142052632840267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815555794680761368421893511 1223333692021142052632840267)
              ·
                refine ⟨1835000538031713078949260401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223333692021142052632840267 1835000538031713078949260401)
                ·
                  refine ⟨1376250403523784809211945301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1835000538031713078949260401 1376250403523784809211945301)
                  ·
                    refine ⟨4031983604073588308238121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1376250403523784809211945301 4031983604073588308238121)
                    ·
                      refine ⟨3023987703055191231178591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4031983604073588308238121 3023987703055191231178591)
                      ·
                        rfl

theorem cell23_5889195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 10, 2].length) (baseStart_5889195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889195 prefixEnd_5889195 := by exact prefixLift 5889195
  have htrace : WordTrace (prefixWord ++ tailWord_5889195) baseStart_5889195 baseEnd_5889195 := by
    simpa [prefixWord, tailWord_5889195, baseEnd_5889195] using wordTrace_append hprefix tailTrace_5889195
  have hstable : (prefixWord ++ tailWord_5889195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889195).length < 2 ^ (prefixWord ++ tailWord_5889195).sum := by decide
  have hdescent : baseEnd_5889195 < baseStart_5889195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889215 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 3]
def baseStart_5889215 : Nat := 118140960795 + 5889215 * 2 ^ 59
def prefixEnd_5889215 : Nat := 4983230072969 + 3 ^ 40 * 5889215 * 2
def baseEnd_5889215 : Nat := 3023997972668281152928499

theorem tailTrace_5889215 : CollatzResearch.WordTrace tailWord_5889215 prefixEnd_5889215 3023997972668281152928499 := by
  unfold tailWord_5889215
  simp only [CollatzResearch.WordTrace]
  refine ⟨214797317359387327691453099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143198211572924885127635399 214797317359387327691453099)
  ·
    refine ⟨322195976039080991537179649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214797317359387327691453099 322195976039080991537179649)
    ·
      refine ⟨241646982029310743652884737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322195976039080991537179649 241646982029310743652884737)
      ·
        refine ⟨181235236521983057739663553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241646982029310743652884737 181235236521983057739663553)
        ·
          refine ⟨135926427391487293304747665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181235236521983057739663553 135926427391487293304747665)
          ·
            refine ⟨101944820543615469978560749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135926427391487293304747665 101944820543615469978560749)
            ·
              refine ⟨38229307703855801241960281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101944820543615469978560749 38229307703855801241960281)
              ·
                refine ⟨28671980777891850931470211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38229307703855801241960281 28671980777891850931470211)
                ·
                  refine ⟨43007971166837776397205317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28671980777891850931470211 43007971166837776397205317)
                  ·
                    refine ⟨8063994593782083074475997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43007971166837776397205317 8063994593782083074475997)
                    ·
                      refine ⟨3023997972668281152928499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8063994593782083074475997 3023997972668281152928499)
                      ·
                        rfl

theorem cell23_5889215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_5889215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889215 prefixEnd_5889215 := by exact prefixLift 5889215
  have htrace : WordTrace (prefixWord ++ tailWord_5889215) baseStart_5889215 baseEnd_5889215 := by
    simpa [prefixWord, tailWord_5889215, baseEnd_5889215] using wordTrace_append hprefix tailTrace_5889215
  have hstable : (prefixWord ++ tailWord_5889215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889215).length < 2 ^ (prefixWord ++ tailWord_5889215).sum := by decide
  have hdescent : baseEnd_5889215 < baseStart_5889215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889239 : List Nat := [1, 1, 3, 2, 1, 2, 5, 3, 1, 4]
def baseStart_5889239 : Nat := 118140960795 + 5889239 * 2 ^ 59
def prefixEnd_5889239 : Nat := 4983230072969 + 3 ^ 40 * 5889239 * 2
def baseEnd_5889239 : Nat := 1008003432067996353009463

theorem tailTrace_5889239 : CollatzResearch.WordTrace tailWord_5889239 prefixEnd_5889239 1008003432067996353009463 := by
  unfold tailWord_5889239
  simp only [CollatzResearch.WordTrace]
  refine ⟨214798192711300379790326771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143198795140866919860217847 214798192711300379790326771)
  ·
    refine ⟨322197289066950569685490157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214798192711300379790326771 322197289066950569685490157)
    ·
      refine ⟨120823983400106463632058809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322197289066950569685490157 120823983400106463632058809)
      ·
        refine ⟨90617987550079847724044107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120823983400106463632058809 90617987550079847724044107)
        ·
          refine ⟨135926981325119771586066161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90617987550079847724044107 135926981325119771586066161)
          ·
            refine ⟨101945235993839828689549621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135926981325119771586066161 101945235993839828689549621)
            ·
              refine ⟨9557365874422483939645277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101945235993839828689549621 9557365874422483939645277)
              ·
                refine ⟨3584012202908431477366979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9557365874422483939645277 3584012202908431477366979)
                ·
                  refine ⟨5376018304362647216050469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3584012202908431477366979 5376018304362647216050469)
                  ·
                    refine ⟨1008003432067996353009463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5376018304362647216050469 1008003432067996353009463)
                    ·
                      rfl

theorem cell23_5889239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_5889239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889239 prefixEnd_5889239 := by exact prefixLift 5889239
  have htrace : WordTrace (prefixWord ++ tailWord_5889239) baseStart_5889239 baseEnd_5889239 := by
    simpa [prefixWord, tailWord_5889239, baseEnd_5889239] using wordTrace_append hprefix tailTrace_5889239
  have hstable : (prefixWord ++ tailWord_5889239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889239).length < 2 ^ (prefixWord ++ tailWord_5889239).sum := by decide
  have hdescent : baseEnd_5889239 < baseStart_5889239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889256 : List Nat := [2, 1, 4, 1, 2, 1, 5, 2, 1, 4]
def baseStart_5889256 : Nat := 118140960795 + 5889256 * 2 ^ 59
def prefixEnd_5889256 : Nat := 4983230072969 + 3 ^ 40 * 5889256 * 2
def baseEnd_5889256 : Nat := 1008006341791705164171937

theorem tailTrace_5889256 : CollatzResearch.WordTrace tailWord_5889256 prefixEnd_5889256 1008006341791705164171937 := by
  unfold tailWord_5889256
  simp only [CollatzResearch.WordTrace]
  refine ⟨107399406376119395846847811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143199208501492527795797081 107399406376119395846847811)
  ·
    refine ⟨161099109564179093770271717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107399406376119395846847811 161099109564179093770271717)
    ·
      refine ⟨30206083043283580081925947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161099109564179093770271717 30206083043283580081925947)
      ·
        refine ⟨45309124564925370122888921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30206083043283580081925947 45309124564925370122888921)
        ·
          refine ⟨33981843423694027592166691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45309124564925370122888921 33981843423694027592166691)
          ·
            refine ⟨50972765135541041388250037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33981843423694027592166691 50972765135541041388250037)
            ·
              refine ⟨4778696731456972630148441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50972765135541041388250037 4778696731456972630148441)
              ·
                refine ⟨3584022548592729472611331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4778696731456972630148441 3584022548592729472611331)
                ·
                  refine ⟨5376033822889094208916997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3584022548592729472611331 5376033822889094208916997)
                  ·
                    refine ⟨1008006341791705164171937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5376033822889094208916997 1008006341791705164171937)
                    ·
                      rfl

theorem cell23_5889256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_5889256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889256 prefixEnd_5889256 := by exact prefixLift 5889256
  have htrace : WordTrace (prefixWord ++ tailWord_5889256) baseStart_5889256 baseEnd_5889256 := by
    simpa [prefixWord, tailWord_5889256, baseEnd_5889256] using wordTrace_append hprefix tailTrace_5889256
  have hstable : (prefixWord ++ tailWord_5889256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889256).length < 2 ^ (prefixWord ++ tailWord_5889256).sum := by decide
  have hdescent : baseEnd_5889256 < baseStart_5889256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889265 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 3, 5]
def baseStart_5889265 : Nat := 118140960795 + 5889265 * 2 ^ 59
def prefixEnd_5889265 : Nat := 4983230072969 + 3 ^ 40 * 5889265 * 2
def baseEnd_5889265 : Nat := 1008007882233668652434423

theorem tailTrace_5889265 : CollatzResearch.WordTrace tailWord_5889265 prefixEnd_5889265 1008007882233668652434423 := by
  unfold tailWord_5889265
  simp only [CollatzResearch.WordTrace]
  refine ⟨214799141009206186230773249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143199427339470790820515499 214799141009206186230773249)
  ·
    refine ⟨161099355756904639673079937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214799141009206186230773249 161099355756904639673079937)
    ·
      refine ⟨120824516817678479754809953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161099355756904639673079937 120824516817678479754809953)
      ·
        refine ⟨90618387613258859816107465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120824516817678479754809953 90618387613258859816107465)
        ·
          refine ⟨67963790709944144862080599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90618387613258859816107465 67963790709944144862080599)
          ·
            refine ⟨101945686064916217293120899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67963790709944144862080599 101945686064916217293120899)
            ·
              refine ⟨152918529097374325939681349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101945686064916217293120899 152918529097374325939681349)
              ·
                refine ⟨28672224205757686113690253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152918529097374325939681349 28672224205757686113690253)
                ·
                  refine ⟨10752084077159132292633845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28672224205757686113690253 10752084077159132292633845)
                  ·
                    refine ⟨1008007882233668652434423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10752084077159132292633845 1008007882233668652434423)
                    ·
                      rfl

theorem cell23_5889265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_5889265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889265 prefixEnd_5889265 := by exact prefixLift 5889265
  have htrace : WordTrace (prefixWord ++ tailWord_5889265) baseStart_5889265 baseEnd_5889265 := by
    simpa [prefixWord, tailWord_5889265, baseEnd_5889265] using wordTrace_append hprefix tailTrace_5889265
  have hstable : (prefixWord ++ tailWord_5889265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889265).length < 2 ^ (prefixWord ++ tailWord_5889265).sum := by decide
  have hdescent : baseEnd_5889265 < baseStart_5889265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889289 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 2, 3, 2]
def baseStart_5889289 : Nat := 118140960795 + 5889289 * 2 ^ 59
def prefixEnd_5889289 : Nat := 4983230072969 + 3 ^ 40 * 5889289 * 2
def baseEnd_5889289 : Nat := 3024035970236713863403159

theorem tailTrace_5889289 : CollatzResearch.WordTrace tailWord_5889289 prefixEnd_5889289 3024035970236713863403159 := by
  unfold tailWord_5889289
  simp only [CollatzResearch.WordTrace]
  refine ⟨214800016361119238329646921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143200010907412825553097947 214800016361119238329646921)
  ·
    refine ⟨161100012270839428747235191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214800016361119238329646921 161100012270839428747235191)
    ·
      refine ⟨241650018406259143120852787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161100012270839428747235191 241650018406259143120852787)
      ·
        refine ⟨362475027609388714681279181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241650018406259143120852787 362475027609388714681279181)
        ·
          refine ⟨135928135353520768005479693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362475027609388714681279181 135928135353520768005479693)
          ·
            refine ⟨50973050757570288002054885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135928135353520768005479693 50973050757570288002054885)
            ·
              refine ⟨9557447017044429000385291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50973050757570288002054885 9557447017044429000385291)
              ·
                refine ⟨14336170525566643500577937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9557447017044429000385291 14336170525566643500577937)
                ·
                  refine ⟨10752127894174982625433453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14336170525566643500577937 10752127894174982625433453)
                  ·
                    refine ⟨4032047960315618484537545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10752127894174982625433453 4032047960315618484537545)
                    ·
                      refine ⟨3024035970236713863403159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4032047960315618484537545 3024035970236713863403159)
                      ·
                        rfl

theorem cell23_5889289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 3, 2].length) (baseStart_5889289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889289 prefixEnd_5889289 := by exact prefixLift 5889289
  have htrace : WordTrace (prefixWord ++ tailWord_5889289) baseStart_5889289 baseEnd_5889289 := by
    simpa [prefixWord, tailWord_5889289, baseEnd_5889289] using wordTrace_append hprefix tailTrace_5889289
  have hstable : (prefixWord ++ tailWord_5889289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889289).length < 2 ^ (prefixWord ++ tailWord_5889289).sum := by decide
  have hdescent : baseEnd_5889289 < baseStart_5889289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889329 : List Nat := [1, 2, 2, 3, 3, 1, 2, 3, 2, 4]
def baseStart_5889329 : Nat := 118140960795 + 5889329 * 2 ^ 59
def prefixEnd_5889329 : Nat := 4983230072969 + 3 ^ 40 * 5889329 * 2
def baseEnd_5889329 : Nat := 1008018836487631235634325

theorem tailTrace_5889329 : CollatzResearch.WordTrace tailWord_5889329 prefixEnd_5889329 1008018836487631235634325 := by
  unfold tailWord_5889329
  simp only [CollatzResearch.WordTrace]
  refine ⟨214801475280974325161103041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143200983520649550107402027 214801475280974325161103041)
  ·
    refine ⟨161101106460730743870827281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214801475280974325161103041 161101106460730743870827281)
    ·
      refine ⟨120825829845548057903120461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161101106460730743870827281 120825829845548057903120461)
      ·
        refine ⟨45309686192080521713670173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120825829845548057903120461 45309686192080521713670173)
        ·
          refine ⟨16991132322030195642626315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45309686192080521713670173 16991132322030195642626315)
          ·
            refine ⟨25486698483045293463939473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16991132322030195642626315 25486698483045293463939473)
            ·
              refine ⟨19115023862283970097954605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25486698483045293463939473 19115023862283970097954605)
              ·
                refine ⟨7168133948356488786732977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19115023862283970097954605 7168133948356488786732977)
                ·
                  refine ⟨5376100461267366590049733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7168133948356488786732977 5376100461267366590049733)
                  ·
                    refine ⟨1008018836487631235634325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5376100461267366590049733 1008018836487631235634325)
                    ·
                      rfl

theorem cell23_5889329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_5889329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889329 prefixEnd_5889329 := by exact prefixLift 5889329
  have htrace : WordTrace (prefixWord ++ tailWord_5889329) baseStart_5889329 baseEnd_5889329 := by
    simpa [prefixWord, tailWord_5889329, baseEnd_5889329] using wordTrace_append hprefix tailTrace_5889329
  have hstable : (prefixWord ++ tailWord_5889329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889329).length < 2 ^ (prefixWord ++ tailWord_5889329).sum := by decide
  have hdescent : baseEnd_5889329 < baseStart_5889329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889356 : List Nat := [2, 2, 1, 3, 2, 2, 4, 1, 1, 2, 3]
def baseStart_5889356 : Nat := 118140960795 + 5889356 * 2 ^ 59
def prefixEnd_5889356 : Nat := 4983230072969 + 3 ^ 40 * 5889356 * 2
def baseEnd_5889356 : Nat := 3024070373440565101265351

theorem tailTrace_5889356 : CollatzResearch.WordTrace tailWord_5889356 prefixEnd_5889356 3024070373440565101265351 := by
  unfold tailWord_5889356
  simp only [CollatzResearch.WordTrace]
  refine ⟨107401230025938254386167961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143201640034584339181557281 107401230025938254386167961)
  ·
    refine ⟨80550922519453690789625971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107401230025938254386167961 80550922519453690789625971)
    ·
      refine ⟨120826383779180536184438957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80550922519453690789625971 120826383779180536184438957)
      ·
        refine ⟨45309893917192701069164609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120826383779180536184438957 45309893917192701069164609)
        ·
          refine ⟨33982420437894525801873457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45309893917192701069164609 33982420437894525801873457)
          ·
            refine ⟨25486815328420894351405093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33982420437894525801873457 25486815328420894351405093)
            ·
              refine ⟨4778777874078917690888455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25486815328420894351405093 4778777874078917690888455)
              ·
                refine ⟨7168166811118376536332683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4778777874078917690888455 7168166811118376536332683)
                ·
                  refine ⟨10752250216677564804499025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7168166811118376536332683 10752250216677564804499025)
                  ·
                    refine ⟨8064187662508173603374269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10752250216677564804499025 8064187662508173603374269)
                    ·
                      refine ⟨3024070373440565101265351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8064187662508173603374269 3024070373440565101265351)
                      ·
                        rfl

theorem cell23_5889356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_5889356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889356 prefixEnd_5889356 := by exact prefixLift 5889356
  have htrace : WordTrace (prefixWord ++ tailWord_5889356) baseStart_5889356 baseEnd_5889356 := by
    simpa [prefixWord, tailWord_5889356, baseEnd_5889356] using wordTrace_append hprefix tailTrace_5889356
  have hstable : (prefixWord ++ tailWord_5889356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889356).length < 2 ^ (prefixWord ++ tailWord_5889356).sum := by decide
  have hdescent : baseEnd_5889356 < baseStart_5889356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889373 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5889373 : Nat := 118140960795 + 5889373 * 2 ^ 59
def prefixEnd_5889373 : Nat := 4983230072969 + 3 ^ 40 * 5889373 * 2
def baseEnd_5889373 : Nat := 3024079102611691534752773

theorem tailTrace_5889373 : CollatzResearch.WordTrace tailWord_5889373 prefixEnd_5889373 3024079102611691534752773 := by
  unfold tailWord_5889373
  simp only [CollatzResearch.WordTrace]
  refine ⟨214803080092814920675704773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143202053395209947117136515 214803080092814920675704773)
  ·
    refine ⟨40275577517402797626694645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214803080092814920675704773 40275577517402797626694645)
    ·
      refine ⟨3775835392256512277502623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40275577517402797626694645 3775835392256512277502623)
      ·
        refine ⟨5663753088384768416253935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3775835392256512277502623 5663753088384768416253935)
        ·
          refine ⟨8495629632577152624380903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5663753088384768416253935 8495629632577152624380903)
          ·
            refine ⟨12743444448865728936571355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8495629632577152624380903 12743444448865728936571355)
            ·
              refine ⟨19115166673298593404857033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12743444448865728936571355 19115166673298593404857033)
              ·
                refine ⟨14336375004973945053642775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19115166673298593404857033 14336375004973945053642775)
                ·
                  refine ⟨21504562507460917580464163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14336375004973945053642775 21504562507460917580464163)
                  ·
                    refine ⟨32256843761191376370696245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21504562507460917580464163 32256843761191376370696245)
                    ·
                      refine ⟨3024079102611691534752773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32256843761191376370696245 3024079102611691534752773)
                      ·
                        rfl

theorem cell23_5889373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5889373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889373 prefixEnd_5889373 := by exact prefixLift 5889373
  have htrace : WordTrace (prefixWord ++ tailWord_5889373) baseStart_5889373 baseEnd_5889373 := by
    simpa [prefixWord, tailWord_5889373, baseEnd_5889373] using wordTrace_append hprefix tailTrace_5889373
  have hstable : (prefixWord ++ tailWord_5889373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889373).length < 2 ^ (prefixWord ++ tailWord_5889373).sum := by decide
  have hdescent : baseEnd_5889373 < baseStart_5889373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889385 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 1, 8]
def baseStart_5889385 : Nat := 118140960795 + 5889385 * 2 ^ 59
def prefixEnd_5889385 : Nat := 4983230072969 + 3 ^ 40 * 5889385 * 2
def baseEnd_5889385 : Nat := 1008028421459848495934239

theorem tailTrace_5889385 : CollatzResearch.WordTrace tailWord_5889385 prefixEnd_5889385 1008028421459848495934239 := by
  unfold tailWord_5889385
  simp only [CollatzResearch.WordTrace]
  refine ⟨214803517768771446725141609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143202345179180964483427739 214803517768771446725141609)
  ·
    refine ⟨161102638326578585043856207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214803517768771446725141609 161102638326578585043856207)
    ·
      refine ⟨241653957489867877565784311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161102638326578585043856207 241653957489867877565784311)
      ·
        refine ⟨362480936234801816348676467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241653957489867877565784311 362480936234801816348676467)
        ·
          refine ⟨543721404352202724523014701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362480936234801816348676467 543721404352202724523014701)
          ·
            refine ⟨203895526632076021696130513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 543721404352202724523014701 203895526632076021696130513)
            ·
              refine ⟨152921644974057016272097885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203895526632076021696130513 152921644974057016272097885)
              ·
                refine ⟨57345616865271381102036707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152921644974057016272097885 57345616865271381102036707)
                ·
                  refine ⟨86018425297907071653055061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57345616865271381102036707 86018425297907071653055061)
                  ·
                    refine ⟨1008028421459848495934239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86018425297907071653055061 1008028421459848495934239)
                    ·
                      rfl

theorem cell23_5889385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_5889385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889385 prefixEnd_5889385 := by exact prefixLift 5889385
  have htrace : WordTrace (prefixWord ++ tailWord_5889385) baseStart_5889385 baseEnd_5889385 := by
    simpa [prefixWord, tailWord_5889385, baseEnd_5889385] using wordTrace_append hprefix tailTrace_5889385
  have hstable : (prefixWord ++ tailWord_5889385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889385).length < 2 ^ (prefixWord ++ tailWord_5889385).sum := by decide
  have hdescent : baseEnd_5889385 < baseStart_5889385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889412 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_5889412 : Nat := 118140960795 + 5889412 * 2 ^ 59
def prefixEnd_5889412 : Nat := 4983230072969 + 3 ^ 40 * 5889412 * 2
def baseEnd_5889412 : Nat := 3024099128357216882165093

theorem tailTrace_5889412 : CollatzResearch.WordTrace tailWord_5889412 prefixEnd_5889412 3024099128357216882165093 := by
  unfold tailWord_5889412
  simp only [CollatzResearch.WordTrace]
  refine ⟨107402251269836815168187245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143203001693115753557582993 107402251269836815168187245)
  ·
    refine ⟨40275844226188805688070217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107402251269836815168187245 40275844226188805688070217)
    ·
      refine ⟨30206883169641604266052663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40275844226188805688070217 30206883169641604266052663)
      ·
        refine ⟨45310324754462406399078995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30206883169641604266052663 45310324754462406399078995)
        ·
          refine ⟨67965487131693609598618493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45310324754462406399078995 67965487131693609598618493)
          ·
            refine ⟨25487057674385103599481935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67965487131693609598618493 25487057674385103599481935)
            ·
              refine ⟨38230586511577655399222903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25487057674385103599481935 38230586511577655399222903)
              ·
                refine ⟨57345879767366483098834355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38230586511577655399222903 57345879767366483098834355)
                ·
                  refine ⟨86018819651049724648251533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57345879767366483098834355 86018819651049724648251533)
                  ·
                    refine ⟨32257057369143646743094325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86018819651049724648251533 32257057369143646743094325)
                    ·
                      refine ⟨3024099128357216882165093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32257057369143646743094325 3024099128357216882165093)
                      ·
                        rfl

theorem cell23_5889412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_5889412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889412 prefixEnd_5889412 := by exact prefixLift 5889412
  have htrace : WordTrace (prefixWord ++ tailWord_5889412) baseStart_5889412 baseEnd_5889412 := by
    simpa [prefixWord, tailWord_5889412, baseEnd_5889412] using wordTrace_append hprefix tailTrace_5889412
  have hstable : (prefixWord ++ tailWord_5889412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889412).length < 2 ^ (prefixWord ++ tailWord_5889412).sum := by decide
  have hdescent : baseEnd_5889412 < baseStart_5889412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889472 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 5]
def baseStart_5889472 : Nat := 118140960795 + 5889472 * 2 ^ 59
def prefixEnd_5889472 : Nat := 4983230072969 + 3 ^ 40 * 5889472 * 2
def baseEnd_5889472 : Nat := 3024129937196486647414817

theorem tailTrace_5889472 : CollatzResearch.WordTrace tailWord_5889472 prefixEnd_5889472 3024129937196486647414817 := by
  unfold tailWord_5889472
  simp only [CollatzResearch.WordTrace]
  refine ⟨107403345459728130291779335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143204460612970840389039113 107403345459728130291779335)
  ·
    refine ⟨161105018189592195437669003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107403345459728130291779335 161105018189592195437669003)
    ·
      refine ⟨241657527284388293156503505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161105018189592195437669003 241657527284388293156503505)
      ·
        refine ⟨181243145463291219867377629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241657527284388293156503505 181243145463291219867377629)
        ·
          refine ⟨67966179548734207450266611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181243145463291219867377629 67966179548734207450266611)
          ·
            refine ⟨101949269323101311175399917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67966179548734207450266611 101949269323101311175399917)
            ·
              refine ⟨38230975996162991690774969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101949269323101311175399917 38230975996162991690774969)
              ·
                refine ⟨28673231997122243768081227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38230975996162991690774969 28673231997122243768081227)
                ·
                  refine ⟨43009847995683365652121841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28673231997122243768081227 43009847995683365652121841)
                  ·
                    refine ⟨32257385996762524239091381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43009847995683365652121841 32257385996762524239091381)
                    ·
                      refine ⟨3024129937196486647414817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32257385996762524239091381 3024129937196486647414817)
                      ·
                        rfl

theorem cell23_5889472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_5889472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889472 prefixEnd_5889472 := by exact prefixLift 5889472
  have htrace : WordTrace (prefixWord ++ tailWord_5889472) baseStart_5889472 baseEnd_5889472 := by
    simpa [prefixWord, tailWord_5889472, baseEnd_5889472] using wordTrace_append hprefix tailTrace_5889472
  have hstable : (prefixWord ++ tailWord_5889472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889472).length < 2 ^ (prefixWord ++ tailWord_5889472).sum := by decide
  have hdescent : baseEnd_5889472 < baseStart_5889472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889543 : List Nat := [1, 1, 4, 3, 2, 1, 2, 4, 1, 4]
def baseStart_5889543 : Nat := 118140960795 + 5889543 * 2 ^ 59
def prefixEnd_5889543 : Nat := 4983230072969 + 3 ^ 40 * 5889543 * 2
def baseEnd_5889543 : Nat := 1008055464774318623208997

theorem tailTrace_5889543 : CollatzResearch.WordTrace tailWord_5889543 prefixEnd_5889543 1008055464774318623208997 := by
  unfold tailWord_5889543
  simp only [CollatzResearch.WordTrace]
  refine ⟨214809280502199039709393283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143206187001466026472928855 214809280502199039709393283)
  ·
    refine ⟨322213920753298559564089925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214809280502199039709393283 322213920753298559564089925)
    ·
      refine ⟨60415110141243479918266861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 322213920753298559564089925 60415110141243479918266861)
      ·
        refine ⟨22655666302966304969350073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60415110141243479918266861 22655666302966304969350073)
        ·
          refine ⟨16991749727224728727012555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22655666302966304969350073 16991749727224728727012555)
          ·
            refine ⟨25487624590837093090518833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16991749727224728727012555 25487624590837093090518833)
            ·
              refine ⟨19115718443127819817889125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25487624590837093090518833 19115718443127819817889125)
              ·
                refine ⟨3584197208086466215854211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19115718443127819817889125 3584197208086466215854211)
                ·
                  refine ⟨5376295812129699323781317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3584197208086466215854211 5376295812129699323781317)
                  ·
                    refine ⟨1008055464774318623208997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5376295812129699323781317 1008055464774318623208997)
                    ·
                      rfl

theorem cell23_5889543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_5889543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889543 prefixEnd_5889543 := by exact prefixLift 5889543
  have htrace : WordTrace (prefixWord ++ tailWord_5889543) baseStart_5889543 baseEnd_5889543 := by
    simpa [prefixWord, tailWord_5889543, baseEnd_5889543] using wordTrace_append hprefix tailTrace_5889543
  have hstable : (prefixWord ++ tailWord_5889543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889543).length < 2 ^ (prefixWord ++ tailWord_5889543).sum := by decide
  have hdescent : baseEnd_5889543 < baseStart_5889543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889593 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 2, 3, 2]
def baseStart_5889593 : Nat := 118140960795 + 5889593 * 2 ^ 59
def prefixEnd_5889593 : Nat := 4983230072969 + 3 ^ 40 * 5889593 * 2
def baseEnd_5889593 : Nat := 3024192068355680674001761

theorem tailTrace_5889593 : CollatzResearch.WordTrace tailWord_5889593 prefixEnd_5889593 3024192068355680674001761 := by
  unfold tailWord_5889593
  simp only [CollatzResearch.WordTrace]
  refine ⟨214811104152017898248713433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143207402768011932165808955 214811104152017898248713433)
  ·
    refine ⟨161108328114013423686535075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214811104152017898248713433 161108328114013423686535075)
    ·
      refine ⟨241662492171020135529802613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161108328114013423686535075 241662492171020135529802613)
      ·
        refine ⟨22655858641033137705918995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241662492171020135529802613 22655858641033137705918995)
        ·
          refine ⟨33983787961549706558878493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22655858641033137705918995 33983787961549706558878493)
          ·
            refine ⟨12743920485581139959579435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33983787961549706558878493 12743920485581139959579435)
            ·
              refine ⟨19115880728371709939369153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12743920485581139959579435 19115880728371709939369153)
              ·
                refine ⟨14336910546278782454526865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19115880728371709939369153 14336910546278782454526865)
                ·
                  refine ⟨10752682909709086840895149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14336910546278782454526865 10752682909709086840895149)
                  ·
                    refine ⟨4032256091140907565335681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10752682909709086840895149 4032256091140907565335681)
                    ·
                      refine ⟨3024192068355680674001761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4032256091140907565335681 3024192068355680674001761)
                      ·
                        rfl

theorem cell23_5889593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_5889593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889593 prefixEnd_5889593 := by exact prefixLift 5889593
  have htrace : WordTrace (prefixWord ++ tailWord_5889593) baseStart_5889593 baseEnd_5889593 := by
    simpa [prefixWord, tailWord_5889593, baseEnd_5889593] using wordTrace_append hprefix tailTrace_5889593
  have hstable : (prefixWord ++ tailWord_5889593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889593).length < 2 ^ (prefixWord ++ tailWord_5889593).sum := by decide
  have hdescent : baseEnd_5889593 < baseStart_5889593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889616 : List Nat := [2, 1, 1, 1, 1, 3, 5, 3, 2, 4]
def baseStart_5889616 : Nat := 118140960795 + 5889616 * 2 ^ 59
def prefixEnd_5889616 : Nat := 4983230072969 + 3 ^ 40 * 5889616 * 2
def baseEnd_5889616 : Nat := 1008067959470244694671385

theorem tailTrace_5889616 : CollatzResearch.WordTrace tailWord_5889616 prefixEnd_5889616 1008067959470244694671385 := by
  unfold tailWord_5889616
  simp only [CollatzResearch.WordTrace]
  refine ⟨107405971515467286588400351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143207962020623048784533801 107405971515467286588400351)
  ·
    refine ⟨161108957273200929882600527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107405971515467286588400351 161108957273200929882600527)
    ·
      refine ⟨241663435909801394823900791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161108957273200929882600527 241663435909801394823900791)
      ·
        refine ⟨362495153864702092235851187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241663435909801394823900791 362495153864702092235851187)
        ·
          refine ⟨543742730797053138353776781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362495153864702092235851187 543742730797053138353776781)
          ·
            refine ⟨203903524048894926882666293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 543742730797053138353776781 203903524048894926882666293)
            ·
              refine ⟨19115955379583899395249965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203903524048894926882666293 19115955379583899395249965)
              ·
                refine ⟨7168483267343962273218737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19115955379583899395249965 7168483267343962273218737)
                ·
                  refine ⟨5376362450507971704914053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7168483267343962273218737 5376362450507971704914053)
                  ·
                    refine ⟨1008067959470244694671385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5376362450507971704914053 1008067959470244694671385)
                    ·
                      rfl

theorem cell23_5889616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 2, 4].length) (baseStart_5889616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889616 prefixEnd_5889616 := by exact prefixLift 5889616
  have htrace : WordTrace (prefixWord ++ tailWord_5889616) baseStart_5889616 baseEnd_5889616 := by
    simpa [prefixWord, tailWord_5889616, baseEnd_5889616] using wordTrace_append hprefix tailTrace_5889616
  have hstable : (prefixWord ++ tailWord_5889616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889616).length < 2 ^ (prefixWord ++ tailWord_5889616).sum := by decide
  have hdescent : baseEnd_5889616 < baseStart_5889616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889623 : List Nat := [1, 1, 3, 2, 2, 5, 1, 2, 1, 1, 4]
def baseStart_5889623 : Nat := 118140960795 + 5889623 * 2 ^ 59
def prefixEnd_5889623 : Nat := 4983230072969 + 3 ^ 40 * 5889623 * 2
def baseEnd_5889623 : Nat := 3024207472775315556626623

theorem tailTrace_5889623 : CollatzResearch.WordTrace tailWord_5889623 prefixEnd_5889623 3024207472775315556626623 := by
  unfold tailWord_5889623
  simp only [CollatzResearch.WordTrace]
  refine ⟨214812198341909213372305523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143208132227939475581537015 214812198341909213372305523)
  ·
    refine ⟨322218297512863820058458285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214812198341909213372305523 322218297512863820058458285)
    ·
      refine ⟨120831861567323932521921857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322218297512863820058458285 120831861567323932521921857)
      ·
        refine ⟨90623896175492949391441393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120831861567323932521921857 90623896175492949391441393)
        ·
          refine ⟨67967922131619712043581045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90623896175492949391441393 67967922131619712043581045)
          ·
            refine ⟨6371992699839348004085723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67967922131619712043581045 6371992699839348004085723)
            ·
              refine ⟨9557989049759022006128585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6371992699839348004085723 9557989049759022006128585)
              ·
                refine ⟨7168491787319266504596439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9557989049759022006128585 7168491787319266504596439)
                ·
                  refine ⟨10752737680978899756894659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7168491787319266504596439 10752737680978899756894659)
                  ·
                    refine ⟨16129106521468349635341989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10752737680978899756894659 16129106521468349635341989)
                    ·
                      refine ⟨3024207472775315556626623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16129106521468349635341989 3024207472775315556626623)
                      ·
                        rfl

theorem cell23_5889623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_5889623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889623 prefixEnd_5889623 := by exact prefixLift 5889623
  have htrace : WordTrace (prefixWord ++ tailWord_5889623) baseStart_5889623 baseEnd_5889623 := by
    simpa [prefixWord, tailWord_5889623, baseEnd_5889623] using wordTrace_append hprefix tailTrace_5889623
  have hstable : (prefixWord ++ tailWord_5889623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889623).length < 2 ^ (prefixWord ++ tailWord_5889623).sum := by decide
  have hdescent : baseEnd_5889623 < baseStart_5889623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889636 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_5889636 : Nat := 118140960795 + 5889636 * 2 ^ 59
def prefixEnd_5889636 : Nat := 4983230072969 + 3 ^ 40 * 5889636 * 2
def baseEnd_5889636 : Nat := 3024214148023824005764063

theorem tailTrace_5889636 : CollatzResearch.WordTrace tailWord_5889636 prefixEnd_5889636 3024214148023824005764063 := by
  unfold tailWord_5889636
  simp only [CollatzResearch.WordTrace]
  refine ⟨107406336245431058296264381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143208448327241411061685841 107406336245431058296264381)
  ·
    refine ⟨40277376092036646861099143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107406336245431058296264381 40277376092036646861099143)
    ·
      refine ⟨60416064138054970291648715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40277376092036646861099143 60416064138054970291648715)
      ·
        refine ⟨90624096207082455437473073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60416064138054970291648715 90624096207082455437473073)
        ·
          refine ⟨67968072155311841578104805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90624096207082455437473073 67968072155311841578104805)
          ·
            refine ⟨12744013529120970295894651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67968072155311841578104805 12744013529120970295894651)
            ·
              refine ⟨19116020293681455443841977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12744013529120970295894651 19116020293681455443841977)
              ·
                refine ⟨14337015220261091582881483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19116020293681455443841977 14337015220261091582881483)
                ·
                  refine ⟨21505522830391637374322225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14337015220261091582881483 21505522830391637374322225)
                  ·
                    refine ⟨16129142122793728030741669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21505522830391637374322225 16129142122793728030741669)
                    ·
                      refine ⟨3024214148023824005764063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16129142122793728030741669 3024214148023824005764063)
                      ·
                        rfl

theorem cell23_5889636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_5889636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889636 prefixEnd_5889636 := by exact prefixLift 5889636
  have htrace : WordTrace (prefixWord ++ tailWord_5889636) baseStart_5889636 baseEnd_5889636 := by
    simpa [prefixWord, tailWord_5889636, baseEnd_5889636] using wordTrace_append hprefix tailTrace_5889636
  have hstable : (prefixWord ++ tailWord_5889636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889636).length < 2 ^ (prefixWord ++ tailWord_5889636).sum := by decide
  have hdescent : baseEnd_5889636 < baseStart_5889636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889640 : List Nat := [2, 1, 4, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_5889640 : Nat := 118140960795 + 5889640 * 2 ^ 59
def prefixEnd_5889640 : Nat := 4983230072969 + 3 ^ 40 * 5889640 * 2
def baseEnd_5889640 : Nat := 3024216201946441990114045

theorem tailTrace_5889640 : CollatzResearch.WordTrace tailWord_5889640 prefixEnd_5889640 3024216201946441990114045 := by
  unfold tailWord_5889640
  simp only [CollatzResearch.WordTrace]
  refine ⟨107406409191423812637837187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143208545588565083517116249 107406409191423812637837187)
  ·
    refine ⟨161109613787135718956755781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107406409191423812637837187 161109613787135718956755781)
    ·
      refine ⟨30208052585087947304391709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161109613787135718956755781 30208052585087947304391709)
      ·
        refine ⟨11328019719407980239146891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30208052585087947304391709 11328019719407980239146891)
        ·
          refine ⟨16992029579111970358720337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11328019719407980239146891 16992029579111970358720337)
          ·
            refine ⟨12744022184333977769040253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16992029579111970358720337 12744022184333977769040253)
            ·
              refine ⟨4779008319125241663390095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12744022184333977769040253 4779008319125241663390095)
              ·
                refine ⟨7168512478687862495085143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779008319125241663390095 7168512478687862495085143)
                ·
                  refine ⟨10752768718031793742627715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7168512478687862495085143 10752768718031793742627715)
                  ·
                    refine ⟨16129153077047690613941573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10752768718031793742627715 16129153077047690613941573)
                    ·
                      refine ⟨3024216201946441990114045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16129153077047690613941573 3024216201946441990114045)
                      ·
                        rfl

theorem cell23_5889640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_5889640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889640 prefixEnd_5889640 := by exact prefixLift 5889640
  have htrace : WordTrace (prefixWord ++ tailWord_5889640) baseStart_5889640 baseEnd_5889640 := by
    simpa [prefixWord, tailWord_5889640, baseEnd_5889640] using wordTrace_append hprefix tailTrace_5889640
  have hstable : (prefixWord ++ tailWord_5889640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889640).length < 2 ^ (prefixWord ++ tailWord_5889640).sum := by decide
  have hdescent : baseEnd_5889640 < baseStart_5889640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889646 : List Nat := [4, 1, 2, 2, 4, 10]
def baseStart_5889646 : Nat := 118140960795 + 5889646 * 2 ^ 59
def prefixEnd_5889646 : Nat := 4983230072969 + 3 ^ 40 * 5889646 * 2
def baseEnd_5889646 : Nat := 12445346842923329080819

theorem tailTrace_5889646 : CollatzResearch.WordTrace tailWord_5889646 prefixEnd_5889646 12445346842923329080819 := by
  unfold tailWord_5889646
  simp only [CollatzResearch.WordTrace]
  refine ⟨26851629652603236037549099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143208691480550592200261861 26851629652603236037549099)
  ·
    refine ⟨40277444478904854056323649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26851629652603236037549099 40277444478904854056323649)
    ·
      refine ⟨30208083359178640542242737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40277444478904854056323649 30208083359178640542242737)
      ·
        refine ⟨22656062519383980406682053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30208083359178640542242737 22656062519383980406682053)
        ·
          refine ⟨4248011722384496326252885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22656062519383980406682053 4248011722384496326252885)
          ·
            refine ⟨12445346842923329080819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4248011722384496326252885 12445346842923329080819)
            ·
              rfl

theorem cell23_5889646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 10].length) (baseStart_5889646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889646 prefixEnd_5889646 := by exact prefixLift 5889646
  have htrace : WordTrace (prefixWord ++ tailWord_5889646) baseStart_5889646 baseEnd_5889646 := by
    simpa [prefixWord, tailWord_5889646, baseEnd_5889646] using wordTrace_append hprefix tailTrace_5889646
  have hstable : (prefixWord ++ tailWord_5889646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889646).length < 2 ^ (prefixWord ++ tailWord_5889646).sum := by decide
  have hdescent : baseEnd_5889646 < baseStart_5889646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889673 : List Nat := [1, 2, 1, 1, 4, 1, 4, 3, 2, 1, 3]
def baseStart_5889673 : Nat := 118140960795 + 5889673 * 2 ^ 59
def prefixEnd_5889673 : Nat := 4983230072969 + 3 ^ 40 * 5889673 * 2
def baseEnd_5889673 : Nat := 3024233146808040361001393

theorem tailTrace_5889673 : CollatzResearch.WordTrace tailWord_5889673 prefixEnd_5889673 3024233146808040361001393 := by
  unfold tailWord_5889673
  simp only [CollatzResearch.WordTrace]
  refine ⟨214814021991728071911625673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143209347994485381274417115 214814021991728071911625673)
  ·
    refine ⟨161110516493796053933719255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214814021991728071911625673 161110516493796053933719255)
    ·
      refine ⟨241665774740694080900578883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161110516493796053933719255 241665774740694080900578883)
      ·
        refine ⟨362498662111041121350868325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241665774740694080900578883 362498662111041121350868325)
        ·
          refine ⟨67968499145820210253287811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362498662111041121350868325 67968499145820210253287811)
          ·
            refine ⟨101952748718730315379931717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67968499145820210253287811 101952748718730315379931717)
            ·
              refine ⟨19116140384761934133737197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101952748718730315379931717 19116140384761934133737197)
              ·
                refine ⟨7168552644285725300151449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19116140384761934133737197 7168552644285725300151449)
                ·
                  refine ⟨5376414483214293975113587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7168552644285725300151449 5376414483214293975113587)
                  ·
                    refine ⟨8064621724821440962670381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5376414483214293975113587 8064621724821440962670381)
                    ·
                      refine ⟨3024233146808040361001393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8064621724821440962670381 3024233146808040361001393)
                      ·
                        rfl

theorem cell23_5889673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 1, 3].length) (baseStart_5889673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889673 prefixEnd_5889673 := by exact prefixLift 5889673
  have htrace : WordTrace (prefixWord ++ tailWord_5889673) baseStart_5889673 baseEnd_5889673 := by
    simpa [prefixWord, tailWord_5889673, baseEnd_5889673] using wordTrace_append hprefix tailTrace_5889673
  have hstable : (prefixWord ++ tailWord_5889673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889673).length < 2 ^ (prefixWord ++ tailWord_5889673).sum := by decide
  have hdescent : baseEnd_5889673 < baseStart_5889673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889699 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 5]
def baseStart_5889699 : Nat := 118140960795 + 5889699 * 2 ^ 59
def prefixEnd_5889699 : Nat := 4983230072969 + 3 ^ 40 * 5889699 * 2
def baseEnd_5889699 : Nat := 3024246497305057259276273

theorem tailTrace_5889699 : CollatzResearch.WordTrace tailWord_5889699 prefixEnd_5889699 3024246497305057259276273 := by
  unfold tailWord_5889699
  simp only [CollatzResearch.WordTrace]
  refine ⟨214814970289633878352072151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143209980193089252234714767 214814970289633878352072151)
  ·
    refine ⟨322222455434450817528108227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214814970289633878352072151 322222455434450817528108227)
    ·
      refine ⟨483333683151676226292162341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322222455434450817528108227 483333683151676226292162341)
      ·
        refine ⟨90625065590939292429780439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 483333683151676226292162341 90625065590939292429780439)
        ·
          refine ⟨135937598386408938644670659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90625065590939292429780439 135937598386408938644670659)
          ·
            refine ⟨203906397579613407967005989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135937598386408938644670659 203906397579613407967005989)
            ·
              refine ⟨38232449546177513993813623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203906397579613407967005989 38232449546177513993813623)
              ·
                refine ⟨57348674319266270990720435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38232449546177513993813623 57348674319266270990720435)
                ·
                  refine ⟨86023011478899406486080653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57348674319266270990720435 86023011478899406486080653)
                  ·
                    refine ⟨32258629304587277432280245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86023011478899406486080653 32258629304587277432280245)
                    ·
                      refine ⟨3024246497305057259276273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32258629304587277432280245 3024246497305057259276273)
                      ·
                        rfl

theorem cell23_5889699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_5889699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889699 prefixEnd_5889699 := by exact prefixLift 5889699
  have htrace : WordTrace (prefixWord ++ tailWord_5889699) baseStart_5889699 baseEnd_5889699 := by
    simpa [prefixWord, tailWord_5889699, baseEnd_5889699] using wordTrace_append hprefix tailTrace_5889699
  have hstable : (prefixWord ++ tailWord_5889699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889699).length < 2 ^ (prefixWord ++ tailWord_5889699).sum := by decide
  have hdescent : baseEnd_5889699 < baseStart_5889699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889700 : List Nat := [2, 3, 1, 2, 2, 3, 1, 3, 1, 3, 2]
def baseStart_5889700 : Nat := 118140960795 + 5889700 * 2 ^ 59
def prefixEnd_5889700 : Nat := 4983230072969 + 3 ^ 40 * 5889700 * 2
def baseEnd_5889700 : Nat := 3024247010785711755363769

theorem tailTrace_5889700 : CollatzResearch.WordTrace tailWord_5889700 prefixEnd_5889700 3024247010785711755363769 := by
  unfold tailWord_5889700
  simp only [CollatzResearch.WordTrace]
  refine ⟨107407503381315127761429277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143210004508420170348572369 107407503381315127761429277)
  ·
    refine ⟨40277813767993172910535979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107407503381315127761429277 40277813767993172910535979)
    ·
      refine ⟨60416720651989759365803969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40277813767993172910535979 60416720651989759365803969)
      ·
        refine ⟨45312540488992319524352977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60416720651989759365803969 45312540488992319524352977)
        ·
          refine ⟨33984405366744239643264733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45312540488992319524352977 33984405366744239643264733)
          ·
            refine ⟨12744152012529089866224275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33984405366744239643264733 12744152012529089866224275)
            ·
              refine ⟨19116228018793634799336413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12744152012529089866224275 19116228018793634799336413)
              ·
                refine ⟨7168585507047613049751155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19116228018793634799336413 7168585507047613049751155)
                ·
                  refine ⟨10752878260571419574626733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7168585507047613049751155 10752878260571419574626733)
                  ·
                    refine ⟨4032329347714282340485025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10752878260571419574626733 4032329347714282340485025)
                    ·
                      refine ⟨3024247010785711755363769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4032329347714282340485025 3024247010785711755363769)
                      ·
                        rfl

theorem cell23_5889700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_5889700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889700 prefixEnd_5889700 := by exact prefixLift 5889700
  have htrace : WordTrace (prefixWord ++ tailWord_5889700) baseStart_5889700 baseEnd_5889700 := by
    simpa [prefixWord, tailWord_5889700, baseEnd_5889700] using wordTrace_append hprefix tailTrace_5889700
  have hstable : (prefixWord ++ tailWord_5889700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889700).length < 2 ^ (prefixWord ++ tailWord_5889700).sum := by decide
  have hdescent : baseEnd_5889700 < baseStart_5889700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889734 : List Nat := [6, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_5889734 : Nat := 118140960795 + 5889734 * 2 ^ 59
def prefixEnd_5889734 : Nat := 4983230072969 + 3 ^ 40 * 5889734 * 2
def baseEnd_5889734 : Nat := 3024264469127964622338613

theorem tailTrace_5889734 : CollatzResearch.WordTrace tailWord_5889734 prefixEnd_5889734 3024264469127964622338613 := by
  unfold tailWord_5889734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6713007713890846229049883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143210831229671386219730837 6713007713890846229049883)
  ·
    refine ⟨10069511570836269343574825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6713007713890846229049883 10069511570836269343574825)
    ·
      refine ⟨7552133678127202007681119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10069511570836269343574825 7552133678127202007681119)
      ·
        refine ⟨11328200517190803011521679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7552133678127202007681119 11328200517190803011521679)
        ·
          refine ⟨16992300775786204517282519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11328200517190803011521679 16992300775786204517282519)
          ·
            refine ⟨25488451163679306775923779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16992300775786204517282519 25488451163679306775923779)
            ·
              refine ⟨38232676745518960163885669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25488451163679306775923779 38232676745518960163885669)
              ·
                refine ⟨7168626889784805030728563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38232676745518960163885669 7168626889784805030728563)
                ·
                  refine ⟨10752940334677207546092845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7168626889784805030728563 10752940334677207546092845)
                  ·
                    refine ⟨4032352625503952829784817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10752940334677207546092845 4032352625503952829784817)
                    ·
                      refine ⟨3024264469127964622338613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4032352625503952829784817 3024264469127964622338613)
                      ·
                        rfl

theorem cell23_5889734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_5889734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889734 prefixEnd_5889734 := by exact prefixLift 5889734
  have htrace : WordTrace (prefixWord ++ tailWord_5889734) baseStart_5889734 baseEnd_5889734 := by
    simpa [prefixWord, tailWord_5889734, baseEnd_5889734] using wordTrace_append hprefix tailTrace_5889734
  have hstable : (prefixWord ++ tailWord_5889734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889734).length < 2 ^ (prefixWord ++ tailWord_5889734).sum := by decide
  have hdescent : baseEnd_5889734 < baseStart_5889734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889753 : List Nat := [1, 2, 1, 2, 3, 3, 3, 3, 5]
def baseStart_5889753 : Nat := 118140960795 + 5889753 * 2 ^ 59
def prefixEnd_5889753 : Nat := 4983230072969 + 3 ^ 40 * 5889753 * 2
def baseEnd_5889753 : Nat := 336030469473377783111225

theorem tailTrace_5889753 : CollatzResearch.WordTrace tailWord_5889753 prefixEnd_5889753 336030469473377783111225 := by
  unfold tailWord_5889753
  simp only [CollatzResearch.WordTrace]
  refine ⟨214816939831438245574537913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143211293220958830383025275 214816939831438245574537913)
  ·
    refine ⟨161112704873578684180903435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214816939831438245574537913 161112704873578684180903435)
    ·
      refine ⟨241669057310368026271355153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161112704873578684180903435 241669057310368026271355153)
      ·
        refine ⟨181251792982776019703516365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241669057310368026271355153 181251792982776019703516365)
        ·
          refine ⟨67969422368541007388818637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181251792982776019703516365 67969422368541007388818637)
          ·
            refine ⟨25488533388202877770806989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67969422368541007388818637 25488533388202877770806989)
            ·
              refine ⟨9558200020576079164052621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25488533388202877770806989 9558200020576079164052621)
              ·
                refine ⟨3584325007716029686519733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9558200020576079164052621 3584325007716029686519733)
                ·
                  refine ⟨336030469473377783111225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3584325007716029686519733 336030469473377783111225)
                  ·
                    rfl

theorem cell23_5889753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 5].length) (baseStart_5889753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889753 prefixEnd_5889753 := by exact prefixLift 5889753
  have htrace : WordTrace (prefixWord ++ tailWord_5889753) baseStart_5889753 baseEnd_5889753 := by
    simpa [prefixWord, tailWord_5889753, baseEnd_5889753] using wordTrace_append hprefix tailTrace_5889753
  have hstable : (prefixWord ++ tailWord_5889753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889753).length < 2 ^ (prefixWord ++ tailWord_5889753).sum := by decide
  have hdescent : baseEnd_5889753 < baseStart_5889753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889786 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_5889786 : Nat := 118140960795 + 5889786 * 2 ^ 59
def prefixEnd_5889786 : Nat := 4983230072969 + 3 ^ 40 * 5889786 * 2
def baseEnd_5889786 : Nat := 3024291170121998418888373

theorem tailTrace_5889786 : CollatzResearch.WordTrace tailWord_5889786 prefixEnd_5889786 3024291170121998418888373 := by
  unfold tailWord_5889786
  simp only [CollatzResearch.WordTrace]
  refine ⟨53704535860079673052622303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143212095626879128140326141 53704535860079673052622303)
  ·
    refine ⟨80556803790119509578933455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53704535860079673052622303 80556803790119509578933455)
    ·
      refine ⟨120835205685179264368400183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80556803790119509578933455 120835205685179264368400183)
      ·
        refine ⟨181252808527768896552600275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120835205685179264368400183 181252808527768896552600275)
        ·
          refine ⟨271879212791653344828900413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181252808527768896552600275 271879212791653344828900413)
          ·
            refine ⟨101954704796870004310837655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271879212791653344828900413 101954704796870004310837655)
            ·
              refine ⟨152932057195305006466256483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101954704796870004310837655 152932057195305006466256483)
              ·
                refine ⟨229398085792957509699384725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152932057195305006466256483 229398085792957509699384725)
                ·
                  refine ⟨10753035271544883267158659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 229398085792957509699384725 10753035271544883267158659)
                  ·
                    refine ⟨16129552907317324900737989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10753035271544883267158659 16129552907317324900737989)
                    ·
                      refine ⟨3024291170121998418888373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16129552907317324900737989 3024291170121998418888373)
                      ·
                        rfl

theorem cell23_5889786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_5889786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889786 prefixEnd_5889786 := by exact prefixLift 5889786
  have htrace : WordTrace (prefixWord ++ tailWord_5889786) baseStart_5889786 baseEnd_5889786 := by
    simpa [prefixWord, tailWord_5889786, baseEnd_5889786] using wordTrace_append hprefix tailTrace_5889786
  have hstable : (prefixWord ++ tailWord_5889786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889786).length < 2 ^ (prefixWord ++ tailWord_5889786).sum := by decide
  have hdescent : baseEnd_5889786 < baseStart_5889786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889798 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5889798 : Nat := 118140960795 + 5889798 * 2 ^ 59
def prefixEnd_5889798 : Nat := 4983230072969 + 3 ^ 40 * 5889798 * 2
def baseEnd_5889798 : Nat := 3024297331889852371938319

theorem tailTrace_5889798 : CollatzResearch.WordTrace tailWord_5889798 prefixEnd_5889798 3024297331889852371938319 := by
  unfold tailWord_5889798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6713080659883600570622689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143212387410850145506617365 6713080659883600570622689)
  ·
    refine ⟨5034810494912700427967017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6713080659883600570622689 5034810494912700427967017)
    ·
      refine ⟨3776107871184525320975263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5034810494912700427967017 3776107871184525320975263)
      ·
        refine ⟨5664161806776787981462895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3776107871184525320975263 5664161806776787981462895)
        ·
          refine ⟨8496242710165181972194343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5664161806776787981462895 8496242710165181972194343)
          ·
            refine ⟨12744364065247772958291515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8496242710165181972194343 12744364065247772958291515)
            ·
              refine ⟨19116546097871659437437273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12744364065247772958291515 19116546097871659437437273)
              ·
                refine ⟨14337409573403744578077955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19116546097871659437437273 14337409573403744578077955)
                ·
                  refine ⟨21506114360105616867116933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14337409573403744578077955 21506114360105616867116933)
                  ·
                    refine ⟨4032396442519803162584425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21506114360105616867116933 4032396442519803162584425)
                    ·
                      refine ⟨3024297331889852371938319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4032396442519803162584425 3024297331889852371938319)
                      ·
                        rfl

theorem cell23_5889798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5889798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889798 prefixEnd_5889798 := by exact prefixLift 5889798
  have htrace : WordTrace (prefixWord ++ tailWord_5889798) baseStart_5889798 baseEnd_5889798 := by
    simpa [prefixWord, tailWord_5889798, baseEnd_5889798] using wordTrace_append hprefix tailTrace_5889798
  have hstable : (prefixWord ++ tailWord_5889798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889798).length < 2 ^ (prefixWord ++ tailWord_5889798).sum := by decide
  have hdescent : baseEnd_5889798 < baseStart_5889798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889823 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 3]
def baseStart_5889823 : Nat := 118140960795 + 5889823 * 2 ^ 59
def prefixEnd_5889823 : Nat := 4983230072969 + 3 ^ 40 * 5889823 * 2
def baseEnd_5889823 : Nat := 3024310168906214774125703

theorem tailTrace_5889823 : CollatzResearch.WordTrace tailWord_5889823 prefixEnd_5889823 3024310168906214774125703 := by
  unfold tailWord_5889823
  simp only [CollatzResearch.WordTrace]
  refine ⟨214819492941184647529586123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143212995294123098353057415 214819492941184647529586123)
  ·
    refine ⟨322229239411776971294379185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214819492941184647529586123 322229239411776971294379185)
    ·
      refine ⟨241671929558832728470784389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322229239411776971294379185 241671929558832728470784389)
      ·
        refine ⟨45313486792281136588272073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241671929558832728470784389 45313486792281136588272073)
        ·
          refine ⟨33985115094210852441204055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45313486792281136588272073 33985115094210852441204055)
          ·
            refine ⟨50977672641316278661806083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33985115094210852441204055 50977672641316278661806083)
            ·
              refine ⟨76466508961974417992709125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50977672641316278661806083 76466508961974417992709125)
              ·
                refine ⟨14337470430370203373632961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76466508961974417992709125 14337470430370203373632961)
                ·
                  refine ⟨10753102822777652530224721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14337470430370203373632961 10753102822777652530224721)
                  ·
                    refine ⟨8064827117083239397668541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10753102822777652530224721 8064827117083239397668541)
                    ·
                      refine ⟨3024310168906214774125703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8064827117083239397668541 3024310168906214774125703)
                      ·
                        rfl

theorem cell23_5889823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_5889823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889823 prefixEnd_5889823 := by exact prefixLift 5889823
  have htrace : WordTrace (prefixWord ++ tailWord_5889823) baseStart_5889823 baseEnd_5889823 := by
    simpa [prefixWord, tailWord_5889823, baseEnd_5889823] using wordTrace_append hprefix tailTrace_5889823
  have hstable : (prefixWord ++ tailWord_5889823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889823).length < 2 ^ (prefixWord ++ tailWord_5889823).sum := by decide
  have hdescent : baseEnd_5889823 < baseStart_5889823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889887 : List Nat := [1, 1, 2, 3, 1, 4, 2, 4, 1, 1, 3]
def baseStart_5889887 : Nat := 118140960795 + 5889887 * 2 ^ 59
def prefixEnd_5889887 : Nat := 4983230072969 + 3 ^ 40 * 5889887 * 2
def baseEnd_5889887 : Nat := 3024343031668102523725409

theorem tailTrace_5889887 : CollatzResearch.WordTrace tailWord_5889887 prefixEnd_5889887 3024343031668102523725409 := by
  unfold tailWord_5889887
  simp only [CollatzResearch.WordTrace]
  refine ⟨214821827212952786459915915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143214551475301857639943943 214821827212952786459915915)
  ·
    refine ⟨322232740819429179689873873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214821827212952786459915915 322232740819429179689873873)
    ·
      refine ⟨241674555614571884767405405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322232740819429179689873873 241674555614571884767405405)
      ·
        refine ⟨90627958355464456787777027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241674555614571884767405405 90627958355464456787777027)
        ·
          refine ⟨135941937533196685181665541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90627958355464456787777027 135941937533196685181665541)
          ·
            refine ⟨25489113287474378471562289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135941937533196685181665541 25489113287474378471562289)
            ·
              refine ⟨19116834965605783853671717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25489113287474378471562289 19116834965605783853671717)
              ·
                refine ⟨3584406556051084472563447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19116834965605783853671717 3584406556051084472563447)
                ·
                  refine ⟨5376609834076626708845171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3584406556051084472563447 5376609834076626708845171)
                  ·
                    refine ⟨8064914751114940063267757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5376609834076626708845171 8064914751114940063267757)
                    ·
                      refine ⟨3024343031668102523725409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8064914751114940063267757 3024343031668102523725409)
                      ·
                        rfl

theorem cell23_5889887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_5889887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889887 prefixEnd_5889887 := by exact prefixLift 5889887
  have htrace : WordTrace (prefixWord ++ tailWord_5889887) baseStart_5889887 baseEnd_5889887 := by
    simpa [prefixWord, tailWord_5889887, baseEnd_5889887] using wordTrace_append hprefix tailTrace_5889887
  have hstable : (prefixWord ++ tailWord_5889887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889887).length < 2 ^ (prefixWord ++ tailWord_5889887).sum := by decide
  have hdescent : baseEnd_5889887 < baseStart_5889887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5889936 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 6]
def baseStart_5889936 : Nat := 118140960795 + 5889936 * 2 ^ 59
def prefixEnd_5889936 : Nat := 4983230072969 + 3 ^ 40 * 5889936 * 2
def baseEnd_5889936 : Nat := 3024368192220172832012683

theorem tailTrace_5889936 : CollatzResearch.WordTrace tailWord_5889936 prefixEnd_5889936 3024368192220172832012683 := by
  unfold tailWord_5889936
  simp only [CollatzResearch.WordTrace]
  refine ⟨107411807194887633914224831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143215742926516845218966441 107411807194887633914224831)
  ·
    refine ⟨161117710792331450871337247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107411807194887633914224831 161117710792331450871337247)
    ·
      refine ⟨241676566188497176307005871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161117710792331450871337247 241676566188497176307005871)
      ·
        refine ⟨362514849282745764460508807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241676566188497176307005871 362514849282745764460508807)
        ·
          refine ⟨543772273924118646690763211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362514849282745764460508807 543772273924118646690763211)
          ·
            refine ⟨815658410886177970036144817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543772273924118646690763211 815658410886177970036144817)
            ·
              refine ⟨611743808164633477527108613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815658410886177970036144817 611743808164633477527108613)
              ·
                refine ⟨114701964030868777036332865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 611743808164633477527108613 114701964030868777036332865)
                ·
                  refine ⟨86026473023151582777249649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114701964030868777036332865 86026473023151582777249649)
                  ·
                    refine ⟨64519854767363687082937237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86026473023151582777249649 64519854767363687082937237)
                    ·
                      refine ⟨3024368192220172832012683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64519854767363687082937237 3024368192220172832012683)
                      ·
                        rfl

theorem cell23_5889936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_5889936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5889936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5889936 prefixEnd_5889936 := by exact prefixLift 5889936
  have htrace : WordTrace (prefixWord ++ tailWord_5889936) baseStart_5889936 baseEnd_5889936 := by
    simpa [prefixWord, tailWord_5889936, baseEnd_5889936] using wordTrace_append hprefix tailTrace_5889936
  have hstable : (prefixWord ++ tailWord_5889936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5889936).length < 2 ^ (prefixWord ++ tailWord_5889936).sum := by decide
  have hdescent : baseEnd_5889936 < baseStart_5889936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5889936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890010 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 2, 6]
def baseStart_5890010 : Nat := 118140960795 + 5890010 * 2 ^ 59
def prefixEnd_5890010 : Nat := 4983230072969 + 3 ^ 40 * 5890010 * 2
def baseEnd_5890010 : Nat := 1008135396596201847495781

theorem tailTrace_5890010 : CollatzResearch.WordTrace tailWord_5890010 prefixEnd_5890010 1008135396596201847495781 := by
  unfold tailWord_5890010
  simp only [CollatzResearch.WordTrace]
  refine ⟨53706578347876794616660871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143217542261004785644428989 53706578347876794616660871)
  ·
    refine ⟨80559867521815191924991307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53706578347876794616660871 80559867521815191924991307)
    ·
      refine ⟨120839801282722787887486961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80559867521815191924991307 120839801282722787887486961)
      ·
        refine ⟨90629850962042090915615221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120839801282722787887486961 90629850962042090915615221)
        ·
          refine ⟨8496548527691446023338927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90629850962042090915615221 8496548527691446023338927)
          ·
            refine ⟨12744822791537169035008391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8496548527691446023338927 12744822791537169035008391)
            ·
              refine ⟨19117234187305753552512587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12744822791537169035008391 19117234187305753552512587)
              ·
                refine ⟨28675851280958630328768881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19117234187305753552512587 28675851280958630328768881)
                ·
                  refine ⟨21506888460718972746576661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28675851280958630328768881 21506888460718972746576661)
                  ·
                    refine ⟨1008135396596201847495781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21506888460718972746576661 1008135396596201847495781)
                    ·
                      rfl

theorem cell23_5890010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_5890010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890010 prefixEnd_5890010 := by exact prefixLift 5890010
  have htrace : WordTrace (prefixWord ++ tailWord_5890010) baseStart_5890010 baseEnd_5890010 := by
    simpa [prefixWord, tailWord_5890010, baseEnd_5890010] using wordTrace_append hprefix tailTrace_5890010
  have hstable : (prefixWord ++ tailWord_5890010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890010).length < 2 ^ (prefixWord ++ tailWord_5890010).sum := by decide
  have hdescent : baseEnd_5890010 < baseStart_5890010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890038 : List Nat := [5, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_5890038 : Nat := 118140960795 + 5890038 * 2 ^ 59
def prefixEnd_5890038 : Nat := 4983230072969 + 3 ^ 40 * 5890038 * 2
def baseEnd_5890038 : Nat := 3024420567246931432937215

theorem tailTrace_5890038 : CollatzResearch.WordTrace tailWord_5890038 prefixEnd_5890038 3024420567246931432937215 := by
  unfold tailWord_5890038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13426708414712858703041423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143218223090270492832441845 13426708414712858703041423)
  ·
    refine ⟨20140062622069288054562135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13426708414712858703041423 20140062622069288054562135)
    ·
      refine ⟨30210093933103932081843203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20140062622069288054562135 30210093933103932081843203)
      ·
        refine ⟨45315140899655898122764805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30210093933103932081843203 45315140899655898122764805)
        ·
          refine ⟨8496588918685480898018401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45315140899655898122764805 8496588918685480898018401)
          ·
            refine ⟨6372441689014110673513801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8496588918685480898018401 6372441689014110673513801)
            ·
              refine ⟨4779331266760583005135351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6372441689014110673513801 4779331266760583005135351)
              ·
                refine ⟨7168996900140874507703027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779331266760583005135351 7168996900140874507703027)
                ·
                  refine ⟨10753495350211311761554541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7168996900140874507703027 10753495350211311761554541)
                  ·
                    refine ⟨4032560756329241910582953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10753495350211311761554541 4032560756329241910582953)
                    ·
                      refine ⟨3024420567246931432937215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4032560756329241910582953 3024420567246931432937215)
                      ·
                        rfl

theorem cell23_5890038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_5890038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890038 prefixEnd_5890038 := by exact prefixLift 5890038
  have htrace : WordTrace (prefixWord ++ tailWord_5890038) baseStart_5890038 baseEnd_5890038 := by
    simpa [prefixWord, tailWord_5890038, baseEnd_5890038] using wordTrace_append hprefix tailTrace_5890038
  have hstable : (prefixWord ++ tailWord_5890038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890038).length < 2 ^ (prefixWord ++ tailWord_5890038).sum := by decide
  have hdescent : baseEnd_5890038 < baseStart_5890038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890040 : List Nat := [2, 1, 2, 1, 1, 3, 3, 5, 5]
def baseStart_5890040 : Nat := 118140960795 + 5890040 * 2 ^ 59
def prefixEnd_5890040 : Nat := 4983230072969 + 3 ^ 40 * 5890040 * 2
def baseEnd_5890040 : Nat := 336046843800915602790245

theorem tailTrace_5890040 : CollatzResearch.WordTrace tailWord_5890040 prefixEnd_5890040 336046843800915602790245 := by
  unfold tailWord_5890040
  simp only [CollatzResearch.WordTrace]
  refine ⟨107413703790699246795117787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143218271720932329060157049 107413703790699246795117787)
  ·
    refine ⟨161120555686048870192676681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107413703790699246795117787 161120555686048870192676681)
    ·
      refine ⟨120840416764536652644507511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161120555686048870192676681 120840416764536652644507511)
      ·
        refine ⟨181260625146804978966761267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120840416764536652644507511 181260625146804978966761267)
        ·
          refine ⟨271890937720207468450141901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181260625146804978966761267 271890937720207468450141901)
          ·
            refine ⟨101959101645077800668803213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271890937720207468450141901 101959101645077800668803213)
            ·
              refine ⟨38234663116904175250801205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101959101645077800668803213 38234663116904175250801205)
              ·
                refine ⟨3584499667209766429762613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38234663116904175250801205 3584499667209766429762613)
                ·
                  refine ⟨336046843800915602790245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3584499667209766429762613 336046843800915602790245)
                  ·
                    rfl

theorem cell23_5890040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 5].length) (baseStart_5890040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890040 prefixEnd_5890040 := by exact prefixLift 5890040
  have htrace : WordTrace (prefixWord ++ tailWord_5890040) baseStart_5890040 baseEnd_5890040 := by
    simpa [prefixWord, tailWord_5890040, baseEnd_5890040] using wordTrace_append hprefix tailTrace_5890040
  have hstable : (prefixWord ++ tailWord_5890040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890040).length < 2 ^ (prefixWord ++ tailWord_5890040).sum := by decide
  have hdescent : baseEnd_5890040 < baseStart_5890040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890068 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_5890068 : Nat := 118140960795 + 5890068 * 2 ^ 59
def prefixEnd_5890068 : Nat := 4983230072969 + 3 ^ 40 * 5890068 * 2
def baseEnd_5890068 : Nat := 3024435971666566315562077

theorem tailTrace_5890068 : CollatzResearch.WordTrace tailWord_5890068 prefixEnd_5890068 3024435971666566315562077 := by
  unfold tailWord_5890068
  simp only [CollatzResearch.WordTrace]
  refine ⟨107414214412648527186127429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143218952550198036248169905 107414214412648527186127429)
  ·
    refine ⟨20140165202371598847398893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107414214412648527186127429 20140165202371598847398893)
    ·
      refine ⟨7552561950889349567774585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20140165202371598847398893 7552561950889349567774585)
      ·
        refine ⟨5664421463167012175830939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7552561950889349567774585 5664421463167012175830939)
        ·
          refine ⟨8496632194750518263746409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5664421463167012175830939 8496632194750518263746409)
          ·
            refine ⟨6372474146062888697809807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8496632194750518263746409 6372474146062888697809807)
            ·
              refine ⟨9558711219094333046714711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6372474146062888697809807 9558711219094333046714711)
              ·
                refine ⟨14338066828641499570072067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9558711219094333046714711 14338066828641499570072067)
                ·
                  refine ⟨21507100242962249355108101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14338066828641499570072067 21507100242962249355108101)
                  ·
                    refine ⟨4032581295555421754082769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21507100242962249355108101 4032581295555421754082769)
                    ·
                      refine ⟨3024435971666566315562077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4032581295555421754082769 3024435971666566315562077)
                      ·
                        rfl

theorem cell23_5890068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_5890068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890068 prefixEnd_5890068 := by exact prefixLift 5890068
  have htrace : WordTrace (prefixWord ++ tailWord_5890068) baseStart_5890068 baseEnd_5890068 := by
    simpa [prefixWord, tailWord_5890068, baseEnd_5890068] using wordTrace_append hprefix tailTrace_5890068
  have hstable : (prefixWord ++ tailWord_5890068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890068).length < 2 ^ (prefixWord ++ tailWord_5890068).sum := by decide
  have hdescent : baseEnd_5890068 < baseStart_5890068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890083 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 2, 8]
def baseStart_5890083 : Nat := 118140960795 + 5890083 * 2 ^ 59
def prefixEnd_5890083 : Nat := 4983230072969 + 3 ^ 40 * 5890083 * 2
def baseEnd_5890083 : Nat := 1008147891292127918958169

theorem tailTrace_5890083 : CollatzResearch.WordTrace tailWord_5890083 prefixEnd_5890083 1008147891292127918958169 := by
  unfold tailWord_5890083
  simp only [CollatzResearch.WordTrace]
  refine ⟨214828975920242711934050903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143219317280161807956033935 214828975920242711934050903)
  ·
    refine ⟨322243463880364067901076355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214828975920242711934050903 322243463880364067901076355)
    ·
      refine ⟨483365195820546101851614533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322243463880364067901076355 483365195820546101851614533)
      ·
        refine ⟨90630974216352394097177725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 483365195820546101851614533 90630974216352394097177725)
        ·
          refine ⟨33986615331132147786441647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90630974216352394097177725 33986615331132147786441647)
          ·
            refine ⟨50979922996698221679662471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33986615331132147786441647 50979922996698221679662471)
            ·
              refine ⟨76469884495047332519493707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50979922996698221679662471 76469884495047332519493707)
              ·
                refine ⟨114704826742570998779240561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76469884495047332519493707 114704826742570998779240561)
                ·
                  refine ⟨86028620056928249084430421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114704826742570998779240561 86028620056928249084430421)
                  ·
                    refine ⟨1008147891292127918958169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86028620056928249084430421 1008147891292127918958169)
                    ·
                      rfl

theorem cell23_5890083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 8].length) (baseStart_5890083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890083 prefixEnd_5890083 := by exact prefixLift 5890083
  have htrace : WordTrace (prefixWord ++ tailWord_5890083) baseStart_5890083 baseEnd_5890083 := by
    simpa [prefixWord, tailWord_5890083, baseEnd_5890083] using wordTrace_append hprefix tailTrace_5890083
  have hstable : (prefixWord ++ tailWord_5890083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890083).length < 2 ^ (prefixWord ++ tailWord_5890083).sum := by decide
  have hdescent : baseEnd_5890083 < baseStart_5890083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890103 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_5890103 : Nat := 118140960795 + 5890103 * 2 ^ 59
def prefixEnd_5890103 : Nat := 4983230072969 + 3 ^ 40 * 5890103 * 2
def baseEnd_5890103 : Nat := 3024453943489473678624415

theorem tailTrace_5890103 : CollatzResearch.WordTrace tailWord_5890103 prefixEnd_5890103 3024453943489473678624415 := by
  unfold tailWord_5890103
  simp only [CollatzResearch.WordTrace]
  refine ⟨214829705380170255349778963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143219803586780170233185975 214829705380170255349778963)
  ·
    refine ⟨322244558070255383024668445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214829705380170255349778963 322244558070255383024668445)
    ·
      refine ⟨120841709276345768634250667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322244558070255383024668445 120841709276345768634250667)
      ·
        refine ⟨181262563914518652951376001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120841709276345768634250667 181262563914518652951376001)
        ·
          refine ⟨135946922935888989713532001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181262563914518652951376001 135946922935888989713532001)
          ·
            refine ⟨101960192201916742285149001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135946922935888989713532001 101960192201916742285149001)
            ·
              refine ⟨76470144151437556713861751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101960192201916742285149001 76470144151437556713861751)
              ·
                refine ⟨114705216227156335070792627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76470144151437556713861751 114705216227156335070792627)
                ·
                  refine ⟨172057824340734502606188941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114705216227156335070792627 172057824340734502606188941)
                  ·
                    refine ⟨64521684127775438477320853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172057824340734502606188941 64521684127775438477320853)
                    ·
                      refine ⟨3024453943489473678624415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64521684127775438477320853 3024453943489473678624415)
                      ·
                        rfl

theorem cell23_5890103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_5890103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890103 prefixEnd_5890103 := by exact prefixLift 5890103
  have htrace : WordTrace (prefixWord ++ tailWord_5890103) baseStart_5890103 baseEnd_5890103 := by
    simpa [prefixWord, tailWord_5890103, baseEnd_5890103] using wordTrace_append hprefix tailTrace_5890103
  have hstable : (prefixWord ++ tailWord_5890103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890103).length < 2 ^ (prefixWord ++ tailWord_5890103).sum := by decide
  have hdescent : baseEnd_5890103 < baseStart_5890103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890197 : List Nat := [1, 3, 2, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_5890197 : Nat := 118140960795 + 5890197 * 2 ^ 59
def prefixEnd_5890197 : Nat := 4983230072969 + 3 ^ 40 * 5890197 * 2
def baseEnd_5890197 : Nat := 3024502210670996310848983

theorem tailTrace_5890197 : CollatzResearch.WordTrace tailWord_5890197 prefixEnd_5890197 3024502210670996310848983 := by
  unfold tailWord_5890197
  simp only [CollatzResearch.WordTrace]
  refine ⟨214833133841829709403700845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143222089227886472935800563 214833133841829709403700845)
  ·
    refine ⟨80562425190686141026387817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214833133841829709403700845 80562425190686141026387817)
    ·
      refine ⟨60421818893014605769790863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80562425190686141026387817 60421818893014605769790863)
      ·
        refine ⟨90632728339521908654686295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60421818893014605769790863 90632728339521908654686295)
        ·
          refine ⟨135949092509282862982029443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90632728339521908654686295 135949092509282862982029443)
          ·
            refine ⟨203923638763924294473044165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135949092509282862982029443 203923638763924294473044165)
            ·
              refine ⟨38235682268235805213695781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203923638763924294473044165 38235682268235805213695781)
              ·
                refine ⟨7169190425294213477567959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38235682268235805213695781 7169190425294213477567959)
                ·
                  refine ⟨10753785637941320216351939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7169190425294213477567959 10753785637941320216351939)
                  ·
                    refine ⟨16130678456911980324527909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10753785637941320216351939 16130678456911980324527909)
                    ·
                      refine ⟨3024502210670996310848983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16130678456911980324527909 3024502210670996310848983)
                      ·
                        rfl

theorem cell23_5890197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_5890197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890197 prefixEnd_5890197 := by exact prefixLift 5890197
  have htrace : WordTrace (prefixWord ++ tailWord_5890197) baseStart_5890197 baseEnd_5890197 := by
    simpa [prefixWord, tailWord_5890197, baseEnd_5890197] using wordTrace_append hprefix tailTrace_5890197
  have hstable : (prefixWord ++ tailWord_5890197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890197).length < 2 ^ (prefixWord ++ tailWord_5890197).sum := by decide
  have hdescent : baseEnd_5890197 < baseStart_5890197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890207 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 1, 6]
def baseStart_5890207 : Nat := 118140960795 + 5890207 * 2 ^ 59
def prefixEnd_5890207 : Nat := 4983230072969 + 3 ^ 40 * 5890207 * 2
def baseEnd_5890207 : Nat := 1008169115159180423907979

theorem tailTrace_5890207 : CollatzResearch.WordTrace tailWord_5890207 prefixEnd_5890207 1008169115159180423907979 := by
  unfold tailWord_5890207
  simp only [CollatzResearch.WordTrace]
  refine ⟨214833498571793481111564875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143222332381195654074376583 214833498571793481111564875)
  ·
    refine ⟨322250247857690221667347313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214833498571793481111564875 322250247857690221667347313)
    ·
      refine ⟨241687685893267666250510485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322250247857690221667347313 241687685893267666250510485)
      ·
        refine ⟨11329110276246921855492679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 241687685893267666250510485 11329110276246921855492679)
        ·
          refine ⟨16993665414370382783239019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11329110276246921855492679 16993665414370382783239019)
          ·
            refine ⟨25490498121555574174858529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16993665414370382783239019 25490498121555574174858529)
            ·
              refine ⟨19117873591166680631143897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25490498121555574174858529 19117873591166680631143897)
              ·
                refine ⟨14338405193375010473357923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19117873591166680631143897 14338405193375010473357923)
                ·
                  refine ⟨21507607790062515710036885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14338405193375010473357923 21507607790062515710036885)
                  ·
                    refine ⟨1008169115159180423907979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21507607790062515710036885 1008169115159180423907979)
                    ·
                      rfl

theorem cell23_5890207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_5890207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890207 prefixEnd_5890207 := by exact prefixLift 5890207
  have htrace : WordTrace (prefixWord ++ tailWord_5890207) baseStart_5890207 baseEnd_5890207 := by
    simpa [prefixWord, tailWord_5890207, baseEnd_5890207] using wordTrace_append hprefix tailTrace_5890207
  have hstable : (prefixWord ++ tailWord_5890207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890207).length < 2 ^ (prefixWord ++ tailWord_5890207).sum := by decide
  have hdescent : baseEnd_5890207 < baseStart_5890207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890231 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 3, 2, 2]
def baseStart_5890231 : Nat := 118140960795 + 5890231 * 2 ^ 59
def prefixEnd_5890231 : Nat := 4983230072969 + 3 ^ 40 * 5890231 * 2
def baseEnd_5890231 : Nat := 3024519669013249177823827

theorem tailTrace_5890231 : CollatzResearch.WordTrace tailWord_5890231 prefixEnd_5890231 3024519669013249177823827 := by
  unfold tailWord_5890231
  simp only [CollatzResearch.WordTrace]
  refine ⟨214834373923706533210438547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143222915949137688806959031 214834373923706533210438547)
  ·
    refine ⟨322251560885559799815657821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214834373923706533210438547 322251560885559799815657821)
    ·
      refine ⟨120844335332084924930871683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322251560885559799815657821 120844335332084924930871683)
      ·
        refine ⟨181266502998127387396307525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120844335332084924930871683 181266502998127387396307525)
        ·
          refine ⟨33987469312148885136807661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181266502998127387396307525 33987469312148885136807661)
          ·
            refine ⟨12745300992055831926302873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33987469312148885136807661 12745300992055831926302873)
            ·
              refine ⟨9558975744041873944727155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12745300992055831926302873 9558975744041873944727155)
              ·
                refine ⟨14338463616062810917090733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9558975744041873944727155 14338463616062810917090733)
                ·
                  refine ⟨5376923856023554093909025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14338463616062810917090733 5376923856023554093909025)
                  ·
                    refine ⟨4032692892017665570431769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5376923856023554093909025 4032692892017665570431769)
                    ·
                      refine ⟨3024519669013249177823827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4032692892017665570431769 3024519669013249177823827)
                      ·
                        rfl

theorem cell23_5890231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 2, 2].length) (baseStart_5890231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890231 prefixEnd_5890231 := by exact prefixLift 5890231
  have htrace : WordTrace (prefixWord ++ tailWord_5890231) baseStart_5890231 baseEnd_5890231 := by
    simpa [prefixWord, tailWord_5890231, baseEnd_5890231] using wordTrace_append hprefix tailTrace_5890231
  have hstable : (prefixWord ++ tailWord_5890231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890231).length < 2 ^ (prefixWord ++ tailWord_5890231).sum := by decide
  have hdescent : baseEnd_5890231 < baseStart_5890231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890241 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 1, 6]
def baseStart_5890241 : Nat := 118140960795 + 5890241 * 2 ^ 59
def prefixEnd_5890241 : Nat := 4983230072969 + 3 ^ 40 * 5890241 * 2
def baseEnd_5890241 : Nat := 1008174934606598046232927

theorem tailTrace_5890241 : CollatzResearch.WordTrace tailWord_5890241 prefixEnd_5890241 1008174934606598046232927 := by
  unfold tailWord_5890241
  simp only [CollatzResearch.WordTrace]
  refine ⟨214834738653670304918302577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143223159102446869945535051 214834738653670304918302577)
  ·
    refine ⟨161126053990252728688726933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214834738653670304918302577 161126053990252728688726933)
    ·
      refine ⟨7552783780793096657284075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 161126053990252728688726933 7552783780793096657284075)
      ·
        refine ⟨11329175671189644985926113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7552783780793096657284075 11329175671189644985926113)
        ·
          refine ⟨8496881753392233739444585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11329175671189644985926113 8496881753392233739444585)
          ·
            refine ⟨6372661315044175304583439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8496881753392233739444585 6372661315044175304583439)
            ·
              refine ⟨9558991972566262956875159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6372661315044175304583439 9558991972566262956875159)
              ·
                refine ⟨14338487958849394435312739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9558991972566262956875159 14338487958849394435312739)
                ·
                  refine ⟨21507731938274091652969109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14338487958849394435312739 21507731938274091652969109)
                  ·
                    refine ⟨1008174934606598046232927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21507731938274091652969109 1008174934606598046232927)
                    ·
                      rfl

theorem cell23_5890241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_5890241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890241 prefixEnd_5890241 := by exact prefixLift 5890241
  have htrace : WordTrace (prefixWord ++ tailWord_5890241) baseStart_5890241 baseEnd_5890241 := by
    simpa [prefixWord, tailWord_5890241, baseEnd_5890241] using wordTrace_append hprefix tailTrace_5890241
  have hstable : (prefixWord ++ tailWord_5890241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890241).length < 2 ^ (prefixWord ++ tailWord_5890241).sum := by decide
  have hdescent : baseEnd_5890241 < baseStart_5890241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890244 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_5890244 : Nat := 118140960795 + 5890244 * 2 ^ 59
def prefixEnd_5890244 : Nat := 4983230072969 + 3 ^ 40 * 5890244 * 2
def baseEnd_5890244 : Nat := 3024526344261757626961267

theorem tailTrace_5890244 : CollatzResearch.WordTrace tailWord_5890244 prefixEnd_5890244 3024526344261757626961267 := by
  unfold tailWord_5890244
  simp only [CollatzResearch.WordTrace]
  refine ⟨107417424036329718215330893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143223232048439624287107857 107417424036329718215330893)
  ·
    refine ⟨40281534013623644330749085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107417424036329718215330893 40281534013623644330749085)
    ·
      refine ⟨15105575255108866624030907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40281534013623644330749085 15105575255108866624030907)
      ·
        refine ⟨22658362882663299936046361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15105575255108866624030907 22658362882663299936046361)
        ·
          refine ⟨16993772161997474952034771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22658362882663299936046361 16993772161997474952034771)
          ·
            refine ⟨25490658242996212428052157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16993772161997474952034771 25490658242996212428052157)
            ·
              refine ⟨9558996841123579660519559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25490658242996212428052157 9558996841123579660519559)
              ·
                refine ⟨14338495261685369490779339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9558996841123579660519559 14338495261685369490779339)
                ·
                  refine ⟨21507742892528054236169009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14338495261685369490779339 21507742892528054236169009)
                  ·
                    refine ⟨16130807169396040677126757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21507742892528054236169009 16130807169396040677126757)
                    ·
                      refine ⟨3024526344261757626961267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16130807169396040677126757 3024526344261757626961267)
                      ·
                        rfl

theorem cell23_5890244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_5890244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890244 prefixEnd_5890244 := by exact prefixLift 5890244
  have htrace : WordTrace (prefixWord ++ tailWord_5890244) baseStart_5890244 baseEnd_5890244 := by
    simpa [prefixWord, tailWord_5890244, baseEnd_5890244] using wordTrace_append hprefix tailTrace_5890244
  have hstable : (prefixWord ++ tailWord_5890244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890244).length < 2 ^ (prefixWord ++ tailWord_5890244).sum := by decide
  have hdescent : baseEnd_5890244 < baseStart_5890244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890254 : List Nat := [4, 1, 1, 1, 4, 3, 2, 7]
def baseStart_5890254 : Nat := 118140960795 + 5890254 * 2 ^ 59
def prefixEnd_5890254 : Nat := 4983230072969 + 3 ^ 40 * 5890254 * 2
def baseEnd_5890254 : Nat := 112019684409937132882823

theorem tailTrace_5890254 : CollatzResearch.WordTrace tailWord_5890254 prefixEnd_5890254 112019684409937132882823 := by
  unfold tailWord_5890254
  simp only [CollatzResearch.WordTrace]
  refine ⟨26854401600327901017315727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143223475201748805425683877 26854401600327901017315727)
  ·
    refine ⟨40281602400491851525973591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26854401600327901017315727 40281602400491851525973591)
    ·
      refine ⟨60422403600737777288960387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40281602400491851525973591 60422403600737777288960387)
      ·
        refine ⟨90633605401106665933440581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60422403600737777288960387 90633605401106665933440581)
        ·
          refine ⟨16993801012707499862520109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90633605401106665933440581 16993801012707499862520109)
          ·
            refine ⟨6372675379765312448445041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16993801012707499862520109 6372675379765312448445041)
            ·
              refine ⟨4779506534823984336333781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6372675379765312448445041 4779506534823984336333781)
              ·
                refine ⟨112019684409937132882823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4779506534823984336333781 112019684409937132882823)
                ·
                  rfl

theorem cell23_5890254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_5890254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890254 prefixEnd_5890254 := by exact prefixLift 5890254
  have htrace : WordTrace (prefixWord ++ tailWord_5890254) baseStart_5890254 baseEnd_5890254 := by
    simpa [prefixWord, tailWord_5890254, baseEnd_5890254] using wordTrace_append hprefix tailTrace_5890254
  have hstable : (prefixWord ++ tailWord_5890254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890254).length < 2 ^ (prefixWord ++ tailWord_5890254).sum := by decide
  have hdescent : baseEnd_5890254 < baseStart_5890254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890264 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 4, 1, 3]
def baseStart_5890264 : Nat := 118140960795 + 5890264 * 2 ^ 59
def prefixEnd_5890264 : Nat := 4983230072969 + 3 ^ 40 * 5890264 * 2
def baseEnd_5890264 : Nat := 3024536613874847548711175

theorem tailTrace_5890264 : CollatzResearch.WordTrace tailWord_5890264 prefixEnd_5890264 3024536613874847548711175 := by
  unfold tailWord_5890264
  simp only [CollatzResearch.WordTrace]
  refine ⟨107417788766293489923194923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143223718355057986564259897 107417788766293489923194923)
  ·
    refine ⟨161126683149440234884792385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107417788766293489923194923 161126683149440234884792385)
    ·
      refine ⟨120845012362080176163594289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161126683149440234884792385 120845012362080176163594289)
      ·
        refine ⟨90633759271560132122695717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120845012362080176163594289 90633759271560132122695717)
        ·
          refine ⟨16993829863417524773005447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90633759271560132122695717 16993829863417524773005447)
          ·
            refine ⟨25490744795126287159508171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16993829863417524773005447 25490744795126287159508171)
            ·
              refine ⟨38236117192689430739262257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25490744795126287159508171 38236117192689430739262257)
              ·
                refine ⟨28677087894517073054446693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38236117192689430739262257 28677087894517073054446693)
                ·
                  refine ⟨5376953980221951197708755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28677087894517073054446693 5376953980221951197708755)
                  ·
                    refine ⟨8065430970332926796563133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5376953980221951197708755 8065430970332926796563133)
                    ·
                      refine ⟨3024536613874847548711175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8065430970332926796563133 3024536613874847548711175)
                      ·
                        rfl

theorem cell23_5890264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_5890264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890264 prefixEnd_5890264 := by exact prefixLift 5890264
  have htrace : WordTrace (prefixWord ++ tailWord_5890264) baseStart_5890264 baseEnd_5890264 := by
    simpa [prefixWord, tailWord_5890264, baseEnd_5890264] using wordTrace_append hprefix tailTrace_5890264
  have hstable : (prefixWord ++ tailWord_5890264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890264).length < 2 ^ (prefixWord ++ tailWord_5890264).sum := by decide
  have hdescent : baseEnd_5890264 < baseStart_5890264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890298 : List Nat := [3, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3]
def baseStart_5890298 : Nat := 118140960795 + 5890298 * 2 ^ 59
def prefixEnd_5890298 : Nat := 4983230072969 + 3 ^ 40 * 5890298 * 2
def baseEnd_5890298 : Nat := 3024554072217100415686019

theorem tailTrace_5890298 : CollatzResearch.WordTrace tailWord_5890298 prefixEnd_5890298 3024554072217100415686019 := by
  unfold tailWord_5890298
  simp only [CollatzResearch.WordTrace]
  refine ⟨53709204403615950913281887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143224545076309202435418365 53709204403615950913281887)
  ·
    refine ⟨80563806605423926369922831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53709204403615950913281887 80563806605423926369922831)
    ·
      refine ⟨120845709908135889554884247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80563806605423926369922831 120845709908135889554884247)
      ·
        refine ⟨181268564862203834332326371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120845709908135889554884247 181268564862203834332326371)
        ·
          refine ⟨271902847293305751498489557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181268564862203834332326371 271902847293305751498489557)
          ·
            refine ⟨6372722983436853550745849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 271902847293305751498489557 6372722983436853550745849)
            ·
              refine ⟨4779542237577640163059387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6372722983436853550745849 4779542237577640163059387)
              ·
                refine ⟨7169313356366460244589081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779542237577640163059387 7169313356366460244589081)
                ·
                  refine ⟨5376985017274845183441811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7169313356366460244589081 5376985017274845183441811)
                  ·
                    refine ⟨8065477525912267775162717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5376985017274845183441811 8065477525912267775162717)
                    ·
                      refine ⟨3024554072217100415686019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8065477525912267775162717 3024554072217100415686019)
                      ·
                        rfl

theorem cell23_5890298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3].length) (baseStart_5890298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890298 prefixEnd_5890298 := by exact prefixLift 5890298
  have htrace : WordTrace (prefixWord ++ tailWord_5890298) baseStart_5890298 baseEnd_5890298 := by
    simpa [prefixWord, tailWord_5890298, baseEnd_5890298] using wordTrace_append hprefix tailTrace_5890298
  have hstable : (prefixWord ++ tailWord_5890298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890298).length < 2 ^ (prefixWord ++ tailWord_5890298).sum := by decide
  have hdescent : baseEnd_5890298 < baseStart_5890298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890338 : List Nat := [3, 3, 1, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_5890338 : Nat := 118140960795 + 5890338 * 2 ^ 59
def prefixEnd_5890338 : Nat := 4983230072969 + 3 ^ 40 * 5890338 * 2
def baseEnd_5890338 : Nat := 3024574611443280259185835

theorem tailTrace_5890338 : CollatzResearch.WordTrace tailWord_5890338 prefixEnd_5890338 3024574611443280259185835 := by
  unfold tailWord_5890338
  simp only [CollatzResearch.WordTrace]
  refine ⟨53709569133579722621145917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143225517689545926989722445 53709569133579722621145917)
  ·
    refine ⟨20141088425092395982929719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53709569133579722621145917 20141088425092395982929719)
    ·
      refine ⟨30211632637638593974394579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20141088425092395982929719 30211632637638593974394579)
      ·
        refine ⟨45317448956457890961591869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30211632637638593974394579 45317448956457890961591869)
        ·
          refine ⟨16994043358671709110596951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45317448956457890961591869 16994043358671709110596951)
          ·
            refine ⟨25491065038007563665895427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16994043358671709110596951 25491065038007563665895427)
            ·
              refine ⟨38236597557011345498843141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25491065038007563665895427 38236597557011345498843141)
              ·
                refine ⟨7169362041939627281033089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38236597557011345498843141 7169362041939627281033089)
                ·
                  refine ⟨5377021531454720460774817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7169362041939627281033089 5377021531454720460774817)
                  ·
                    refine ⟨4032766148591040345581113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5377021531454720460774817 4032766148591040345581113)
                    ·
                      refine ⟨3024574611443280259185835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4032766148591040345581113 3024574611443280259185835)
                      ·
                        rfl

theorem cell23_5890338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_5890338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890338 prefixEnd_5890338 := by exact prefixLift 5890338
  have htrace : WordTrace (prefixWord ++ tailWord_5890338) baseStart_5890338 baseEnd_5890338 := by
    simpa [prefixWord, tailWord_5890338, baseEnd_5890338] using wordTrace_append hprefix tailTrace_5890338
  have hstable : (prefixWord ++ tailWord_5890338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890338).length < 2 ^ (prefixWord ++ tailWord_5890338).sum := by decide
  have hdescent : baseEnd_5890338 < baseStart_5890338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890357 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 1, 7]
def baseStart_5890357 : Nat := 118140960795 + 5890357 * 2 ^ 59
def prefixEnd_5890357 : Nat := 4983230072969 + 3 ^ 40 * 5890357 * 2
def baseEnd_5890357 : Nat := 1008194789191905228282749

theorem tailTrace_5890357 : CollatzResearch.WordTrace tailWord_5890357 prefixEnd_5890357 1008194789191905228282749 := by
  unfold tailWord_5890357
  simp only [CollatzResearch.WordTrace]
  refine ⟨214838969521250056729525325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143225979680833371153016883 214838969521250056729525325)
  ·
    refine ⟨80564613570468771273571997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214838969521250056729525325 80564613570468771273571997)
    ·
      refine ⟨30211730088925789227589499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80564613570468771273571997 30211730088925789227589499)
      ·
        refine ⟨45317595133388683841384249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30211730088925789227589499 45317595133388683841384249)
        ·
          refine ⟨33988196350041512881038187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45317595133388683841384249 33988196350041512881038187)
          ·
            refine ⟨50982294525062269321557281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33988196350041512881038187 50982294525062269321557281)
            ·
              refine ⟨38236720893796701991167961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50982294525062269321557281 38236720893796701991167961)
              ·
                refine ⟨28677540670347526493375971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38236720893796701991167961 28677540670347526493375971)
                ·
                  refine ⟨43016311005521289740063957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28677540670347526493375971 43016311005521289740063957)
                  ·
                    refine ⟨1008194789191905228282749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43016311005521289740063957 1008194789191905228282749)
                    ·
                      rfl

theorem cell23_5890357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_5890357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890357 prefixEnd_5890357 := by exact prefixLift 5890357
  have htrace : WordTrace (prefixWord ++ tailWord_5890357) baseStart_5890357 baseEnd_5890357 := by
    simpa [prefixWord, tailWord_5890357, baseEnd_5890357] using wordTrace_append hprefix tailTrace_5890357
  have hstable : (prefixWord ++ tailWord_5890357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890357).length < 2 ^ (prefixWord ++ tailWord_5890357).sum := by decide
  have hdescent : baseEnd_5890357 < baseStart_5890357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890364 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 2, 5, 2]
def baseStart_5890364 : Nat := 118140960795 + 5890364 * 2 ^ 59
def prefixEnd_5890364 : Nat := 4983230072969 + 3 ^ 40 * 5890364 * 2
def baseEnd_5890364 : Nat := 3024587961940297157460715

theorem tailTrace_5890364 : CollatzResearch.WordTrace tailWord_5890364 prefixEnd_5890364 3024587961940297157460715 := by
  unfold tailWord_5890364
  simp only [CollatzResearch.WordTrace]
  refine ⟨107419612416112348462515073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143226149888149797950020097 107419612416112348462515073)
  ·
    refine ⟨80564709312084261346886305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107419612416112348462515073 80564709312084261346886305)
    ·
      refine ⟨60423531984063196010164729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80564709312084261346886305 60423531984063196010164729)
      ·
        refine ⟨45317648988047397007623547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60423531984063196010164729 45317648988047397007623547)
        ·
          refine ⟨67976473482071095511435321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45317648988047397007623547 67976473482071095511435321)
          ·
            refine ⟨50982355111553321633576491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67976473482071095511435321 50982355111553321633576491)
            ·
              refine ⟨76473532667329982450364737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50982355111553321633576491 76473532667329982450364737)
              ·
                refine ⟨57355149500497486837773553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76473532667329982450364737 57355149500497486837773553)
                ·
                  refine ⟨43016362125373115128330165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57355149500497486837773553 43016362125373115128330165)
                  ·
                    refine ⟨4032783949253729543280953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43016362125373115128330165 4032783949253729543280953)
                    ·
                      refine ⟨3024587961940297157460715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4032783949253729543280953 3024587961940297157460715)
                      ·
                        rfl

theorem cell23_5890364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_5890364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890364 prefixEnd_5890364 := by exact prefixLift 5890364
  have htrace : WordTrace (prefixWord ++ tailWord_5890364) baseStart_5890364 baseEnd_5890364 := by
    simpa [prefixWord, tailWord_5890364, baseEnd_5890364] using wordTrace_append hprefix tailTrace_5890364
  have hstable : (prefixWord ++ tailWord_5890364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890364).length < 2 ^ (prefixWord ++ tailWord_5890364).sum := by decide
  have hdescent : baseEnd_5890364 < baseStart_5890364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890421 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 3, 4]
def baseStart_5890421 : Nat := 118140960795 + 5890421 * 2 ^ 59
def prefixEnd_5890421 : Nat := 4983230072969 + 3 ^ 40 * 5890421 * 2
def baseEnd_5890421 : Nat := 1008205743445867811482651

theorem tailTrace_5890421 : CollatzResearch.WordTrace tailWord_5890421 prefixEnd_5890421 1008205743445867811482651 := by
  unfold tailWord_5890421
  simp only [CollatzResearch.WordTrace]
  refine ⟨214841303793018195659855117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143227535862012130439903411 214841303793018195659855117)
  ·
    refine ⟨80565488922381823372445669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214841303793018195659855117 80565488922381823372445669)
    ·
      refine ⟨15106029172946591882333563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80565488922381823372445669 15106029172946591882333563)
      ·
        refine ⟨22659043759419887823500345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15106029172946591882333563 22659043759419887823500345)
        ·
          refine ⟨16994282819564915867625259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22659043759419887823500345 16994282819564915867625259)
          ·
            refine ⟨25491424229347373801437889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16994282819564915867625259 25491424229347373801437889)
            ·
              refine ⟨19118568172010530351078417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25491424229347373801437889 19118568172010530351078417)
              ·
                refine ⟨14338926129007897763308813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19118568172010530351078417 14338926129007897763308813)
                ·
                  refine ⟨5377097298377961661240805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14338926129007897763308813 5377097298377961661240805)
                  ·
                    refine ⟨1008205743445867811482651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5377097298377961661240805 1008205743445867811482651)
                    ·
                      rfl

theorem cell23_5890421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_5890421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890421 prefixEnd_5890421 := by exact prefixLift 5890421
  have htrace : WordTrace (prefixWord ++ tailWord_5890421) baseStart_5890421 baseEnd_5890421 := by
    simpa [prefixWord, tailWord_5890421, baseEnd_5890421] using wordTrace_append hprefix tailTrace_5890421
  have hstable : (prefixWord ++ tailWord_5890421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890421).length < 2 ^ (prefixWord ++ tailWord_5890421).sum := by decide
  have hdescent : baseEnd_5890421 < baseStart_5890421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890481 : List Nat := [1, 2, 2, 4, 1, 2, 3, 2, 1, 5]
def baseStart_5890481 : Nat := 118140960795 + 5890481 * 2 ^ 59
def prefixEnd_5890481 : Nat := 4983230072969 + 3 ^ 40 * 5890481 * 2
def baseEnd_5890481 : Nat := 1008216013058957733232559

theorem tailTrace_5890481 : CollatzResearch.WordTrace tailWord_5890481 prefixEnd_5890481 1008216013058957733232559 := by
  unfold tailWord_5890481
  simp only [CollatzResearch.WordTrace]
  refine ⟨214843492172800825907039297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143228994781867217271359531 214843492172800825907039297)
  ·
    refine ⟨161132619129600619430279473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214843492172800825907039297 161132619129600619430279473)
    ·
      refine ⟨120849464347200464572709605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161132619129600619430279473 120849464347200464572709605)
      ·
        refine ⟨22659274565100087107383051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120849464347200464572709605 22659274565100087107383051)
        ·
          refine ⟨33988911847650130661074577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22659274565100087107383051 33988911847650130661074577)
          ·
            refine ⟨25491683885737597995805933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33988911847650130661074577 25491683885737597995805933)
            ·
              refine ⟨9559381457151599248427225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25491683885737597995805933 9559381457151599248427225)
              ·
                refine ⟨7169536092863699436320419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9559381457151599248427225 7169536092863699436320419)
                ·
                  refine ⟨10754304139295549154480629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7169536092863699436320419 10754304139295549154480629)
                  ·
                    refine ⟨1008216013058957733232559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10754304139295549154480629 1008216013058957733232559)
                    ·
                      rfl

theorem cell23_5890481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_5890481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890481 prefixEnd_5890481 := by exact prefixLift 5890481
  have htrace : WordTrace (prefixWord ++ tailWord_5890481) baseStart_5890481 baseEnd_5890481 := by
    simpa [prefixWord, tailWord_5890481, baseEnd_5890481] using wordTrace_append hprefix tailTrace_5890481
  have hstable : (prefixWord ++ tailWord_5890481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890481).length < 2 ^ (prefixWord ++ tailWord_5890481).sum := by decide
  have hdescent : baseEnd_5890481 < baseStart_5890481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890494 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_5890494 : Nat := 118140960795 + 5890494 * 2 ^ 59
def prefixEnd_5890494 : Nat := 4983230072969 + 3 ^ 40 * 5890494 * 2
def baseEnd_5890494 : Nat := 1008218238141793882945039

theorem tailTrace_5890494 : CollatzResearch.WordTrace tailWord_5890494 prefixEnd_5890494 1008218238141793882945039 := by
  unfold tailWord_5890494
  simp only [CollatzResearch.WordTrace]
  refine ⟨26855495790219216140907817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143229310881169152751508357 26855495790219216140907817)
  ·
    refine ⟨20141621842664412105680863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26855495790219216140907817 20141621842664412105680863)
    ·
      refine ⟨30212432763996618158521295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20141621842664412105680863 30212432763996618158521295)
      ·
        refine ⟨45318649145994927237781943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30212432763996618158521295 45318649145994927237781943)
        ·
          refine ⟨67977973718992390856672915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45318649145994927237781943 67977973718992390856672915)
          ·
            refine ⟨101966960578488586285009373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67977973718992390856672915 101966960578488586285009373)
            ·
              refine ⟨38237610216933219856878515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101966960578488586285009373 38237610216933219856878515)
              ·
                refine ⟨57356415325399829785317773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38237610216933219856878515 57356415325399829785317773)
                ·
                  refine ⟨21508655747024936169494165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57356415325399829785317773 21508655747024936169494165)
                  ·
                    refine ⟨1008218238141793882945039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21508655747024936169494165 1008218238141793882945039)
                    ·
                      rfl

theorem cell23_5890494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_5890494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890494 prefixEnd_5890494 := by exact prefixLift 5890494
  have htrace : WordTrace (prefixWord ++ tailWord_5890494) baseStart_5890494 baseEnd_5890494 := by
    simpa [prefixWord, tailWord_5890494, baseEnd_5890494] using wordTrace_append hprefix tailTrace_5890494
  have hstable : (prefixWord ++ tailWord_5890494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890494).length < 2 ^ (prefixWord ++ tailWord_5890494).sum := by decide
  have hdescent : baseEnd_5890494 < baseStart_5890494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890562 : List Nat := [3, 4, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_5890562 : Nat := 118140960795 + 5890562 * 2 ^ 59
def prefixEnd_5890562 : Nat := 4983230072969 + 3 ^ 40 * 5890562 * 2
def baseEnd_5890562 : Nat := 1008229877036629127594935

theorem tailTrace_5890562 : CollatzResearch.WordTrace tailWord_5890562 prefixEnd_5890562 1008229877036629127594935 := by
  unfold tailWord_5890562
  simp only [CollatzResearch.WordTrace]
  refine ⟨53711611621376844185184485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143230964323671584493825293 53711611621376844185184485)
  ·
    refine ⟨10070927179008158284722091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53711611621376844185184485 10070927179008158284722091)
    ·
      refine ⟨15106390768512237427083137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10070927179008158284722091 15106390768512237427083137)
      ·
        refine ⟨11329793076384178070312353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15106390768512237427083137 11329793076384178070312353)
        ·
          refine ⟨8497344807288133552734265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11329793076384178070312353 8497344807288133552734265)
          ·
            refine ⟨6373008605466100164550699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8497344807288133552734265 6373008605466100164550699)
            ·
              refine ⟨9559512908199150246826049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6373008605466100164550699 9559512908199150246826049)
              ·
                refine ⟨7169634681149362685119537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9559512908199150246826049 7169634681149362685119537)
                ·
                  refine ⟨5377226010862022013839653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7169634681149362685119537 5377226010862022013839653)
                  ·
                    refine ⟨1008229877036629127594935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5377226010862022013839653 1008229877036629127594935)
                    ·
                      rfl

theorem cell23_5890562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_5890562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890562 prefixEnd_5890562 := by exact prefixLift 5890562
  have htrace : WordTrace (prefixWord ++ tailWord_5890562) baseStart_5890562 baseEnd_5890562 := by
    simpa [prefixWord, tailWord_5890562, baseEnd_5890562] using wordTrace_append hprefix tailTrace_5890562
  have hstable : (prefixWord ++ tailWord_5890562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890562).length < 2 ^ (prefixWord ++ tailWord_5890562).sum := by decide
  have hdescent : baseEnd_5890562 < baseStart_5890562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890595 : List Nat := [1, 1, 1, 4, 4, 2, 2, 2, 1, 3, 2]
def baseStart_5890595 : Nat := 118140960795 + 5890595 * 2 ^ 59
def prefixEnd_5890595 : Nat := 4983230072969 + 3 ^ 40 * 5890595 * 2
def baseEnd_5890595 : Nat := 3024706575971485753672153

theorem tailTrace_5890595 : CollatzResearch.WordTrace tailWord_5890595 prefixEnd_5890595 3024706575971485753672153 := by
  unfold tailWord_5890595
  simp only [CollatzResearch.WordTrace]
  refine ⟨214847650094387823376689239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143231766729591882251126159 214847650094387823376689239)
  ·
    refine ⟨322271475141581735065033859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214847650094387823376689239 322271475141581735065033859)
    ·
      refine ⟨483407212712372602597550789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322271475141581735065033859 483407212712372602597550789)
      ·
        refine ⟨90638852383569862987040773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 483407212712372602597550789 90638852383569862987040773)
        ·
          refine ⟨16994784821919349310070145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90638852383569862987040773 16994784821919349310070145)
          ·
            refine ⟨12746088616439511982552609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16994784821919349310070145 12746088616439511982552609)
            ·
              refine ⟨9559566462329633986914457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12746088616439511982552609 9559566462329633986914457)
              ·
                refine ⟨7169674846747225490185843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9559566462329633986914457 7169674846747225490185843)
                ·
                  refine ⟨10754512270120838235278765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7169674846747225490185843 10754512270120838235278765)
                  ·
                    refine ⟨4032942101295314338229537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10754512270120838235278765 4032942101295314338229537)
                    ·
                      refine ⟨3024706575971485753672153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4032942101295314338229537 3024706575971485753672153)
                      ·
                        rfl

theorem cell23_5890595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_5890595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890595 prefixEnd_5890595 := by exact prefixLift 5890595
  have htrace : WordTrace (prefixWord ++ tailWord_5890595) baseStart_5890595 baseEnd_5890595 := by
    simpa [prefixWord, tailWord_5890595, baseEnd_5890595] using wordTrace_append hprefix tailTrace_5890595
  have hstable : (prefixWord ++ tailWord_5890595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890595).length < 2 ^ (prefixWord ++ tailWord_5890595).sum := by decide
  have hdescent : baseEnd_5890595 < baseStart_5890595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890604 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_5890604 : Nat := 118140960795 + 5890604 * 2 ^ 59
def prefixEnd_5890604 : Nat := 4983230072969 + 3 ^ 40 * 5890604 * 2
def baseEnd_5890604 : Nat := 3024711197297376218459611

theorem tailTrace_5890604 : CollatzResearch.WordTrace tailWord_5890604 prefixEnd_5890604 3024711197297376218459611 := by
  unfold tailWord_5890604
  simp only [CollatzResearch.WordTrace]
  refine ⟨107423989175677608956883433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143231985567570145275844577 107423989175677608956883433)
  ·
    refine ⟨80567991881758206717662575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107423989175677608956883433 80567991881758206717662575)
    ·
      refine ⟨120851987822637310076493863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80567991881758206717662575 120851987822637310076493863)
      ·
        refine ⟨181277981733955965114740795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120851987822637310076493863 181277981733955965114740795)
        ·
          refine ⟨271916972600933947672111193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181277981733955965114740795 271916972600933947672111193)
          ·
            refine ⟨203937729450700460754083395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271916972600933947672111193 203937729450700460754083395)
            ·
              refine ⟨305906594176050691131125093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203937729450700460754083395 305906594176050691131125093)
              ·
                refine ⟨57357486408009504587085955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305906594176050691131125093 57357486408009504587085955)
                ·
                  refine ⟨86036229612014256880628933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57357486408009504587085955 86036229612014256880628933)
                  ·
                    refine ⟨16131793052252673165117925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86036229612014256880628933 16131793052252673165117925)
                    ·
                      refine ⟨3024711197297376218459611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16131793052252673165117925 3024711197297376218459611)
                      ·
                        rfl

theorem cell23_5890604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_5890604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890604 prefixEnd_5890604 := by exact prefixLift 5890604
  have htrace : WordTrace (prefixWord ++ tailWord_5890604) baseStart_5890604 baseEnd_5890604 := by
    simpa [prefixWord, tailWord_5890604, baseEnd_5890604] using wordTrace_append hprefix tailTrace_5890604
  have hstable : (prefixWord ++ tailWord_5890604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890604).length < 2 ^ (prefixWord ++ tailWord_5890604).sum := by decide
  have hdescent : baseEnd_5890604 < baseStart_5890604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890608 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 4, 2, 2]
def baseStart_5890608 : Nat := 118140960795 + 5890608 * 2 ^ 59
def prefixEnd_5890608 : Nat := 4983230072969 + 3 ^ 40 * 5890608 * 2
def baseEnd_5890608 : Nat := 3024713251219994202809593

theorem tailTrace_5890608 : CollatzResearch.WordTrace tailWord_5890608 prefixEnd_5890608 3024713251219994202809593 := by
  unfold tailWord_5890608
  simp only [CollatzResearch.WordTrace]
  refine ⟨107424062121670363298456239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143232082828893817731274985 107424062121670363298456239)
  ·
    refine ⟨161136093182505544947684359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107424062121670363298456239 161136093182505544947684359)
    ·
      refine ⟨241704139773758317421526539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161136093182505544947684359 241704139773758317421526539)
      ·
        refine ⟨362556209660637476132289809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241704139773758317421526539 362556209660637476132289809)
        ·
          refine ⟨271917157245478107099217357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362556209660637476132289809 271917157245478107099217357)
          ·
            refine ⟨101968933967054290162206509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271917157245478107099217357 101968933967054290162206509)
            ·
              refine ⟨38238350237645358810827441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101968933967054290162206509 38238350237645358810827441)
              ·
                refine ⟨28678762678234019108120581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38238350237645358810827441 28678762678234019108120581)
                ·
                  refine ⟨5377268002168878582772609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28678762678234019108120581 5377268002168878582772609)
                  ·
                    refine ⟨4032951001626658937079457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5377268002168878582772609 4032951001626658937079457)
                    ·
                      refine ⟨3024713251219994202809593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4032951001626658937079457 3024713251219994202809593)
                      ·
                        rfl

theorem cell23_5890608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 4, 2, 2].length) (baseStart_5890608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890608 prefixEnd_5890608 := by exact prefixLift 5890608
  have htrace : WordTrace (prefixWord ++ tailWord_5890608) baseStart_5890608 baseEnd_5890608 := by
    simpa [prefixWord, tailWord_5890608, baseEnd_5890608] using wordTrace_append hprefix tailTrace_5890608
  have hstable : (prefixWord ++ tailWord_5890608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890608).length < 2 ^ (prefixWord ++ tailWord_5890608).sum := by decide
  have hdescent : baseEnd_5890608 < baseStart_5890608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890625 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_5890625 : Nat := 118140960795 + 5890625 * 2 ^ 59
def prefixEnd_5890625 : Nat := 4983230072969 + 3 ^ 40 * 5890625 * 2
def baseEnd_5890625 : Nat := 3024721980391120636297015

theorem tailTrace_5890625 : CollatzResearch.WordTrace tailWord_5890625 prefixEnd_5890625 3024721980391120636297015 := by
  unfold tailWord_5890625
  simp only [CollatzResearch.WordTrace]
  refine ⟨214848744284279138500281329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143232496189519425666854219 214848744284279138500281329)
  ·
    refine ⟨161136558213209353875210997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214848744284279138500281329 161136558213209353875210997)
    ·
      refine ⟨15106552332488376925801031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161136558213209353875210997 15106552332488376925801031)
      ·
        refine ⟨22659828498732565388701547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15106552332488376925801031 22659828498732565388701547)
        ·
          refine ⟨33989742748098848083052321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22659828498732565388701547 33989742748098848083052321)
          ·
            refine ⟨25492307061074136062289241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33989742748098848083052321 25492307061074136062289241)
            ·
              refine ⟨19119230295805602046716931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25492307061074136062289241 19119230295805602046716931)
              ·
                refine ⟨28678845443708403070075397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19119230295805602046716931 28678845443708403070075397)
                ·
                  refine ⟨5377283520695325575639137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28678845443708403070075397 5377283520695325575639137)
                  ·
                    refine ⟨4032962640521494181729353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5377283520695325575639137 4032962640521494181729353)
                    ·
                      refine ⟨3024721980391120636297015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4032962640521494181729353 3024721980391120636297015)
                      ·
                        rfl

theorem cell23_5890625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_5890625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890625 prefixEnd_5890625 := by exact prefixLift 5890625
  have htrace : WordTrace (prefixWord ++ tailWord_5890625) baseStart_5890625 baseEnd_5890625 := by
    simpa [prefixWord, tailWord_5890625, baseEnd_5890625] using wordTrace_append hprefix tailTrace_5890625
  have hstable : (prefixWord ++ tailWord_5890625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890625).length < 2 ^ (prefixWord ++ tailWord_5890625).sum := by decide
  have hdescent : baseEnd_5890625 < baseStart_5890625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890631 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 7]
def baseStart_5890631 : Nat := 118140960795 + 5890631 * 2 ^ 59
def prefixEnd_5890631 : Nat := 4983230072969 + 3 ^ 40 * 5890631 * 2
def baseEnd_5890631 : Nat := 336080562363894179202443

theorem tailTrace_5890631 : CollatzResearch.WordTrace tailWord_5890631 prefixEnd_5890631 336080562363894179202443 := by
  unfold tailWord_5890631
  simp only [CollatzResearch.WordTrace]
  refine ⟨214848963122257401524999747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143232642081504934349999831 214848963122257401524999747)
  ·
    refine ⟨322273444683386102287499621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214848963122257401524999747 322273444683386102287499621)
    ·
      refine ⟨60426270878134894178906179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 322273444683386102287499621 60426270878134894178906179)
      ·
        refine ⟨90639406317202341268359269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60426270878134894178906179 90639406317202341268359269)
        ·
          refine ⟨16994888684475438987817363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90639406317202341268359269 16994888684475438987817363)
          ·
            refine ⟨25492333026713158481726045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16994888684475438987817363 25492333026713158481726045)
            ·
              refine ⟨9559624885017434430647267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25492333026713158481726045 9559624885017434430647267)
              ·
                refine ⟨14339437327526151645970901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9559624885017434430647267 14339437327526151645970901)
                ·
                  refine ⟨336080562363894179202443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14339437327526151645970901 336080562363894179202443)
                  ·
                    rfl

theorem cell23_5890631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 7].length) (baseStart_5890631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890631 prefixEnd_5890631 := by exact prefixLift 5890631
  have htrace : WordTrace (prefixWord ++ tailWord_5890631) baseStart_5890631 baseEnd_5890631 := by
    simpa [prefixWord, tailWord_5890631, baseEnd_5890631] using wordTrace_append hprefix tailTrace_5890631
  have hstable : (prefixWord ++ tailWord_5890631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890631).length < 2 ^ (prefixWord ++ tailWord_5890631).sum := by decide
  have hdescent : baseEnd_5890631 < baseStart_5890631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890704 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 12]
def baseStart_5890704 : Nat := 118140960795 + 5890704 * 2 ^ 59
def prefixEnd_5890704 : Nat := 4983230072969 + 3 ^ 40 * 5890704 * 2
def baseEnd_5890704 : Nat := 336084727262536203023239

theorem tailTrace_5890704 : CollatzResearch.WordTrace tailWord_5890704 prefixEnd_5890704 336084727262536203023239 := by
  unfold tailWord_5890704
  simp only [CollatzResearch.WordTrace]
  refine ⟨107425812825496467496203583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143234417100661956661604777 107425812825496467496203583)
  ·
    refine ⟨161138719238244701244305375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107425812825496467496203583 161138719238244701244305375)
    ·
      refine ⟨241708078857367051866458063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161138719238244701244305375 241708078857367051866458063)
      ·
        refine ⟨362562118286050577799687095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241708078857367051866458063 362562118286050577799687095)
        ·
          refine ⟨543843177429075866699530643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362562118286050577799687095 543843177429075866699530643)
          ·
            refine ⟨815764766143613800049295965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543843177429075866699530643 815764766143613800049295965)
            ·
              refine ⟨305911787303855175018485987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 815764766143613800049295965 305911787303855175018485987)
              ·
                refine ⟨458867680955782762527728981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305911787303855175018485987 458867680955782762527728981)
                ·
                  refine ⟨336084727262536203023239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 458867680955782762527728981 336084727262536203023239)
                  ·
                    rfl

theorem cell23_5890704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 12].length) (baseStart_5890704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890704 prefixEnd_5890704 := by exact prefixLift 5890704
  have htrace : WordTrace (prefixWord ++ tailWord_5890704) baseStart_5890704 baseEnd_5890704 := by
    simpa [prefixWord, tailWord_5890704, baseEnd_5890704] using wordTrace_append hprefix tailTrace_5890704
  have hstable : (prefixWord ++ tailWord_5890704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890704).length < 2 ^ (prefixWord ++ tailWord_5890704).sum := by decide
  have hdescent : baseEnd_5890704 < baseStart_5890704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890792 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_5890792 : Nat := 118140960795 + 5890792 * 2 ^ 59
def prefixEnd_5890792 : Nat := 4983230072969 + 3 ^ 40 * 5890792 * 2
def baseEnd_5890792 : Nat := 3024807731660421482908747

theorem tailTrace_5890792 : CollatzResearch.WordTrace tailWord_5890792 prefixEnd_5890792 3024807731660421482908747 := by
  unfold tailWord_5890792
  simp only [CollatzResearch.WordTrace]
  refine ⟨107427417637337063010805315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143236556849782750681073753 107427417637337063010805315)
  ·
    refine ⟨161141126456005594516207973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107427417637337063010805315 161141126456005594516207973)
    ·
      refine ⟨30213961210501048971788995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161141126456005594516207973 30213961210501048971788995)
      ·
        refine ⟨45320941815751573457683493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30213961210501048971788995 45320941815751573457683493)
        ·
          refine ⟨8497676590453420023315655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45320941815751573457683493 8497676590453420023315655)
          ·
            refine ⟨12746514885680130034973483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8497676590453420023315655 12746514885680130034973483)
            ·
              refine ⟨19119772328520195052460225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12746514885680130034973483 19119772328520195052460225)
              ·
                refine ⟨14339829246390146289345169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19119772328520195052460225 14339829246390146289345169)
                ·
                  refine ⟨10754871934792609717008877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14339829246390146289345169 10754871934792609717008877)
                  ·
                    refine ⟨4033076975547228643878329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10754871934792609717008877 4033076975547228643878329)
                    ·
                      refine ⟨3024807731660421482908747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4033076975547228643878329 3024807731660421482908747)
                      ·
                        rfl

theorem cell23_5890792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_5890792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890792 prefixEnd_5890792 := by exact prefixLift 5890792
  have htrace : WordTrace (prefixWord ++ tailWord_5890792) baseStart_5890792 baseEnd_5890792 := by
    simpa [prefixWord, tailWord_5890792, baseEnd_5890792] using wordTrace_append hprefix tailTrace_5890792
  have hstable : (prefixWord ++ tailWord_5890792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890792).length < 2 ^ (prefixWord ++ tailWord_5890792).sum := by decide
  have hdescent : baseEnd_5890792 < baseStart_5890792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890799 : List Nat := [1, 1, 2, 1, 5, 3, 3, 2, 1, 1, 3]
def baseStart_5890799 : Nat := 118140960795 + 5890799 * 2 ^ 59
def prefixEnd_5890799 : Nat := 4983230072969 + 3 ^ 40 * 5890799 * 2
def baseEnd_5890799 : Nat := 3024811326025002955521215

theorem tailTrace_5890799 : CollatzResearch.WordTrace tailWord_5890799 prefixEnd_5890799 3024811326025002955521215 := by
  unfold tailWord_5890799
  simp only [CollatzResearch.WordTrace]
  refine ⟨214855090585648766217115451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143236727057099177478076967 214855090585648766217115451)
  ·
    refine ⟨322282635878473149325673177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214855090585648766217115451 322282635878473149325673177)
    ·
      refine ⟨241711976908854861994254883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322282635878473149325673177 241711976908854861994254883)
      ·
        refine ⟨362567965363282292991382325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241711976908854861994254883 362567965363282292991382325)
        ·
          refine ⟨33990746752807714967942093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 362567965363282292991382325 33990746752807714967942093)
          ·
            refine ⟨12746530032302893112978285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33990746752807714967942093 12746530032302893112978285)
            ·
              refine ⟨4779948762113584917366857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12746530032302893112978285 4779948762113584917366857)
              ·
                refine ⟨3584961571585188688025143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4779948762113584917366857 3584961571585188688025143)
                ·
                  refine ⟨5377442357377783032037715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3584961571585188688025143 5377442357377783032037715)
                  ·
                    refine ⟨8066163536066674548056573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5377442357377783032037715 8066163536066674548056573)
                    ·
                      refine ⟨3024811326025002955521215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8066163536066674548056573 3024811326025002955521215)
                      ·
                        rfl

theorem cell23_5890799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 1, 1, 3].length) (baseStart_5890799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890799 prefixEnd_5890799 := by exact prefixLift 5890799
  have htrace : WordTrace (prefixWord ++ tailWord_5890799) baseStart_5890799 baseEnd_5890799 := by
    simpa [prefixWord, tailWord_5890799, baseEnd_5890799] using wordTrace_append hprefix tailTrace_5890799
  have hstable : (prefixWord ++ tailWord_5890799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890799).length < 2 ^ (prefixWord ++ tailWord_5890799).sum := by decide
  have hdescent : baseEnd_5890799 < baseStart_5890799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890801 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_5890801 : Nat := 118140960795 + 5890801 * 2 ^ 59
def prefixEnd_5890801 : Nat := 4983230072969 + 3 ^ 40 * 5890801 * 2
def baseEnd_5890801 : Nat := 3024812352986311947696205

theorem tailTrace_5890801 : CollatzResearch.WordTrace tailWord_5890801 prefixEnd_5890801 3024812352986311947696205 := by
  unfold tailWord_5890801
  simp only [CollatzResearch.WordTrace]
  refine ⟨214855163531641520558688257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143236775687761013705792171 214855163531641520558688257)
  ·
    refine ⟨161141372648731140419016193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214855163531641520558688257 161141372648731140419016193)
    ·
      refine ⟨120856029486548355314262145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161141372648731140419016193 120856029486548355314262145)
      ·
        refine ⟨90642022114911266485696609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120856029486548355314262145 90642022114911266485696609)
        ·
          refine ⟨67981516586183449864272457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90642022114911266485696609 67981516586183449864272457)
          ·
            refine ⟨50986137439637587398204343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67981516586183449864272457 50986137439637587398204343)
            ·
              refine ⟨76479206159456381097306515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50986137439637587398204343 76479206159456381097306515)
              ·
                refine ⟨114718809239184571645959773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76479206159456381097306515 114718809239184571645959773)
                ·
                  refine ⟨43019553464694214367234915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114718809239184571645959773 43019553464694214367234915)
                  ·
                    refine ⟨64529330197041321550852373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43019553464694214367234915 64529330197041321550852373)
                    ·
                      refine ⟨3024812352986311947696205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64529330197041321550852373 3024812352986311947696205)
                      ·
                        rfl

theorem cell23_5890801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_5890801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890801 prefixEnd_5890801 := by exact prefixLift 5890801
  have htrace : WordTrace (prefixWord ++ tailWord_5890801) baseStart_5890801 baseEnd_5890801 := by
    simpa [prefixWord, tailWord_5890801, baseEnd_5890801] using wordTrace_append hprefix tailTrace_5890801
  have hstable : (prefixWord ++ tailWord_5890801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890801).length < 2 ^ (prefixWord ++ tailWord_5890801).sum := by decide
  have hdescent : baseEnd_5890801 < baseStart_5890801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890808 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 3, 2, 3]
def baseStart_5890808 : Nat := 118140960795 + 5890808 * 2 ^ 59
def prefixEnd_5890808 : Nat := 4983230072969 + 3 ^ 40 * 5890808 * 2
def baseEnd_5890808 : Nat := 3024815947350893420308673

theorem tailTrace_5890808 : CollatzResearch.WordTrace tailWord_5890808 prefixEnd_5890808 3024815947350893420308673 := by
  unfold tailWord_5890808
  simp only [CollatzResearch.WordTrace]
  refine ⟨107427709421308080377096539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143236945895077440502795385 107427709421308080377096539)
  ·
    refine ⟨161141564131962120565644809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107427709421308080377096539 161141564131962120565644809)
    ·
      refine ⟨120856173098971590424233607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161141564131962120565644809 120856173098971590424233607)
      ·
        refine ⟨181284259648457385636350411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120856173098971590424233607 181284259648457385636350411)
        ·
          refine ⟨271926389472686078454525617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181284259648457385636350411 271926389472686078454525617)
          ·
            refine ⟨203944792104514558840894213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271926389472686078454525617 203944792104514558840894213)
            ·
              refine ⟨38239648519596479782667665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203944792104514558840894213 38239648519596479782667665)
              ·
                refine ⟨28679736389697359837000749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38239648519596479782667665 28679736389697359837000749)
                ·
                  refine ⟨10754901146136509938875281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28679736389697359837000749 10754901146136509938875281)
                  ·
                    refine ⟨8066175859602382454156461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10754901146136509938875281 8066175859602382454156461)
                    ·
                      refine ⟨3024815947350893420308673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8066175859602382454156461 3024815947350893420308673)
                      ·
                        rfl

theorem cell23_5890808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_5890808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890808 prefixEnd_5890808 := by exact prefixLift 5890808
  have htrace : WordTrace (prefixWord ++ tailWord_5890808) baseStart_5890808 baseEnd_5890808 := by
    simpa [prefixWord, tailWord_5890808, baseEnd_5890808] using wordTrace_append hprefix tailTrace_5890808
  have hstable : (prefixWord ++ tailWord_5890808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890808).length < 2 ^ (prefixWord ++ tailWord_5890808).sum := by decide
  have hdescent : baseEnd_5890808 < baseStart_5890808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890825 : List Nat := [1, 2, 1, 1, 3, 2, 5, 2, 1, 2, 3]
def baseStart_5890825 : Nat := 118140960795 + 5890825 * 2 ^ 59
def prefixEnd_5890825 : Nat := 4983230072969 + 3 ^ 40 * 5890825 * 2
def baseEnd_5890825 : Nat := 3024824676522019853796095

theorem tailTrace_5890825 : CollatzResearch.WordTrace tailWord_5890825 prefixEnd_5890825 3024824676522019853796095 := by
  unfold tailWord_5890825
  simp only [CollatzResearch.WordTrace]
  refine ⟨214856038883554572657561929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143237359255703048438374619 214856038883554572657561929)
  ·
    refine ⟨161142029162665929493171447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214856038883554572657561929 161142029162665929493171447)
    ·
      refine ⟨241713043743998894239757171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161142029162665929493171447 241713043743998894239757171)
      ·
        refine ⟨362569565615998341359635757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241713043743998894239757171 362569565615998341359635757)
        ·
          refine ⟨135963587105999378009863409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362569565615998341359635757 135963587105999378009863409)
          ·
            refine ⟨101972690329499533507397557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135963587105999378009863409 101972690329499533507397557)
            ·
              refine ⟨9559939718390581266318521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101972690329499533507397557 9559939718390581266318521)
              ·
                refine ⟨7169954788792935949738891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9559939718390581266318521 7169954788792935949738891)
                ·
                  refine ⟨10754932183189403924608337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7169954788792935949738891 10754932183189403924608337)
                  ·
                    refine ⟨8066199137392052943456253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10754932183189403924608337 8066199137392052943456253)
                    ·
                      refine ⟨3024824676522019853796095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8066199137392052943456253 3024824676522019853796095)
                      ·
                        rfl

theorem cell23_5890825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 2, 3].length) (baseStart_5890825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890825 prefixEnd_5890825 := by exact prefixLift 5890825
  have htrace : WordTrace (prefixWord ++ tailWord_5890825) baseStart_5890825 baseEnd_5890825 := by
    simpa [prefixWord, tailWord_5890825, baseEnd_5890825] using wordTrace_append hprefix tailTrace_5890825
  have hstable : (prefixWord ++ tailWord_5890825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890825).length < 2 ^ (prefixWord ++ tailWord_5890825).sum := by decide
  have hdescent : baseEnd_5890825 < baseStart_5890825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890842 : List Nat := [3, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3]
def baseStart_5890842 : Nat := 118140960795 + 5890842 * 2 ^ 59
def prefixEnd_5890842 : Nat := 4983230072969 + 3 ^ 40 * 5890842 * 2
def baseEnd_5890842 : Nat := 3024833405693146287283517

theorem tailTrace_5890842 : CollatzResearch.WordTrace tailWord_5890842 prefixEnd_5890842 3024833405693146287283517 := by
  unfold tailWord_5890842
  simp only [CollatzResearch.WordTrace]
  refine ⟨53714164731123246140232695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143237772616328656373953853 53714164731123246140232695)
  ·
    refine ⟨80571247096684869210349043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53714164731123246140232695 80571247096684869210349043)
    ·
      refine ⟨120856870645027303815523565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80571247096684869210349043 120856870645027303815523565)
      ·
        refine ⟨45321326491885238930821337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120856870645027303815523565 45321326491885238930821337)
        ·
          refine ⟨33990994868913929198116003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45321326491885238930821337 33990994868913929198116003)
          ·
            refine ⟨50986492303370893797174005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33990994868913929198116003 50986492303370893797174005)
            ·
              refine ⟨4779983653441021293485063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50986492303370893797174005 4779983653441021293485063)
              ·
                refine ⟨7169975480161531940227595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779983653441021293485063 7169975480161531940227595)
                ·
                  refine ⟨10754963220242297910341393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7169975480161531940227595 10754963220242297910341393)
                  ·
                    refine ⟨8066222415181723432756045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10754963220242297910341393 8066222415181723432756045)
                    ·
                      refine ⟨3024833405693146287283517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8066222415181723432756045 3024833405693146287283517)
                      ·
                        rfl

theorem cell23_5890842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_5890842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890842 prefixEnd_5890842 := by exact prefixLift 5890842
  have htrace : WordTrace (prefixWord ++ tailWord_5890842) baseStart_5890842 baseEnd_5890842 := by
    simpa [prefixWord, tailWord_5890842, baseEnd_5890842] using wordTrace_append hprefix tailTrace_5890842
  have hstable : (prefixWord ++ tailWord_5890842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890842).length < 2 ^ (prefixWord ++ tailWord_5890842).sum := by decide
  have hdescent : baseEnd_5890842 < baseStart_5890842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890845 : List Nat := [1, 4, 2, 4, 2, 10]
def baseStart_5890845 : Nat := 118140960795 + 5890845 * 2 ^ 59
def prefixEnd_5890845 : Nat := 4983230072969 + 3 ^ 40 * 5890845 * 2
def baseEnd_5890845 : Nat := 12447880436769999076321

theorem tailTrace_5890845 : CollatzResearch.WordTrace tailWord_5890845 prefixEnd_5890845 12447880436769999076321 := by
  unfold tailWord_5890845
  simp only [CollatzResearch.WordTrace]
  refine ⟨214856768343482116073289989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143237845562321410715526659 214856768343482116073289989)
  ·
    refine ⟨40285644064402896763741873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214856768343482116073289989 40285644064402896763741873)
    ·
      refine ⟨30214233048302172572806405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40285644064402896763741873 30214233048302172572806405)
      ·
        refine ⟨5665168696556657357401201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30214233048302172572806405 5665168696556657357401201)
        ·
          refine ⟨4248876522417493018050901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5665168696556657357401201 4248876522417493018050901)
          ·
            refine ⟨12447880436769999076321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4248876522417493018050901 12447880436769999076321)
            ·
              rfl

theorem cell23_5890845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 10].length) (baseStart_5890845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890845 prefixEnd_5890845 := by exact prefixLift 5890845
  have htrace : WordTrace (prefixWord ++ tailWord_5890845) baseStart_5890845 baseEnd_5890845 := by
    simpa [prefixWord, tailWord_5890845, baseEnd_5890845] using wordTrace_append hprefix tailTrace_5890845
  have hstable : (prefixWord ++ tailWord_5890845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890845).length < 2 ^ (prefixWord ++ tailWord_5890845).sum := by decide
  have hdescent : baseEnd_5890845 < baseStart_5890845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890865 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 5, 3, 2]
def baseStart_5890865 : Nat := 118140960795 + 5890865 * 2 ^ 59
def prefixEnd_5890865 : Nat := 4983230072969 + 3 ^ 40 * 5890865 * 2
def baseEnd_5890865 : Nat := 3024845215748199697295911

theorem tailTrace_5890865 : CollatzResearch.WordTrace tailWord_5890865 prefixEnd_5890865 3024845215748199697295911 := by
  unfold tailWord_5890865
  simp only [CollatzResearch.WordTrace]
  refine ⟨214857497803409659489018049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143238331868939772992678699 214857497803409659489018049)
  ·
    refine ⟨161143123352557244616763537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214857497803409659489018049 161143123352557244616763537)
    ·
      refine ⟨120857342514417933462572653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161143123352557244616763537 120857342514417933462572653)
      ·
        refine ⟨45321503442906725048464745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120857342514417933462572653 45321503442906725048464745)
        ·
          refine ⟨33991127582180043786348559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45321503442906725048464745 33991127582180043786348559)
          ·
            refine ⟨50986691373270065679522839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33991127582180043786348559 50986691373270065679522839)
            ·
              refine ⟨76480037059905098519284259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50986691373270065679522839 76480037059905098519284259)
              ·
                refine ⟨114720055589857647778926389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76480037059905098519284259 114720055589857647778926389)
                ·
                  refine ⟨10755005211549154479274349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114720055589857647778926389 10755005211549154479274349)
                  ·
                    refine ⟨4033126954330932929727881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10755005211549154479274349 4033126954330932929727881)
                    ·
                      refine ⟨3024845215748199697295911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4033126954330932929727881 3024845215748199697295911)
                      ·
                        rfl

theorem cell23_5890865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_5890865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890865 prefixEnd_5890865 := by exact prefixLift 5890865
  have htrace : WordTrace (prefixWord ++ tailWord_5890865) baseStart_5890865 baseEnd_5890865 := by
    simpa [prefixWord, tailWord_5890865, baseEnd_5890865] using wordTrace_append hprefix tailTrace_5890865
  have hstable : (prefixWord ++ tailWord_5890865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890865).length < 2 ^ (prefixWord ++ tailWord_5890865).sum := by decide
  have hdescent : baseEnd_5890865 < baseStart_5890865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890893 : List Nat := [1, 6, 1, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_5890893 : Nat := 118140960795 + 5890893 * 2 ^ 59
def prefixEnd_5890893 : Nat := 4983230072969 + 3 ^ 40 * 5890893 * 2
def baseEnd_5890893 : Nat := 3024859593206525587745783

theorem tailTrace_5890893 : CollatzResearch.WordTrace tailWord_5890893 prefixEnd_5890893 3024859593206525587745783 := by
  unfold tailWord_5890893
  simp only [CollatzResearch.WordTrace]
  refine ⟨214858519047308220271037333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143239012698205480180691555 214858519047308220271037333)
  ·
    refine ⟨10071493080342572825204875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 214858519047308220271037333 10071493080342572825204875)
    ·
      refine ⟨15107239620513859237807313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10071493080342572825204875 15107239620513859237807313)
      ·
        refine ⟨11330429715385394428355485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15107239620513859237807313 11330429715385394428355485)
        ·
          refine ⟨4248911143269522910633307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11330429715385394428355485 4248911143269522910633307)
          ·
            refine ⟨6373366714904284365949961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4248911143269522910633307 6373366714904284365949961)
            ·
              refine ⟨4780025036178213274462471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6373366714904284365949961 4780025036178213274462471)
              ·
                refine ⟨7170037554267319911693707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4780025036178213274462471 7170037554267319911693707)
                ·
                  refine ⟨10755056331400979867540561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7170037554267319911693707 10755056331400979867540561)
                  ·
                    refine ⟨8066292248550734900655421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10755056331400979867540561 8066292248550734900655421)
                    ·
                      refine ⟨3024859593206525587745783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8066292248550734900655421 3024859593206525587745783)
                      ·
                        rfl

theorem cell23_5890893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_5890893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890893 prefixEnd_5890893 := by exact prefixLift 5890893
  have htrace : WordTrace (prefixWord ++ tailWord_5890893) baseStart_5890893 baseEnd_5890893 := by
    simpa [prefixWord, tailWord_5890893, baseEnd_5890893] using wordTrace_append hprefix tailTrace_5890893
  have hstable : (prefixWord ++ tailWord_5890893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890893).length < 2 ^ (prefixWord ++ tailWord_5890893).sum := by decide
  have hdescent : baseEnd_5890893 < baseStart_5890893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890898 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_5890898 : Nat := 118140960795 + 5890898 * 2 ^ 59
def prefixEnd_5890898 : Nat := 4983230072969 + 3 ^ 40 * 5890898 * 2
def baseEnd_5890898 : Nat := 3024862160609798068183259

theorem tailTrace_5890898 : CollatzResearch.WordTrace tailWord_5890898 prefixEnd_5890898 3024862160609798068183259 := by
  unfold tailWord_5890898
  simp only [CollatzResearch.WordTrace]
  refine ⟨53714675353072526531242337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143239134274860070749979565 53714675353072526531242337)
  ·
    refine ⟨40286006514804394898431753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53714675353072526531242337 40286006514804394898431753)
    ·
      refine ⟨30214504886103296173823815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40286006514804394898431753 30214504886103296173823815)
      ·
        refine ⟨45321757329154944260735723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30214504886103296173823815 45321757329154944260735723)
        ·
          refine ⟨67982635993732416391103585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45321757329154944260735723 67982635993732416391103585)
          ·
            refine ⟨50986976995299312293327689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67982635993732416391103585 50986976995299312293327689)
            ·
              refine ⟨38240232746474484219995767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50986976995299312293327689 38240232746474484219995767)
              ·
                refine ⟨57360349119711726329993651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38240232746474484219995767 57360349119711726329993651)
                ·
                  refine ⟨86040523679567589494990477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57360349119711726329993651 86040523679567589494990477)
                  ·
                    refine ⟨32265196379837846060621429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86040523679567589494990477 32265196379837846060621429)
                    ·
                      refine ⟨3024862160609798068183259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32265196379837846060621429 3024862160609798068183259)
                      ·
                        rfl

theorem cell23_5890898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_5890898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890898 prefixEnd_5890898 := by exact prefixLift 5890898
  have htrace : WordTrace (prefixWord ++ tailWord_5890898) baseStart_5890898 baseEnd_5890898 := by
    simpa [prefixWord, tailWord_5890898, baseEnd_5890898] using wordTrace_append hprefix tailTrace_5890898
  have hstable : (prefixWord ++ tailWord_5890898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890898).length < 2 ^ (prefixWord ++ tailWord_5890898).sum := by decide
  have hdescent : baseEnd_5890898 < baseStart_5890898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890912 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 4, 2, 2]
def baseStart_5890912 : Nat := 118140960795 + 5890912 * 2 ^ 59
def prefixEnd_5890912 : Nat := 4983230072969 + 3 ^ 40 * 5890912 * 2
def baseEnd_5890912 : Nat := 3024869349338961013408195

theorem tailTrace_5890912 : CollatzResearch.WordTrace tailWord_5890912 prefixEnd_5890912 3024869349338961013408195 := by
  unfold tailWord_5890912
  simp only [CollatzResearch.WordTrace]
  refine ⟨107429606017119693257989495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143239474689492924343985993 107429606017119693257989495)
  ·
    refine ⟨161144409025679539886984243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107429606017119693257989495 161144409025679539886984243)
    ·
      refine ⟨241716613538519309830476365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161144409025679539886984243 241716613538519309830476365)
      ·
        refine ⟨90643730076944741186428637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241716613538519309830476365 90643730076944741186428637)
        ·
          refine ⟨33991398778854277944910739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90643730076944741186428637 33991398778854277944910739)
          ·
            refine ⟨50987098168281416917366109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33991398778854277944910739 50987098168281416917366109)
            ·
              refine ⟨19120161813105531344012291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50987098168281416917366109 19120161813105531344012291)
              ·
                refine ⟨28680242719658297016018437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19120161813105531344012291 28680242719658297016018437)
                ·
                  refine ⟨5377545509935930690503457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28680242719658297016018437 5377545509935930690503457)
                  ·
                    refine ⟨4033159132451948017877593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5377545509935930690503457 4033159132451948017877593)
                    ·
                      refine ⟨3024869349338961013408195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4033159132451948017877593 3024869349338961013408195)
                      ·
                        rfl

theorem cell23_5890912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_5890912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890912 prefixEnd_5890912 := by exact prefixLift 5890912
  have htrace : WordTrace (prefixWord ++ tailWord_5890912) baseStart_5890912 baseEnd_5890912 := by
    simpa [prefixWord, tailWord_5890912, baseEnd_5890912] using wordTrace_append hprefix tailTrace_5890912
  have hstable : (prefixWord ++ tailWord_5890912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890912).length < 2 ^ (prefixWord ++ tailWord_5890912).sum := by decide
  have hdescent : baseEnd_5890912 < baseStart_5890912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890952 : List Nat := [2, 1, 3, 3, 2, 1, 3, 3, 5]
def baseStart_5890952 : Nat := 118140960795 + 5890952 * 2 ^ 59
def prefixEnd_5890952 : Nat := 4983230072969 + 3 ^ 40 * 5890952 * 2
def baseEnd_5890952 : Nat := 336098876507237872989779

theorem tailTrace_5890952 : CollatzResearch.WordTrace tailWord_5890952 prefixEnd_5890952 336098876507237872989779 := by
  unfold tailWord_5890952
  simp only [CollatzResearch.WordTrace]
  refine ⟨107430335477047236673717555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143240447302729648898290073 107430335477047236673717555)
  ·
    refine ⟨161145503215570855010576333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107430335477047236673717555 161145503215570855010576333)
    ·
      refine ⟨60429563705839070628966125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161145503215570855010576333 60429563705839070628966125)
      ·
        refine ⟨22661086389689651485862297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60429563705839070628966125 22661086389689651485862297)
        ·
          refine ⟨16995814792267238614396723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22661086389689651485862297 16995814792267238614396723)
          ·
            refine ⟨25493722188400857921595085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16995814792267238614396723 25493722188400857921595085)
            ·
              refine ⟨9560145820650321720598157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25493722188400857921595085 9560145820650321720598157)
              ·
                refine ⟨3585054682743870645224309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9560145820650321720598157 3585054682743870645224309)
                ·
                  refine ⟨336098876507237872989779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3585054682743870645224309 336098876507237872989779)
                  ·
                    rfl

theorem cell23_5890952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 5].length) (baseStart_5890952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890952 prefixEnd_5890952 := by exact prefixLift 5890952
  have htrace : WordTrace (prefixWord ++ tailWord_5890952) baseStart_5890952 baseEnd_5890952 := by
    simpa [prefixWord, tailWord_5890952, baseEnd_5890952] using wordTrace_append hprefix tailTrace_5890952
  have hstable : (prefixWord ++ tailWord_5890952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890952).length < 2 ^ (prefixWord ++ tailWord_5890952).sum := by decide
  have hdescent : baseEnd_5890952 < baseStart_5890952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890965 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 2, 5]
def baseStart_5890965 : Nat := 118140960795 + 5890965 * 2 ^ 59
def prefixEnd_5890965 : Nat := 4983230072969 + 3 ^ 40 * 5890965 * 2
def baseEnd_5890965 : Nat := 1008298854604549768681817

theorem tailTrace_5890965 : CollatzResearch.WordTrace tailWord_5890965 prefixEnd_5890965 1008298854604549768681817 := by
  unfold tailWord_5890965
  simp only [CollatzResearch.WordTrace]
  refine ⟨214861145103047376567658349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143240763402031584378438899 214861145103047376567658349)
  ·
    refine ⟨80572929413642766212871881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214861145103047376567658349 80572929413642766212871881)
    ·
      refine ⟨60429697060232074659653911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80572929413642766212871881 60429697060232074659653911)
      ·
        refine ⟨90644545590348111989480867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60429697060232074659653911 90644545590348111989480867)
        ·
          refine ⟨135966818385522167984221301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90644545590348111989480867 135966818385522167984221301)
          ·
            refine ⟨12746889223642703248520747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135966818385522167984221301 12746889223642703248520747)
            ·
              refine ⟨19120333835464054872781121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12746889223642703248520747 19120333835464054872781121)
              ·
                refine ⟨14340250376598041154585841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19120333835464054872781121 14340250376598041154585841)
                ·
                  refine ⟨10755187782448530865939381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14340250376598041154585841 10755187782448530865939381)
                  ·
                    refine ⟨1008298854604549768681817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10755187782448530865939381 1008298854604549768681817)
                    ·
                      rfl

theorem cell23_5890965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_5890965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890965 prefixEnd_5890965 := by exact prefixLift 5890965
  have htrace : WordTrace (prefixWord ++ tailWord_5890965) baseStart_5890965 baseEnd_5890965 := by
    simpa [prefixWord, tailWord_5890965, baseEnd_5890965] using wordTrace_append hprefix tailTrace_5890965
  have hstable : (prefixWord ++ tailWord_5890965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890965).length < 2 ^ (prefixWord ++ tailWord_5890965).sum := by decide
  have hdescent : baseEnd_5890965 < baseStart_5890965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890975 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 5]
def baseStart_5890975 : Nat := 118140960795 + 5890975 * 2 ^ 59
def prefixEnd_5890975 : Nat := 4983230072969 + 3 ^ 40 * 5890975 * 2
def baseEnd_5890975 : Nat := 3024901698620194266920405

theorem tailTrace_5890975 : CollatzResearch.WordTrace tailWord_5890975 prefixEnd_5890975 3024901698620194266920405 := by
  unfold tailWord_5890975
  simp only [CollatzResearch.WordTrace]
  refine ⟨214861509833011148275522379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143241006555340765517014919 214861509833011148275522379)
  ·
    refine ⟨322292264749516722413283569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214861509833011148275522379 322292264749516722413283569)
    ·
      refine ⟨241719198562137541809962677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322292264749516722413283569 241719198562137541809962677)
      ·
        refine ⟨22661174865200394544684001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241719198562137541809962677 22661174865200394544684001)
        ·
          refine ⟨16995881148900295908513001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22661174865200394544684001 16995881148900295908513001)
          ·
            refine ⟨12746910861675221931384751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16995881148900295908513001 12746910861675221931384751)
            ·
              refine ⟨19120366292512832897077127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12746910861675221931384751 19120366292512832897077127)
              ·
                refine ⟨28680549438769249345615691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19120366292512832897077127 28680549438769249345615691)
                ·
                  refine ⟨43020824158153874018423537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28680549438769249345615691 43020824158153874018423537)
                  ·
                    refine ⟨32265618118615405513817653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43020824158153874018423537 32265618118615405513817653)
                    ·
                      refine ⟨3024901698620194266920405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32265618118615405513817653 3024901698620194266920405)
                      ·
                        rfl

theorem cell23_5890975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_5890975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890975 prefixEnd_5890975 := by exact prefixLift 5890975
  have htrace : WordTrace (prefixWord ++ tailWord_5890975) baseStart_5890975 baseEnd_5890975 := by
    simpa [prefixWord, tailWord_5890975, baseEnd_5890975] using wordTrace_append hprefix tailTrace_5890975
  have hstable : (prefixWord ++ tailWord_5890975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890975).length < 2 ^ (prefixWord ++ tailWord_5890975).sum := by decide
  have hdescent : baseEnd_5890975 < baseStart_5890975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5890985 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 1, 6, 2]
def baseStart_5890985 : Nat := 118140960795 + 5890985 * 2 ^ 59
def prefixEnd_5890985 : Nat := 4983230072969 + 3 ^ 40 * 5890985 * 2
def baseEnd_5890985 : Nat := 3024906833426739227795359

theorem tailTrace_5890985 : CollatzResearch.WordTrace tailWord_5890985 prefixEnd_5890985 3024906833426739227795359 := by
  unfold tailWord_5890985
  simp only [CollatzResearch.WordTrace]
  refine ⟨214861874562974919983386409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143241249708649946655590939 214861874562974919983386409)
  ·
    refine ⟨161146405922231189987539807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214861874562974919983386409 161146405922231189987539807)
    ·
      refine ⟨241719608883346784981309711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161146405922231189987539807 241719608883346784981309711)
      ·
        refine ⟨362579413325020177471964567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241719608883346784981309711 362579413325020177471964567)
        ·
          refine ⟨543869119987530266207946851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362579413325020177471964567 543869119987530266207946851)
          ·
            refine ⟨815803679981295399311920277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543869119987530266207946851 815803679981295399311920277)
            ·
              refine ⟨38240797499123221842746263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 815803679981295399311920277 38240797499123221842746263)
              ·
                refine ⟨57361196248684832764119395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38240797499123221842746263 57361196248684832764119395)
                ·
                  refine ⟨86041794373027249146179093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57361196248684832764119395 86041794373027249146179093)
                  ·
                    refine ⟨4033209111235652303727145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86041794373027249146179093 4033209111235652303727145)
                    ·
                      refine ⟨3024906833426739227795359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4033209111235652303727145 3024906833426739227795359)
                      ·
                        rfl

theorem cell23_5890985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 6, 2].length) (baseStart_5890985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5890985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5890985 prefixEnd_5890985 := by exact prefixLift 5890985
  have htrace : WordTrace (prefixWord ++ tailWord_5890985) baseStart_5890985 baseEnd_5890985 := by
    simpa [prefixWord, tailWord_5890985, baseEnd_5890985] using wordTrace_append hprefix tailTrace_5890985
  have hstable : (prefixWord ++ tailWord_5890985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5890985).length < 2 ^ (prefixWord ++ tailWord_5890985).sum := by decide
  have hdescent : baseEnd_5890985 < baseStart_5890985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5890985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891022 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_5891022 : Nat := 118140960795 + 5891022 * 2 ^ 59
def prefixEnd_5891022 : Nat := 4983230072969 + 3 ^ 40 * 5891022 * 2
def baseEnd_5891022 : Nat := 3024925832210955583032689

theorem tailTrace_5891022 : CollatzResearch.WordTrace tailWord_5891022 prefixEnd_5891022 3024925832210955583032689 := by
  unfold tailWord_5891022
  simp only [CollatzResearch.WordTrace]
  refine ⟨26857903007980109412810415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143242149375893916868322213 26857903007980109412810415)
  ·
    refine ⟨40286854511970164119215623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26857903007980109412810415 40286854511970164119215623)
    ·
      refine ⟨60430281767955246178823435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40286854511970164119215623 60430281767955246178823435)
      ·
        refine ⟨90645422651932869268235153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60430281767955246178823435 90645422651932869268235153)
        ·
          refine ⟨67984066988949651951176365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90645422651932869268235153 67984066988949651951176365)
          ·
            refine ⟨25494025120856119481691137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67984066988949651951176365 25494025120856119481691137)
            ·
              refine ⟨19120518840642089611268353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25494025120856119481691137 19120518840642089611268353)
              ·
                refine ⟨14340389130481567208451265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19120518840642089611268353 14340389130481567208451265)
                ·
                  refine ⟨10755291847861175406338449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14340389130481567208451265 10755291847861175406338449)
                  ·
                    refine ⟨8066468885895881554753837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10755291847861175406338449 8066468885895881554753837)
                    ·
                      refine ⟨3024925832210955583032689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8066468885895881554753837 3024925832210955583032689)
                      ·
                        rfl

theorem cell23_5891022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_5891022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891022 prefixEnd_5891022 := by exact prefixLift 5891022
  have htrace : WordTrace (prefixWord ++ tailWord_5891022) baseStart_5891022 baseEnd_5891022 := by
    simpa [prefixWord, tailWord_5891022, baseEnd_5891022] using wordTrace_append hprefix tailTrace_5891022
  have hstable : (prefixWord ++ tailWord_5891022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891022).length < 2 ^ (prefixWord ++ tailWord_5891022).sum := by decide
  have hdescent : baseEnd_5891022 < baseStart_5891022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891025 : List Nat := [1, 2, 2, 1, 2, 1, 6, 2, 6]
def baseStart_5891025 : Nat := 118140960795 + 5891025 * 2 ^ 59
def prefixEnd_5891025 : Nat := 4983230072969 + 3 ^ 40 * 5891025 * 2
def baseEnd_5891025 : Nat := 336103041405879896810575

theorem tailTrace_5891025 : CollatzResearch.WordTrace tailWord_5891025 prefixEnd_5891025 336103041405879896810575 := by
  unfold tailWord_5891025
  simp only [CollatzResearch.WordTrace]
  refine ⟨214863333482830006814842529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143242222321886671209895019 214863333482830006814842529)
  ·
    refine ⟨161147500112122505111131897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214863333482830006814842529 161147500112122505111131897)
    ·
      refine ⟨120860625084091878833348923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161147500112122505111131897 120860625084091878833348923)
      ·
        refine ⟨181290937626137818250023385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120860625084091878833348923 181290937626137818250023385)
        ·
          refine ⟨135968203219603363687517539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181290937626137818250023385 135968203219603363687517539)
          ·
            refine ⟨203952304829405045531276309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135968203219603363687517539 203952304829405045531276309)
            ·
              refine ⟨9560264288878361509278577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 203952304829405045531276309 9560264288878361509278577)
              ·
                refine ⟨7170198216658771131958933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9560264288878361509278577 7170198216658771131958933)
                ·
                  refine ⟨336103041405879896810575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7170198216658771131958933 336103041405879896810575)
                  ·
                    rfl

theorem cell23_5891025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 6].length) (baseStart_5891025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891025 prefixEnd_5891025 := by exact prefixLift 5891025
  have htrace : WordTrace (prefixWord ++ tailWord_5891025) baseStart_5891025 baseEnd_5891025 := by
    simpa [prefixWord, tailWord_5891025, baseEnd_5891025] using wordTrace_append hprefix tailTrace_5891025
  have hstable : (prefixWord ++ tailWord_5891025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891025).length < 2 ^ (prefixWord ++ tailWord_5891025).sum := by decide
  have hdescent : baseEnd_5891025 < baseStart_5891025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891055 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 3, 5]
def baseStart_5891055 : Nat := 118140960795 + 5891055 * 2 ^ 59
def prefixEnd_5891055 : Nat := 4983230072969 + 3 ^ 40 * 5891055 * 2
def baseEnd_5891055 : Nat := 1008314259024184651306679

theorem tailTrace_5891055 : CollatzResearch.WordTrace tailWord_5891055 prefixEnd_5891055 1008314259024184651306679 := by
  unfold tailWord_5891055
  simp only [CollatzResearch.WordTrace]
  refine ⟨214864427672721321938434619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143242951781814214625623079 214864427672721321938434619)
  ·
    refine ⟨322296641509081982907651929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214864427672721321938434619 322296641509081982907651929)
    ·
      refine ⟨241722481131811487180738947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322296641509081982907651929 241722481131811487180738947)
      ·
        refine ⟨362583721697717230771108421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241722481131811487180738947 362583721697717230771108421)
        ·
          refine ⟨67984447818321980769582829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362583721697717230771108421 67984447818321980769582829)
          ·
            refine ⟨25494167931870742788593561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67984447818321980769582829 25494167931870742788593561)
            ·
              refine ⟨19120625948903057091445171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25494167931870742788593561 19120625948903057091445171)
              ·
                refine ⟨28680938923354585637167757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19120625948903057091445171 28680938923354585637167757)
                ·
                  refine ⟨10755352096257969613937909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28680938923354585637167757 10755352096257969613937909)
                  ·
                    refine ⟨1008314259024184651306679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10755352096257969613937909 1008314259024184651306679)
                    ·
                      rfl

theorem cell23_5891055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_5891055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891055 prefixEnd_5891055 := by exact prefixLift 5891055
  have htrace : WordTrace (prefixWord ++ tailWord_5891055) baseStart_5891055 baseEnd_5891055 := by
    simpa [prefixWord, tailWord_5891055, baseEnd_5891055] using wordTrace_append hprefix tailTrace_5891055
  have hstable : (prefixWord ++ tailWord_5891055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891055).length < 2 ^ (prefixWord ++ tailWord_5891055).sum := by decide
  have hdescent : baseEnd_5891055 < baseStart_5891055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891086 : List Nat := [4, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3]
def baseStart_5891086 : Nat := 118140960795 + 5891086 * 2 ^ 59
def prefixEnd_5891086 : Nat := 4983230072969 + 3 ^ 40 * 5891086 * 2
def baseEnd_5891086 : Nat := 3024958694972843332632395

theorem tailTrace_5891086 : CollatzResearch.WordTrace tailWord_5891086 prefixEnd_5891086 3024958694972843332632395 := by
  unfold tailWord_5891086
  simp only [CollatzResearch.WordTrace]
  refine ⟨26858194791951126779101639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143243705557072676155208741 26858194791951126779101639)
  ·
    refine ⟨40287292187926690168652459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26858194791951126779101639 40287292187926690168652459)
    ·
      refine ⟨60430938281890035252978689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40287292187926690168652459 60430938281890035252978689)
      ·
        refine ⟨45323203711417526439734017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60430938281890035252978689 45323203711417526439734017)
        ·
          refine ⟨33992402783563144829800513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45323203711417526439734017 33992402783563144829800513)
          ·
            refine ⟨25494302087672358622350385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33992402783563144829800513 25494302087672358622350385)
            ·
              refine ⟨19120726565754268966762789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25494302087672358622350385 19120726565754268966762789)
              ·
                refine ⟨3585136231078925431268023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19120726565754268966762789 3585136231078925431268023)
                ·
                  refine ⟨5377704346618388146902035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585136231078925431268023 5377704346618388146902035)
                  ·
                    refine ⟨8066556519927582220353053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5377704346618388146902035 8066556519927582220353053)
                    ·
                      refine ⟨3024958694972843332632395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8066556519927582220353053 3024958694972843332632395)
                      ·
                        rfl

theorem cell23_5891086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_5891086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891086 prefixEnd_5891086 := by exact prefixLift 5891086
  have htrace : WordTrace (prefixWord ++ tailWord_5891086) baseStart_5891086 baseEnd_5891086 := by
    simpa [prefixWord, tailWord_5891086, baseEnd_5891086] using wordTrace_append hprefix tailTrace_5891086
  have hstable : (prefixWord ++ tailWord_5891086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891086).length < 2 ^ (prefixWord ++ tailWord_5891086).sum := by decide
  have hdescent : baseEnd_5891086 < baseStart_5891086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891109 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 3, 2, 2]
def baseStart_5891109 : Nat := 118140960795 + 5891109 * 2 ^ 59
def prefixEnd_5891109 : Nat := 4983230072969 + 3 ^ 40 * 5891109 * 2
def baseEnd_5891109 : Nat := 3024970505027896742644789

theorem tailTrace_5891109 : CollatzResearch.WordTrace tailWord_5891109 prefixEnd_5891109 3024970505027896742644789 := by
  unfold tailWord_5891109
  simp only [CollatzResearch.WordTrace]
  refine ⟨214866397214525689160900381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143244264809683792773933587 214866397214525689160900381)
  ·
    refine ⟨80574898955447133435337643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214866397214525689160900381 80574898955447133435337643)
    ·
      refine ⟨120862348433170700153006465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80574898955447133435337643 120862348433170700153006465)
      ·
        refine ⟨90646761324878025114754849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120862348433170700153006465 90646761324878025114754849)
        ·
          refine ⟨67985070993658518836066137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90646761324878025114754849 67985070993658518836066137)
          ·
            refine ⟨50988803245243889127049603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67985070993658518836066137 50988803245243889127049603)
            ·
              refine ⟨76483204867865833690574405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50988803245243889127049603 76483204867865833690574405)
              ·
                refine ⟨14340600912724843816982701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76483204867865833690574405 14340600912724843816982701)
                ·
                  refine ⟨5377725342271816431368513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14340600912724843816982701 5377725342271816431368513)
                  ·
                    refine ⟨4033294006703862323526385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5377725342271816431368513 4033294006703862323526385)
                    ·
                      refine ⟨3024970505027896742644789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4033294006703862323526385 3024970505027896742644789)
                      ·
                        rfl

theorem cell23_5891109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_5891109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891109 prefixEnd_5891109 := by exact prefixLift 5891109
  have htrace : WordTrace (prefixWord ++ tailWord_5891109) baseStart_5891109 baseEnd_5891109 := by
    simpa [prefixWord, tailWord_5891109, baseEnd_5891109] using wordTrace_append hprefix tailTrace_5891109
  have hstable : (prefixWord ++ tailWord_5891109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891109).length < 2 ^ (prefixWord ++ tailWord_5891109).sum := by decide
  have hdescent : baseEnd_5891109 < baseStart_5891109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891129 : List Nat := [1, 2, 1, 5, 2, 1, 2, 3, 1, 2, 3]
def baseStart_5891129 : Nat := 118140960795 + 5891129 * 2 ^ 59
def prefixEnd_5891129 : Nat := 4983230072969 + 3 ^ 40 * 5891129 * 2
def baseEnd_5891129 : Nat := 3024980774640986664394697

theorem tailTrace_5891129 : CollatzResearch.WordTrace tailWord_5891129 prefixEnd_5891129 3024980774640986664394697 := by
  unfold tailWord_5891129
  simp only [CollatzResearch.WordTrace]
  refine ⟨214867126674453232576628441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143244751116302155051085627 214867126674453232576628441)
  ·
    refine ⟨161150345005839924432471331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214867126674453232576628441 161150345005839924432471331)
    ·
      refine ⟨241725517508759886648706997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161150345005839924432471331 241725517508759886648706997)
      ·
        refine ⟨22661767266446239373316281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241725517508759886648706997 22661767266446239373316281)
        ·
          refine ⟨16996325449834679529987211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22661767266446239373316281 16996325449834679529987211)
          ·
            refine ⟨25494488174752019294980817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16996325449834679529987211 25494488174752019294980817)
            ·
              refine ⟨19120866131064014471235613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25494488174752019294980817 19120866131064014471235613)
              ·
                refine ⟨7170324799149005426713355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19120866131064014471235613 7170324799149005426713355)
                ·
                  refine ⟨10755487198723508140070033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7170324799149005426713355 10755487198723508140070033)
                  ·
                    refine ⟨8066615399042631105052525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10755487198723508140070033 8066615399042631105052525)
                    ·
                      refine ⟨3024980774640986664394697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8066615399042631105052525 3024980774640986664394697)
                      ·
                        rfl

theorem cell23_5891129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_5891129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891129 prefixEnd_5891129 := by exact prefixLift 5891129
  have htrace : WordTrace (prefixWord ++ tailWord_5891129) baseStart_5891129 baseEnd_5891129 := by
    simpa [prefixWord, tailWord_5891129, baseEnd_5891129] using wordTrace_append hprefix tailTrace_5891129
  have hstable : (prefixWord ++ tailWord_5891129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891129).length < 2 ^ (prefixWord ++ tailWord_5891129).sum := by decide
  have hdescent : baseEnd_5891129 < baseStart_5891129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891176 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5891176 : Nat := 118140960795 + 5891176 * 2 ^ 59
def prefixEnd_5891176 : Nat := 4983230072969 + 3 ^ 40 * 5891176 * 2
def baseEnd_5891176 : Nat := 3025004908231747980506981

theorem tailTrace_5891176 : CollatzResearch.WordTrace tailWord_5891176 prefixEnd_5891176 3025004908231747980506981 := by
  unfold tailWord_5891176
  simp only [CollatzResearch.WordTrace]
  refine ⟨107434420452641479801794691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143245893936855306402392921 107434420452641479801794691)
  ·
    refine ⟨161151630678962219702692037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107434420452641479801794691 161151630678962219702692037)
    ·
      refine ⟨30215930752305416194254757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161151630678962219702692037 30215930752305416194254757)
      ·
        refine ⟨5665487016057265536422767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30215930752305416194254757 5665487016057265536422767)
        ·
          refine ⟨8498230524085898304634151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665487016057265536422767 8498230524085898304634151)
          ·
            refine ⟨12747345786128847456951227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8498230524085898304634151 12747345786128847456951227)
            ·
              refine ⟨19121018679193271185426841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12747345786128847456951227 19121018679193271185426841)
              ·
                refine ⟨14340764009394953389070131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19121018679193271185426841 14340764009394953389070131)
                ·
                  refine ⟨21511146014092430083605197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14340764009394953389070131 21511146014092430083605197)
                  ·
                    refine ⟨8066679755284661281351949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21511146014092430083605197 8066679755284661281351949)
                    ·
                      refine ⟨3025004908231747980506981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8066679755284661281351949 3025004908231747980506981)
                      ·
                        rfl

theorem cell23_5891176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5891176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891176 prefixEnd_5891176 := by exact prefixLift 5891176
  have htrace : WordTrace (prefixWord ++ tailWord_5891176) baseStart_5891176 baseEnd_5891176 := by
    simpa [prefixWord, tailWord_5891176, baseEnd_5891176] using wordTrace_append hprefix tailTrace_5891176
  have hstable : (prefixWord ++ tailWord_5891176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891176).length < 2 ^ (prefixWord ++ tailWord_5891176).sum := by decide
  have hdescent : baseEnd_5891176 < baseStart_5891176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891185 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_5891185 : Nat := 118140960795 + 5891185 * 2 ^ 59
def prefixEnd_5891185 : Nat := 4983230072969 + 3 ^ 40 * 5891185 * 2
def baseEnd_5891185 : Nat := 3025009529557638445294439

theorem tailTrace_5891185 : CollatzResearch.WordTrace tailWord_5891185 prefixEnd_5891185 3025009529557638445294439 := by
  unfold tailWord_5891185
  simp only [CollatzResearch.WordTrace]
  refine ⟨214869169162250354140667009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143246112774833569427111339 214869169162250354140667009)
  ·
    refine ⟨161151876871687765605500257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214869169162250354140667009 161151876871687765605500257)
    ·
      refine ⟨120863907653765824204125193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161151876871687765605500257 120863907653765824204125193)
      ·
        refine ⟨90647930740324368153093895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120863907653765824204125193 90647930740324368153093895)
        ·
          refine ⟨135971896110486552229640843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90647930740324368153093895 135971896110486552229640843)
          ·
            refine ⟨203957844165729828344461265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135971896110486552229640843 203957844165729828344461265)
            ·
              refine ⟨152968383124297371258345949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203957844165729828344461265 152968383124297371258345949)
              ·
                refine ⟨57363143671611514221879731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152968383124297371258345949 57363143671611514221879731)
                ·
                  refine ⟨86044715507417271332819597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57363143671611514221879731 86044715507417271332819597)
                  ·
                    refine ⟨32266768315281476749807349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86044715507417271332819597 32266768315281476749807349)
                    ·
                      refine ⟨3025009529557638445294439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32266768315281476749807349 3025009529557638445294439)
                      ·
                        rfl

theorem cell23_5891185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_5891185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891185 prefixEnd_5891185 := by exact prefixLift 5891185
  have htrace : WordTrace (prefixWord ++ tailWord_5891185) baseStart_5891185 baseEnd_5891185 := by
    simpa [prefixWord, tailWord_5891185, baseEnd_5891185] using wordTrace_append hprefix tailTrace_5891185
  have hstable : (prefixWord ++ tailWord_5891185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891185).length < 2 ^ (prefixWord ++ tailWord_5891185).sum := by decide
  have hdescent : baseEnd_5891185 < baseStart_5891185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891195 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 4]
def baseStart_5891195 : Nat := 118140960795 + 5891195 * 2 ^ 59
def prefixEnd_5891195 : Nat := 4983230072969 + 3 ^ 40 * 5891195 * 2
def baseEnd_5891195 : Nat := 3025014664364183406169393

theorem tailTrace_5891195 : CollatzResearch.WordTrace tailWord_5891195 prefixEnd_5891195 3025014664364183406169393 := by
  unfold tailWord_5891195
  simp only [CollatzResearch.WordTrace]
  refine ⟨214869533892214125848531039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143246355928142750565687359 214869533892214125848531039)
  ·
    refine ⟨322304300838321188772796559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214869533892214125848531039 322304300838321188772796559)
    ·
      refine ⟨483456451257481783159194839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322304300838321188772796559 483456451257481783159194839)
      ·
        refine ⟨725184676886222674738792259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483456451257481783159194839 725184676886222674738792259)
        ·
          refine ⟨1087777015329334012108188389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725184676886222674738792259 1087777015329334012108188389)
          ·
            refine ⟨203958190374250127270285323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1087777015329334012108188389 203958190374250127270285323)
            ·
              refine ⟨305937285561375190905427985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203958190374250127270285323 305937285561375190905427985)
              ·
                refine ⟨229452964171031393179070989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305937285561375190905427985 229452964171031393179070989)
                ·
                  refine ⟨86044861564136772442151621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229452964171031393179070989 86044861564136772442151621)
                  ·
                    refine ⟨16133411543275644832903429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86044861564136772442151621 16133411543275644832903429)
                    ·
                      refine ⟨3025014664364183406169393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16133411543275644832903429 3025014664364183406169393)
                      ·
                        rfl

theorem cell23_5891195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 4].length) (baseStart_5891195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891195 prefixEnd_5891195 := by exact prefixLift 5891195
  have htrace : WordTrace (prefixWord ++ tailWord_5891195) baseStart_5891195 baseEnd_5891195 := by
    simpa [prefixWord, tailWord_5891195, baseEnd_5891195] using wordTrace_append hprefix tailTrace_5891195
  have hstable : (prefixWord ++ tailWord_5891195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891195).length < 2 ^ (prefixWord ++ tailWord_5891195).sum := by decide
  have hdescent : baseEnd_5891195 < baseStart_5891195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891232 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 3]
def baseStart_5891232 : Nat := 118140960795 + 5891232 * 2 ^ 59
def prefixEnd_5891232 : Nat := 4983230072969 + 3 ^ 40 * 5891232 * 2
def baseEnd_5891232 : Nat := 3025033663148399761406723

theorem tailTrace_5891232 : CollatzResearch.WordTrace tailWord_5891232 prefixEnd_5891232 3025033663148399761406723 := by
  unfold tailWord_5891232
  simp only [CollatzResearch.WordTrace]
  refine ⟨107435441696540040583813975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143247255595386720778418633 107435441696540040583813975)
  ·
    refine ⟨161153162544810060875720963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107435441696540040583813975 161153162544810060875720963)
    ·
      refine ⟨241729743817215091313581445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161153162544810060875720963 241729743817215091313581445)
      ·
        refine ⟨45324326965727829621296521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241729743817215091313581445 45324326965727829621296521)
        ·
          refine ⟨33993245224295872215972391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45324326965727829621296521 33993245224295872215972391)
          ·
            refine ⟨50989867836443808323958587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33993245224295872215972391 50989867836443808323958587)
            ·
              refine ⟨76484801754665712485937881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50989867836443808323958587 76484801754665712485937881)
              ·
                refine ⟨57363601315999284364453411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76484801754665712485937881 57363601315999284364453411)
                ·
                  refine ⟨86045401973998926546680117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57363601315999284364453411 86045401973998926546680117)
                  ·
                    refine ⟨8066756435062399363751261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86045401973998926546680117 8066756435062399363751261)
                    ·
                      refine ⟨3025033663148399761406723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8066756435062399363751261 3025033663148399761406723)
                      ·
                        rfl

theorem cell23_5891232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_5891232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891232 prefixEnd_5891232 := by exact prefixLift 5891232
  have htrace : WordTrace (prefixWord ++ tailWord_5891232) baseStart_5891232 baseEnd_5891232 := by
    simpa [prefixWord, tailWord_5891232, baseEnd_5891232] using wordTrace_append hprefix tailTrace_5891232
  have hstable : (prefixWord ++ tailWord_5891232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891232).length < 2 ^ (prefixWord ++ tailWord_5891232).sum := by decide
  have hdescent : baseEnd_5891232 < baseStart_5891232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891249 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 2, 3, 3]
def baseStart_5891249 : Nat := 118140960795 + 5891249 * 2 ^ 59
def prefixEnd_5891249 : Nat := 4983230072969 + 3 ^ 40 * 5891249 * 2
def baseEnd_5891249 : Nat := 3025042392319526194894145

theorem tailTrace_5891249 : CollatzResearch.WordTrace tailWord_5891249 prefixEnd_5891249 3025042392319526194894145 := by
  unfold tailWord_5891249
  simp only [CollatzResearch.WordTrace]
  refine ⟨214871503434018493070996801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143247668956012328713997867 214871503434018493070996801)
  ·
    refine ⟨161153627575513869803247601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214871503434018493070996801 161153627575513869803247601)
    ·
      refine ⟨120865220681635402352435701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161153627575513869803247601 120865220681635402352435701)
      ·
        refine ⟨11331114438903318970540847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120865220681635402352435701 11331114438903318970540847)
        ·
          refine ⟨16996671658354978455811271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11331114438903318970540847 16996671658354978455811271)
          ·
            refine ⟨25495007487532467683716907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16996671658354978455811271 25495007487532467683716907)
            ·
              refine ⟨38242511231298701525575361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25495007487532467683716907 38242511231298701525575361)
              ·
                refine ⟨28681883423474026144181521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38242511231298701525575361 28681883423474026144181521)
                ·
                  refine ⟨21511412567605519608136141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28681883423474026144181521 21511412567605519608136141)
                  ·
                    refine ⟨8066779712852069853051053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21511412567605519608136141 8066779712852069853051053)
                    ·
                      refine ⟨3025042392319526194894145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8066779712852069853051053 3025042392319526194894145)
                      ·
                        rfl

theorem cell23_5891249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_5891249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891249 prefixEnd_5891249 := by exact prefixLift 5891249
  have htrace : WordTrace (prefixWord ++ tailWord_5891249) baseStart_5891249 baseEnd_5891249 := by
    simpa [prefixWord, tailWord_5891249, baseEnd_5891249] using wordTrace_append hprefix tailTrace_5891249
  have hstable : (prefixWord ++ tailWord_5891249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891249).length < 2 ^ (prefixWord ++ tailWord_5891249).sum := by decide
  have hdescent : baseEnd_5891249 < baseStart_5891249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891272 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_5891272 : Nat := 118140960795 + 5891272 * 2 ^ 59
def prefixEnd_5891272 : Nat := 4983230072969 + 3 ^ 40 * 5891272 * 2
def baseEnd_5891272 : Nat := 3025054202374579604906539

theorem tailTrace_5891272 : CollatzResearch.WordTrace tailWord_5891272 prefixEnd_5891272 3025054202374579604906539 := by
  unfold tailWord_5891272
  simp only [CollatzResearch.WordTrace]
  refine ⟨107436171156467583999542035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143248228208623445332722713 107436171156467583999542035)
  ·
    refine ⟨161154256734701375999313053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107436171156467583999542035 161154256734701375999313053)
    ·
      refine ⟨60432846275513015999742395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161154256734701375999313053 60432846275513015999742395)
      ·
        refine ⟨90649269413269523999613593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60432846275513015999742395 90649269413269523999613593)
        ·
          refine ⟨67986952059952142999710195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90649269413269523999613593 67986952059952142999710195)
          ·
            refine ⟨101980428089928214499565293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67986952059952142999710195 101980428089928214499565293)
            ·
              refine ⟨38242660533723080437336985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101980428089928214499565293 38242660533723080437336985)
              ·
                refine ⟨28681995400292310328002739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38242660533723080437336985 28681995400292310328002739)
                ·
                  refine ⟨43022993100438465492004109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28681995400292310328002739 43022993100438465492004109)
                  ·
                    refine ⟨16133622412664424559501541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43022993100438465492004109 16133622412664424559501541)
                    ·
                      refine ⟨3025054202374579604906539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16133622412664424559501541 3025054202374579604906539)
                      ·
                        rfl

theorem cell23_5891272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_5891272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891272 prefixEnd_5891272 := by exact prefixLift 5891272
  have htrace : WordTrace (prefixWord ++ tailWord_5891272) baseStart_5891272 baseEnd_5891272 := by
    simpa [prefixWord, tailWord_5891272, baseEnd_5891272] using wordTrace_append hprefix tailTrace_5891272
  have hstable : (prefixWord ++ tailWord_5891272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891272).length < 2 ^ (prefixWord ++ tailWord_5891272).sum := by decide
  have hdescent : baseEnd_5891272 < baseStart_5891272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891282 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_5891282 : Nat := 118140960795 + 5891282 * 2 ^ 59
def prefixEnd_5891282 : Nat := 4983230072969 + 3 ^ 40 * 5891282 * 2
def baseEnd_5891282 : Nat := 1008353112393708188593831

theorem tailTrace_5891282 : CollatzResearch.WordTrace tailWord_5891282 prefixEnd_5891282 1008353112393708188593831 := by
  unfold tailWord_5891282
  simp only [CollatzResearch.WordTrace]
  refine ⟨53718176760724734926737025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143248471361932626471298733 53718176760724734926737025)
  ·
    refine ⟨40288632570543551195052769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53718176760724734926737025 40288632570543551195052769)
    ·
      refine ⟨30216474427907663396289577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40288632570543551195052769 30216474427907663396289577)
      ·
        refine ⟨22662355820930747547217183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30216474427907663396289577 22662355820930747547217183)
        ·
          refine ⟨33993533731396121320825775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22662355820930747547217183 33993533731396121320825775)
          ·
            refine ⟨50990300597094181981238663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33993533731396121320825775 50990300597094181981238663)
            ·
              refine ⟨76485450895641272971857995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50990300597094181981238663 76485450895641272971857995)
              ·
                refine ⟨114728176343461909457786993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76485450895641272971857995 114728176343461909457786993)
                ·
                  refine ⟨86046132257596432093340245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114728176343461909457786993 86046132257596432093340245)
                  ·
                    refine ⟨1008353112393708188593831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86046132257596432093340245 1008353112393708188593831)
                    ·
                      rfl

theorem cell23_5891282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_5891282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891282 prefixEnd_5891282 := by exact prefixLift 5891282
  have htrace : WordTrace (prefixWord ++ tailWord_5891282) baseStart_5891282 baseEnd_5891282 := by
    simpa [prefixWord, tailWord_5891282, baseEnd_5891282] using wordTrace_append hprefix tailTrace_5891282
  have hstable : (prefixWord ++ tailWord_5891282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891282).length < 2 ^ (prefixWord ++ tailWord_5891282).sum := by decide
  have hdescent : baseEnd_5891282 < baseStart_5891282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891329 : List Nat := [1, 2, 4, 1, 1, 4, 1, 3, 6]
def baseStart_5891329 : Nat := 118140960795 + 5891329 * 2 ^ 59
def prefixEnd_5891329 : Nat := 4983230072969 + 3 ^ 40 * 5891329 * 2
def baseEnd_5891329 : Nat := 336120385641320653543753

theorem tailTrace_5891329 : CollatzResearch.WordTrace tailWord_5891329 prefixEnd_5891329 336120385641320653543753 := by
  unfold tailWord_5891329
  simp only [CollatzResearch.WordTrace]
  refine ⟨214874421273728666733909041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143249614182485777822606027 214874421273728666733909041)
  ·
    refine ⟨161155815955296500050431781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214874421273728666733909041 161155815955296500050431781)
    ·
      refine ⟨30216715491618093759455959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161155815955296500050431781 30216715491618093759455959)
      ·
        refine ⟨45325073237427140639183939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30216715491618093759455959 45325073237427140639183939)
        ·
          refine ⟨67987609856140710958775909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45325073237427140639183939 67987609856140710958775909)
          ·
            refine ⟨12747676848026383304770483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67987609856140710958775909 12747676848026383304770483)
            ·
              refine ⟨19121515272039574957155725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12747676848026383304770483 19121515272039574957155725)
              ·
                refine ⟨7170568227014840608933397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19121515272039574957155725 7170568227014840608933397)
                ·
                  refine ⟨336120385641320653543753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7170568227014840608933397 336120385641320653543753)
                  ·
                    rfl

theorem cell23_5891329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 6].length) (baseStart_5891329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891329 prefixEnd_5891329 := by exact prefixLift 5891329
  have htrace : WordTrace (prefixWord ++ tailWord_5891329) baseStart_5891329 baseEnd_5891329 := by
    simpa [prefixWord, tailWord_5891329, baseEnd_5891329] using wordTrace_append hprefix tailTrace_5891329
  have hstable : (prefixWord ++ tailWord_5891329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891329).length < 2 ^ (prefixWord ++ tailWord_5891329).sum := by decide
  have hdescent : baseEnd_5891329 < baseStart_5891329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891372 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 5, 6]
def baseStart_5891372 : Nat := 118140960795 + 5891372 * 2 ^ 59
def prefixEnd_5891372 : Nat := 4983230072969 + 3 ^ 40 * 5891372 * 2
def baseEnd_5891372 : Nat := 1008368516813343071218693

theorem tailTrace_5891372 : CollatzResearch.WordTrace tailWord_5891372 prefixEnd_5891372 1008368516813343071218693 := by
  unfold tailWord_5891372
  simp only [CollatzResearch.WordTrace]
  refine ⟨107437994806286442538862185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143250659741715256718482913 107437994806286442538862185)
  ·
    refine ⟨80578496104714831904146639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107437994806286442538862185 80578496104714831904146639)
    ·
      refine ⟨120867744157072247856219959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80578496104714831904146639 120867744157072247856219959)
      ·
        refine ⟨181301616235608371784329939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120867744157072247856219959 181301616235608371784329939)
        ·
          refine ⟨271952424353412557676494909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181301616235608371784329939 271952424353412557676494909)
          ·
            refine ⟨101982159132529709128685591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271952424353412557676494909 101982159132529709128685591)
            ·
              refine ⟨152973238698794563693028387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101982159132529709128685591 152973238698794563693028387)
              ·
                refine ⟨229459858048191845539542581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152973238698794563693028387 229459858048191845539542581)
                ·
                  refine ⟨21511861692017985519332117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229459858048191845539542581 21511861692017985519332117)
                  ·
                    refine ⟨1008368516813343071218693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21511861692017985519332117 1008368516813343071218693)
                    ·
                      rfl

theorem cell23_5891372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_5891372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891372 prefixEnd_5891372 := by exact prefixLift 5891372
  have htrace : WordTrace (prefixWord ++ tailWord_5891372) baseStart_5891372 baseEnd_5891372 := by
    simpa [prefixWord, tailWord_5891372, baseEnd_5891372] using wordTrace_append hprefix tailTrace_5891372
  have hstable : (prefixWord ++ tailWord_5891372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891372).length < 2 ^ (prefixWord ++ tailWord_5891372).sum := by decide
  have hdescent : baseEnd_5891372 < baseStart_5891372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891379 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 4]
def baseStart_5891379 : Nat := 118140960795 + 5891379 * 2 ^ 59
def prefixEnd_5891379 : Nat := 4983230072969 + 3 ^ 40 * 5891379 * 2
def baseEnd_5891379 : Nat := 3025109144804610686268547

theorem tailTrace_5891379 : CollatzResearch.WordTrace tailWord_5891379 prefixEnd_5891379 3025109144804610686268547 := by
  unfold tailWord_5891379
  simp only [CollatzResearch.WordTrace]
  refine ⟨214876244923547525273229191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143250829949031683515486127 214876244923547525273229191)
  ·
    refine ⟨322314367385321287909843787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214876244923547525273229191 322314367385321287909843787)
    ·
      refine ⟨483471551077981931864765681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322314367385321287909843787 483471551077981931864765681)
      ·
        refine ⟨362603663308486448898574261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483471551077981931864765681 362603663308486448898574261)
        ·
          refine ⟨33994093435170604584241337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 362603663308486448898574261 33994093435170604584241337)
          ·
            refine ⟨25495570076377953438181003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33994093435170604584241337 25495570076377953438181003)
            ·
              refine ⟨38243355114566930157271505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25495570076377953438181003 38243355114566930157271505)
              ·
                refine ⟨28682516335925197617953629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38243355114566930157271505 28682516335925197617953629)
                ·
                  refine ⟨10755943625971949106732611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28682516335925197617953629 10755943625971949106732611)
                  ·
                    refine ⟨16133915438957923660098917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10755943625971949106732611 16133915438957923660098917)
                    ·
                      refine ⟨3025109144804610686268547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16133915438957923660098917 3025109144804610686268547)
                      ·
                        rfl

theorem cell23_5891379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_5891379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891379 prefixEnd_5891379 := by exact prefixLift 5891379
  have htrace : WordTrace (prefixWord ++ tailWord_5891379) baseStart_5891379 baseEnd_5891379 := by
    simpa [prefixWord, tailWord_5891379, baseEnd_5891379] using wordTrace_append hprefix tailTrace_5891379
  have hstable : (prefixWord ++ tailWord_5891379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891379).length < 2 ^ (prefixWord ++ tailWord_5891379).sum := by decide
  have hdescent : baseEnd_5891379 < baseStart_5891379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891402 : List Nat := [3, 1, 2, 1, 1, 1, 1, 13]
def baseStart_5891402 : Nat := 118140960795 + 5891402 * 2 ^ 59
def prefixEnd_5891402 : Nat := 4983230072969 + 3 ^ 40 * 5891402 * 2
def baseEnd_5891402 : Nat := 112041516846654225788183

theorem tailTrace_5891402 : CollatzResearch.WordTrace tailWord_5891402 prefixEnd_5891402 112041516846654225788183 := by
  unfold tailWord_5891402
  simp only [CollatzResearch.WordTrace]
  refine ⟨53719270950616050050329115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143251389201642800134210973 53719270950616050050329115)
  ·
    refine ⟨80578906425924075075493673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53719270950616050050329115 80578906425924075075493673)
    ·
      refine ⟨60434179819443056306620255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80578906425924075075493673 60434179819443056306620255)
      ·
        refine ⟨90651269729164584459930383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60434179819443056306620255 90651269729164584459930383)
        ·
          refine ⟨135976904593746876689895575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90651269729164584459930383 135976904593746876689895575)
          ·
            refine ⟨203965356890620315034843363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135976904593746876689895575 203965356890620315034843363)
            ·
              refine ⟨305948035335930472552265045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203965356890620315034843363 305948035335930472552265045)
              ·
                refine ⟨112041516846654225788183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 305948035335930472552265045 112041516846654225788183)
                ·
                  rfl

theorem cell23_5891402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 13].length) (baseStart_5891402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891402 prefixEnd_5891402 := by exact prefixLift 5891402
  have htrace : WordTrace (prefixWord ++ tailWord_5891402) baseStart_5891402 baseEnd_5891402 := by
    simpa [prefixWord, tailWord_5891402, baseEnd_5891402] using wordTrace_append hprefix tailTrace_5891402
  have hstable : (prefixWord ++ tailWord_5891402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891402).length < 2 ^ (prefixWord ++ tailWord_5891402).sum := by decide
  have hdescent : baseEnd_5891402 < baseStart_5891402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891409 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_5891409 : Nat := 118140960795 + 5891409 * 2 ^ 59
def prefixEnd_5891409 : Nat := 4983230072969 + 3 ^ 40 * 5891409 * 2
def baseEnd_5891409 : Nat := 3025124549224245568893409

theorem tailTrace_5891409 : CollatzResearch.WordTrace tailWord_5891409 prefixEnd_5891409 3025124549224245568893409 := by
  unfold tailWord_5891409
  simp only [CollatzResearch.WordTrace]
  refine ⟨214877339113438840396821281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143251559408959226931214187 214877339113438840396821281)
  ·
    refine ⟨161158004335079130297615961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214877339113438840396821281 161158004335079130297615961)
    ·
      refine ⟨120868503251309347723211971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161158004335079130297615961 120868503251309347723211971)
      ·
        refine ⟨181302754876964021584817957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120868503251309347723211971 181302754876964021584817957)
        ·
          refine ⟨33994266539430754047153367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181302754876964021584817957 33994266539430754047153367)
          ·
            refine ⟨50991399809146131070730051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33994266539430754047153367 50991399809146131070730051)
            ·
              refine ⟨76487099713719196606095077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50991399809146131070730051 76487099713719196606095077)
              ·
                refine ⟨14341331196322349363642827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76487099713719196606095077 14341331196322349363642827)
                ·
                  refine ⟨21511996794483524045464241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14341331196322349363642827 21511996794483524045464241)
                  ·
                    refine ⟨16133997595862643034098181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21511996794483524045464241 16133997595862643034098181)
                    ·
                      refine ⟨3025124549224245568893409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16133997595862643034098181 3025124549224245568893409)
                      ·
                        rfl

theorem cell23_5891409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_5891409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891409 prefixEnd_5891409 := by exact prefixLift 5891409
  have htrace : WordTrace (prefixWord ++ tailWord_5891409) baseStart_5891409 baseEnd_5891409 := by
    simpa [prefixWord, tailWord_5891409, baseEnd_5891409] using wordTrace_append hprefix tailTrace_5891409
  have hstable : (prefixWord ++ tailWord_5891409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891409).length < 2 ^ (prefixWord ++ tailWord_5891409).sum := by decide
  have hdescent : baseEnd_5891409 < baseStart_5891409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891413 : List Nat := [1, 3, 2, 2, 3, 1, 4, 1, 1, 1, 4]
def baseStart_5891413 : Nat := 118140960795 + 5891413 * 2 ^ 59
def prefixEnd_5891413 : Nat := 4983230072969 + 3 ^ 40 * 5891413 * 2
def baseEnd_5891413 : Nat := 3025126603146863553243391

theorem tailTrace_5891413 : CollatzResearch.WordTrace tailWord_5891413 prefixEnd_5891413 3025126603146863553243391 := by
  unfold tailWord_5891413
  simp only [CollatzResearch.WordTrace]
  refine ⟨214877485005424349079966893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143251656670282899386644595 214877485005424349079966893)
  ·
    refine ⟨80579056877034130904987585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214877485005424349079966893 80579056877034130904987585)
    ·
      refine ⟨60434292657775598178740689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80579056877034130904987585 60434292657775598178740689)
      ·
        refine ⟨45325719493331698634055517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60434292657775598178740689 45325719493331698634055517)
        ·
          refine ⟨16997144809999386987770819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45325719493331698634055517 16997144809999386987770819)
          ·
            refine ⟨25495717214999080481656229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16997144809999386987770819 25495717214999080481656229)
            ·
              refine ⟨4780446977812327590310543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25495717214999080481656229 4780446977812327590310543)
              ·
                refine ⟨7170670466718491385465815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4780446977812327590310543 7170670466718491385465815)
                ·
                  refine ⟨10756005700077737078198723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7170670466718491385465815 10756005700077737078198723)
                  ·
                    refine ⟨16134008550116605617298085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10756005700077737078198723 16134008550116605617298085)
                    ·
                      refine ⟨3025126603146863553243391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16134008550116605617298085 3025126603146863553243391)
                      ·
                        rfl

theorem cell23_5891413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_5891413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891413 prefixEnd_5891413 := by exact prefixLift 5891413
  have htrace : WordTrace (prefixWord ++ tailWord_5891413) baseStart_5891413 baseEnd_5891413 := by
    simpa [prefixWord, tailWord_5891413, baseEnd_5891413] using wordTrace_append hprefix tailTrace_5891413
  have hstable : (prefixWord ++ tailWord_5891413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891413).length < 2 ^ (prefixWord ++ tailWord_5891413).sum := by decide
  have hdescent : baseEnd_5891413 < baseStart_5891413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891414 : List Nat := [5, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_5891414 : Nat := 118140960795 + 5891414 * 2 ^ 59
def prefixEnd_5891414 : Nat := 4983230072969 + 3 ^ 40 * 5891414 * 2
def baseEnd_5891414 : Nat := 336125235180835338814543

theorem tailTrace_5891414 : CollatzResearch.WordTrace tailWord_5891414 prefixEnd_5891414 336125235180835338814543 := by
  unfold tailWord_5891414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13429845092401295390672081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143251680985613817500502197 13429845092401295390672081)
  ·
    refine ⟨10072383819300971543004061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13429845092401295390672081 10072383819300971543004061)
    ·
      refine ⟨3777143932237864328626523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10072383819300971543004061 3777143932237864328626523)
      ·
        refine ⟨5665715898356796492939785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3777143932237864328626523 5665715898356796492939785)
        ·
          refine ⟨4249286923767597369704839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5665715898356796492939785 4249286923767597369704839)
          ·
            refine ⟨6373930385651396054557259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4249286923767597369704839 6373930385651396054557259)
            ·
              refine ⟨9560895578477094081835889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6373930385651396054557259 9560895578477094081835889)
              ·
                refine ⟨7170671683857820561376917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9560895578477094081835889 7170671683857820561376917)
                ·
                  refine ⟨336125235180835338814543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7170671683857820561376917 336125235180835338814543)
                  ·
                    rfl

theorem cell23_5891414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_5891414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891414 prefixEnd_5891414 := by exact prefixLift 5891414
  have htrace : WordTrace (prefixWord ++ tailWord_5891414) baseStart_5891414 baseEnd_5891414 := by
    simpa [prefixWord, tailWord_5891414, baseEnd_5891414] using wordTrace_append hprefix tailTrace_5891414
  have hstable : (prefixWord ++ tailWord_5891414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891414).length < 2 ^ (prefixWord ++ tailWord_5891414).sum := by decide
  have hdescent : baseEnd_5891414 < baseStart_5891414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891416 : List Nat := [2, 1, 2, 2, 1, 1, 5, 3, 1, 2, 3]
def baseStart_5891416 : Nat := 118140960795 + 5891416 * 2 ^ 59
def prefixEnd_5891416 : Nat := 4983230072969 + 3 ^ 40 * 5891416 * 2
def baseEnd_5891416 : Nat := 3025128143588827041505877

theorem tailTrace_5891416 : CollatzResearch.WordTrace tailWord_5891416 prefixEnd_5891416 3025128143588827041505877 := by
  unfold tailWord_5891416
  simp only [CollatzResearch.WordTrace]
  refine ⟨107438797212206740296163051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143251729616275653728217401 107438797212206740296163051)
  ·
    refine ⟨161158195818310110444244577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107438797212206740296163051 161158195818310110444244577)
    ·
      refine ⟨120868646863732582833183433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161158195818310110444244577 120868646863732582833183433)
      ·
        refine ⟨90651485147799437124887575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120868646863732582833183433 90651485147799437124887575)
        ·
          refine ⟨135977227721699155687331363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90651485147799437124887575 135977227721699155687331363)
          ·
            refine ⟨203965841582548733530997045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135977227721699155687331363 203965841582548733530997045)
            ·
              refine ⟨19121797648363943768530973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203965841582548733530997045 19121797648363943768530973)
              ·
                refine ⟨7170674118136478913199115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19121797648363943768530973 7170674118136478913199115)
                ·
                  refine ⟨10756011177204718369798673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7170674118136478913199115 10756011177204718369798673)
                  ·
                    refine ⟨8067008382903538777349005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10756011177204718369798673 8067008382903538777349005)
                    ·
                      refine ⟨3025128143588827041505877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8067008382903538777349005 3025128143588827041505877)
                      ·
                        rfl

theorem cell23_5891416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_5891416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891416 prefixEnd_5891416 := by exact prefixLift 5891416
  have htrace : WordTrace (prefixWord ++ tailWord_5891416) baseStart_5891416 baseEnd_5891416 := by
    simpa [prefixWord, tailWord_5891416, baseEnd_5891416] using wordTrace_append hprefix tailTrace_5891416
  have hstable : (prefixWord ++ tailWord_5891416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891416).length < 2 ^ (prefixWord ++ tailWord_5891416).sum := by decide
  have hdescent : baseEnd_5891416 < baseStart_5891416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891456 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 3, 3, 2]
def baseStart_5891456 : Nat := 118140960795 + 5891456 * 2 ^ 59
def prefixEnd_5891456 : Nat := 4983230072969 + 3 ^ 40 * 5891456 * 2
def baseEnd_5891456 : Nat := 3025148682815006885005693

theorem tailTrace_5891456 : CollatzResearch.WordTrace tailWord_5891456 prefixEnd_5891456 3025148682815006885005693 := by
  unfold tailWord_5891456
  simp only [CollatzResearch.WordTrace]
  refine ⟨107439526672134283711891111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143252702229512378282521481 107439526672134283711891111)
  ·
    refine ⟨161159290008201425567836667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107439526672134283711891111 161159290008201425567836667)
    ·
      refine ⟨241738935012302138351755001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161159290008201425567836667 241738935012302138351755001)
      ·
        refine ⟨181304201259226603763816251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241738935012302138351755001 181304201259226603763816251)
        ·
          refine ⟨271956301888839905645724377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181304201259226603763816251 271956301888839905645724377)
          ·
            refine ⟨203967226416629929234293283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271956301888839905645724377 203967226416629929234293283)
            ·
              refine ⟨305950839624944893851439925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203967226416629929234293283 305950839624944893851439925)
              ·
                refine ⟨28682891214838583798572493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 305950839624944893851439925 28682891214838583798572493)
                ·
                  refine ⟨10756084205564468924464685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28682891214838583798572493 10756084205564468924464685)
                  ·
                    refine ⟨4033531577086675846674257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10756084205564468924464685 4033531577086675846674257)
                    ·
                      refine ⟨3025148682815006885005693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4033531577086675846674257 3025148682815006885005693)
                      ·
                        rfl

theorem cell23_5891456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3, 3, 2].length) (baseStart_5891456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891456 prefixEnd_5891456 := by exact prefixLift 5891456
  have htrace : WordTrace (prefixWord ++ tailWord_5891456) baseStart_5891456 baseEnd_5891456 := by
    simpa [prefixWord, tailWord_5891456, baseEnd_5891456] using wordTrace_append hprefix tailTrace_5891456
  have hstable : (prefixWord ++ tailWord_5891456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891456).length < 2 ^ (prefixWord ++ tailWord_5891456).sum := by decide
  have hdescent : baseEnd_5891456 < baseStart_5891456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5891459 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 5]
def baseStart_5891459 : Nat := 118140960795 + 5891459 * 2 ^ 59
def prefixEnd_5891459 : Nat := 4983230072969 + 3 ^ 40 * 5891459 * 2
def baseEnd_5891459 : Nat := 3025150223256970373268179

theorem tailTrace_5891459 : CollatzResearch.WordTrace tailWord_5891459 prefixEnd_5891459 3025150223256970373268179 := by
  unfold tailWord_5891459
  simp only [CollatzResearch.WordTrace]
  refine ⟨214879162763257698936141431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143252775175505132624094287 214879162763257698936141431)
  ·
    refine ⟨322318744144886548404212147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214879162763257698936141431 322318744144886548404212147)
    ·
      refine ⟨483478116217329822606318221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322318744144886548404212147 483478116217329822606318221)
      ·
        refine ⟨181304293581498683477369333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 483478116217329822606318221 181304293581498683477369333)
        ·
          refine ⟨16997277523265501576003375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181304293581498683477369333 16997277523265501576003375)
          ·
            refine ⟨25495916284898252364005063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16997277523265501576003375 25495916284898252364005063)
            ·
              refine ⟨38243874427347378546007595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25495916284898252364005063 38243874427347378546007595)
              ·
                refine ⟨57365811641021067819011393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38243874427347378546007595 57365811641021067819011393)
                ·
                  refine ⟨43024358730765800864258545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57365811641021067819011393 43024358730765800864258545)
                  ·
                    refine ⟨32268269048074350648193909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43024358730765800864258545 32268269048074350648193909)
                    ·
                      refine ⟨3025150223256970373268179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32268269048074350648193909 3025150223256970373268179)
                      ·
                        rfl

theorem cell23_5891459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_5891459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5891459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5891459 prefixEnd_5891459 := by exact prefixLift 5891459
  have htrace : WordTrace (prefixWord ++ tailWord_5891459) baseStart_5891459 baseEnd_5891459 := by
    simpa [prefixWord, tailWord_5891459, baseEnd_5891459] using wordTrace_append hprefix tailTrace_5891459
  have hstable : (prefixWord ++ tailWord_5891459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5891459).length < 2 ^ (prefixWord ++ tailWord_5891459).sum := by decide
  have hdescent : baseEnd_5891459 < baseStart_5891459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5891459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
