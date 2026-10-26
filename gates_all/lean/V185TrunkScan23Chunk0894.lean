import V185TrunkScan23Chunk0893

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5291399 : List Nat := [1, 1, 4, 2, 2, 2, 3, 3, 5]
def baseStart_5291399 : Nat := 118140960795 + 5291399 * 2 ^ 59
def prefixEnd_5291399 : Nat := 4983230072969 + 3 ^ 40 * 5291399 * 2
def baseEnd_5291399 : Nat := 301892335746672012308645

theorem tailTrace_5291399 : CollatzResearch.WordTrace tailWord_5291399 prefixEnd_5291399 301892335746672012308645 := by
  unfold tailWord_5291399
  simp only [CollatzResearch.WordTrace]
  refine ⟨192993176557172596847157251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128662117704781731231438167 192993176557172596847157251)
  ·
    refine ⟨289489764835758895270735877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192993176557172596847157251 289489764835758895270735877)
    ·
      refine ⟨54279330906704792863262977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289489764835758895270735877 54279330906704792863262977)
      ·
        refine ⟨40709498180028594647447233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54279330906704792863262977 40709498180028594647447233)
        ·
          refine ⟨30532123635021445985585425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40709498180028594647447233 30532123635021445985585425)
          ·
            refine ⟨22899092726266084489189069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30532123635021445985585425 22899092726266084489189069)
            ·
              refine ⟨8587159772349781683445901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22899092726266084489189069 8587159772349781683445901)
              ·
                refine ⟨3220184914631168131292213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8587159772349781683445901 3220184914631168131292213)
                ·
                  refine ⟨301892335746672012308645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3220184914631168131292213 301892335746672012308645)
                  ·
                    rfl

theorem cell23_5291399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 5].length) (baseStart_5291399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291399 prefixEnd_5291399 := by exact prefixLift 5291399
  have htrace : WordTrace (prefixWord ++ tailWord_5291399) baseStart_5291399 baseEnd_5291399 := by
    simpa [prefixWord, tailWord_5291399, baseEnd_5291399] using wordTrace_append hprefix tailTrace_5291399
  have hstable : (prefixWord ++ tailWord_5291399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291399).length < 2 ^ (prefixWord ++ tailWord_5291399).sum := by decide
  have hdescent : baseEnd_5291399 < baseStart_5291399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291416 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 7]
def baseStart_5291416 : Nat := 118140960795 + 5291416 * 2 ^ 59
def prefixEnd_5291416 : Nat := 4983230072969 + 3 ^ 40 * 5291416 * 2
def baseEnd_5291416 : Nat := 301893305654574949362803

theorem tailTrace_5291416 : CollatzResearch.WordTrace tailWord_5291416 prefixEnd_5291416 301893305654574949362803 := by
  unfold tailWord_5291416
  simp only [CollatzResearch.WordTrace]
  refine ⟨96496898299055504375263051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128662531065407339167017401 96496898299055504375263051)
  ·
    refine ⟨144745347448583256562894577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96496898299055504375263051 144745347448583256562894577)
    ·
      refine ⟨108559010586437442422170933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144745347448583256562894577 108559010586437442422170933)
      ·
        refine ⟨10177407242478510227078525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108559010586437442422170933 10177407242478510227078525)
        ·
          refine ⟨3816527715929441335154447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10177407242478510227078525 3816527715929441335154447)
          ·
            refine ⟨5724791573894162002731671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3816527715929441335154447 5724791573894162002731671)
            ·
              refine ⟨8587187360841243004097507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724791573894162002731671 8587187360841243004097507)
              ·
                refine ⟨12880781041261864506146261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8587187360841243004097507 12880781041261864506146261)
                ·
                  refine ⟨301893305654574949362803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12880781041261864506146261 301893305654574949362803)
                  ·
                    rfl

theorem cell23_5291416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 7].length) (baseStart_5291416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291416 prefixEnd_5291416 := by exact prefixLift 5291416
  have htrace : WordTrace (prefixWord ++ tailWord_5291416) baseStart_5291416 baseEnd_5291416 := by
    simpa [prefixWord, tailWord_5291416, baseEnd_5291416] using wordTrace_append hprefix tailTrace_5291416
  have hstable : (prefixWord ++ tailWord_5291416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291416).length < 2 ^ (prefixWord ++ tailWord_5291416).sum := by decide
  have hdescent : baseEnd_5291416 < baseStart_5291416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291455 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 10]
def baseStart_5291455 : Nat := 118140960795 + 5291455 * 2 ^ 59
def prefixEnd_5291455 : Nat := 4983230072969 + 3 ^ 40 * 5291455 * 2
def baseEnd_5291455 : Nat := 301895530737411099075283

theorem tailTrace_5291455 : CollatzResearch.WordTrace tailWord_5291455 prefixEnd_5291455 301895530737411099075283 := by
  unfold tailWord_5291455
  simp only [CollatzResearch.WordTrace]
  refine ⟨192995219044969718411195819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128663479363313145607463879 192995219044969718411195819)
  ·
    refine ⟨289492828567454577616793729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192995219044969718411195819 289492828567454577616793729)
    ·
      refine ⟨217119621425590933212595297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289492828567454577616793729 217119621425590933212595297)
      ·
        refine ⟨162839716069193199909446473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217119621425590933212595297 162839716069193199909446473)
        ·
          refine ⟨122129787051894899932084855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162839716069193199909446473 122129787051894899932084855)
          ·
            refine ⟨183194680577842349898127283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122129787051894899932084855 183194680577842349898127283)
            ·
              refine ⟨274792020866763524847190925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183194680577842349898127283 274792020866763524847190925)
              ·
                refine ⟨103047007825036321817696597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274792020866763524847190925 103047007825036321817696597)
                ·
                  refine ⟨301895530737411099075283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 103047007825036321817696597 301895530737411099075283)
                  ·
                    rfl

theorem cell23_5291455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 10].length) (baseStart_5291455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291455 prefixEnd_5291455 := by exact prefixLift 5291455
  have htrace : WordTrace (prefixWord ++ tailWord_5291455) baseStart_5291455 baseEnd_5291455 := by
    simpa [prefixWord, tailWord_5291455, baseEnd_5291455] using wordTrace_append hprefix tailTrace_5291455
  have hstable : (prefixWord ++ tailWord_5291455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291455).length < 2 ^ (prefixWord ++ tailWord_5291455).sum := by decide
  have hdescent : baseEnd_5291455 < baseStart_5291455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291566 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_5291566 : Nat := 118140960795 + 5291566 * 2 ^ 59
def prefixEnd_5291566 : Nat := 4983230072969 + 3 ^ 40 * 5291566 * 2
def baseEnd_5291566 : Nat := 905705590996449652463179

theorem tailTrace_5291566 : CollatzResearch.WordTrace tailWord_5291566 prefixEnd_5291566 905705590996449652463179 := by
  unfold tailWord_5291566
  simp only [CollatzResearch.WordTrace]
  refine ⟨24124908443445948046060819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128666178365045056245657701 24124908443445948046060819)
  ·
    refine ⟨36187362665168922069091229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24124908443445948046060819 36187362665168922069091229)
    ·
      refine ⟨13570260999438345775909211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36187362665168922069091229 13570260999438345775909211)
      ·
        refine ⟨20355391499157518663863817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13570260999438345775909211 20355391499157518663863817)
        ·
          refine ⟨15266543624368138997897863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20355391499157518663863817 15266543624368138997897863)
          ·
            refine ⟨22899815436552208496846795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15266543624368138997897863 22899815436552208496846795)
            ·
              refine ⟨34349723154828312745270193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22899815436552208496846795 34349723154828312745270193)
              ·
                refine ⟨25762292366121234558952645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34349723154828312745270193 25762292366121234558952645)
                ·
                  refine ⟨4830429818647731479803621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25762292366121234558952645 4830429818647731479803621)
                  ·
                    refine ⟨905705590996449652463179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4830429818647731479803621 905705590996449652463179)
                    ·
                      rfl

theorem cell23_5291566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_5291566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291566 prefixEnd_5291566 := by exact prefixLift 5291566
  have htrace : WordTrace (prefixWord ++ tailWord_5291566) baseStart_5291566 baseEnd_5291566 := by
    simpa [prefixWord, tailWord_5291566, baseEnd_5291566] using wordTrace_append hprefix tailTrace_5291566
  have hstable : (prefixWord ++ tailWord_5291566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291566).length < 2 ^ (prefixWord ++ tailWord_5291566).sum := by decide
  have hdescent : baseEnd_5291566 < baseStart_5291566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291576 : List Nat := [2, 1, 2, 1, 4, 2, 2, 3, 1, 2, 3]
def baseStart_5291576 : Nat := 118140960795 + 5291576 * 2 ^ 59
def prefixEnd_5291576 : Nat := 4983230072969 + 3 ^ 40 * 5291576 * 2
def baseEnd_5291576 : Nat := 2717121907795893918264491

theorem tailTrace_5291576 : CollatzResearch.WordTrace tailWord_5291576 prefixEnd_5291576 2717121907795893918264491 := by
  unfold tailWord_5291576
  simp only [CollatzResearch.WordTrace]
  refine ⟨96499816138765678038175291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128666421518354237384233721 96499816138765678038175291)
  ·
    refine ⟨144749724208148517057262937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96499816138765678038175291 144749724208148517057262937)
    ·
      refine ⟨108562293156111387792947203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144749724208148517057262937 108562293156111387792947203)
      ·
        refine ⟨162843439734167081689420805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108562293156111387792947203 162843439734167081689420805)
        ·
          refine ⟨30533144950156327816766401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162843439734167081689420805 30533144950156327816766401)
          ·
            refine ⟨22899858712617245862574801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30533144950156327816766401 22899858712617245862574801)
            ·
              refine ⟨17174894034462934396931101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22899858712617245862574801 17174894034462934396931101)
              ·
                refine ⟨6440585262923600398849163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17174894034462934396931101 6440585262923600398849163)
                ·
                  refine ⟨9660877894385400598273745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6440585262923600398849163 9660877894385400598273745)
                  ·
                    refine ⟨7245658420789050448705309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9660877894385400598273745 7245658420789050448705309)
                    ·
                      refine ⟨2717121907795893918264491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7245658420789050448705309 2717121907795893918264491)
                      ·
                        rfl

theorem cell23_5291576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_5291576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291576 prefixEnd_5291576 := by exact prefixLift 5291576
  have htrace : WordTrace (prefixWord ++ tailWord_5291576) baseStart_5291576 baseEnd_5291576 := by
    simpa [prefixWord, tailWord_5291576, baseEnd_5291576] using wordTrace_append hprefix tailTrace_5291576
  have hstable : (prefixWord ++ tailWord_5291576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291576).length < 2 ^ (prefixWord ++ tailWord_5291576).sum := by decide
  have hdescent : baseEnd_5291576 < baseStart_5291576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291599 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 2, 7, 2]
def baseStart_5291599 : Nat := 118140960795 + 5291599 * 2 ^ 59
def prefixEnd_5291599 : Nat := 4983230072969 + 3 ^ 40 * 5291599 * 2
def baseEnd_5291599 : Nat := 2717133717850947328276885

theorem tailTrace_5291599 : CollatzResearch.WordTrace tailWord_5291599 prefixEnd_5291599 2717133717850947328276885 := by
  unfold tailWord_5291599
  simp only [CollatzResearch.WordTrace]
  refine ⟨193000471156448031004437851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128666980770965354002958567 193000471156448031004437851)
  ·
    refine ⟨289500706734672046506656777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193000471156448031004437851 289500706734672046506656777)
    ·
      refine ⟨217125530051004034879992583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289500706734672046506656777 217125530051004034879992583)
      ·
        refine ⟨325688295076506052319988875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217125530051004034879992583 325688295076506052319988875)
        ·
          refine ⟨488532442614759078479983313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325688295076506052319988875 488532442614759078479983313)
          ·
            refine ⟨366399331961069308859987485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488532442614759078479983313 366399331961069308859987485)
            ·
              refine ⟨137399749485400990822495307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 366399331961069308859987485 137399749485400990822495307)
              ·
                refine ⟨206099624228101486233742961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137399749485400990822495307 206099624228101486233742961)
                ·
                  refine ⟨154574718171076114675307221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206099624228101486233742961 154574718171076114675307221)
                  ·
                    refine ⟨3622844957134596437702513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 154574718171076114675307221 3622844957134596437702513)
                    ·
                      refine ⟨2717133717850947328276885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3622844957134596437702513 2717133717850947328276885)
                      ·
                        rfl

theorem cell23_5291599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 7, 2].length) (baseStart_5291599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291599 prefixEnd_5291599 := by exact prefixLift 5291599
  have htrace : WordTrace (prefixWord ++ tailWord_5291599) baseStart_5291599 baseEnd_5291599 := by
    simpa [prefixWord, tailWord_5291599, baseEnd_5291599] using wordTrace_append hprefix tailTrace_5291599
  have hstable : (prefixWord ++ tailWord_5291599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291599).length < 2 ^ (prefixWord ++ tailWord_5291599).sum := by decide
  have hdescent : baseEnd_5291599 < baseStart_5291599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291659 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 4]
def baseStart_5291659 : Nat := 118140960795 + 5291659 * 2 ^ 59
def prefixEnd_5291659 : Nat := 4983230072969 + 3 ^ 40 * 5291659 * 2
def baseEnd_5291659 : Nat := 2717164526690217093526609

theorem tailTrace_5291659 : CollatzResearch.WordTrace tailWord_5291659 prefixEnd_5291659 2717164526690217093526609 := by
  unfold tailWord_5291659
  simp only [CollatzResearch.WordTrace]
  refine ⟨193002659536230661251622031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128668439690820440834414687 193002659536230661251622031)
  ·
    refine ⟨289503989304345991877433047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193002659536230661251622031 289503989304345991877433047)
    ·
      refine ⟨434255983956518987816149571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289503989304345991877433047 434255983956518987816149571)
      ·
        refine ⟨651383975934778481724224357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434255983956518987816149571 651383975934778481724224357)
        ·
          refine ⟨122134495487770965323292067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 651383975934778481724224357 122134495487770965323292067)
          ·
            refine ⟨183201743231656447984938101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122134495487770965323292067 183201743231656447984938101)
            ·
              refine ⟨17175163427967791998587947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 183201743231656447984938101 17175163427967791998587947)
              ·
                refine ⟨25762745141951687997881921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17175163427967791998587947 25762745141951687997881921)
                ·
                  refine ⟨19322058856463765998411441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25762745141951687997881921 19322058856463765998411441)
                  ·
                    refine ⟨14491544142347824498808581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19322058856463765998411441 14491544142347824498808581)
                    ·
                      refine ⟨2717164526690217093526609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14491544142347824498808581 2717164526690217093526609)
                      ·
                        rfl

theorem cell23_5291659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 4].length) (baseStart_5291659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291659 prefixEnd_5291659 := by exact prefixLift 5291659
  have htrace : WordTrace (prefixWord ++ tailWord_5291659) baseStart_5291659 baseEnd_5291659 := by
    simpa [prefixWord, tailWord_5291659, baseEnd_5291659] using wordTrace_append hprefix tailTrace_5291659
  have hstable : (prefixWord ++ tailWord_5291659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291659).length < 2 ^ (prefixWord ++ tailWord_5291659).sum := by decide
  have hdescent : baseEnd_5291659 < baseStart_5291659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291699 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 4, 5]
def baseStart_5291699 : Nat := 118140960795 + 5291699 * 2 ^ 59
def prefixEnd_5291699 : Nat := 4983230072969 + 3 ^ 40 * 5291699 * 2
def baseEnd_5291699 : Nat := 905728355305465645675475

theorem tailTrace_5291699 : CollatzResearch.WordTrace tailWord_5291699 prefixEnd_5291699 905728355305465645675475 := by
  unfold tailWord_5291699
  simp only [CollatzResearch.WordTrace]
  refine ⟨193004118456085748083078151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128669412304057165388718767 193004118456085748083078151)
  ·
    refine ⟨289506177684128622124617227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193004118456085748083078151 289506177684128622124617227)
    ·
      refine ⟨434259266526192933186925841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289506177684128622124617227 434259266526192933186925841)
      ·
        refine ⟨325694449894644699890194381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434259266526192933186925841 325694449894644699890194381)
        ·
          refine ⟨122135418710491762458822893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325694449894644699890194381 122135418710491762458822893)
          ·
            refine ⟨45800782016434410922058585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122135418710491762458822893 45800782016434410922058585)
            ·
              refine ⟨34350586512325808191543939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45800782016434410922058585 34350586512325808191543939)
              ·
                refine ⟨51525879768488712287315909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34350586512325808191543939 51525879768488712287315909)
                ·
                  refine ⟨9661102456591633553871733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51525879768488712287315909 9661102456591633553871733)
                  ·
                    refine ⟨905728355305465645675475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9661102456591633553871733 905728355305465645675475)
                    ·
                      rfl

theorem cell23_5291699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 5].length) (baseStart_5291699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291699 prefixEnd_5291699 := by exact prefixLift 5291699
  have htrace : WordTrace (prefixWord ++ tailWord_5291699) baseStart_5291699 baseEnd_5291699 := by
    simpa [prefixWord, tailWord_5291699, baseEnd_5291699] using wordTrace_append hprefix tailTrace_5291699
  have hstable : (prefixWord ++ tailWord_5291699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291699).length < 2 ^ (prefixWord ++ tailWord_5291699).sum := by decide
  have hdescent : baseEnd_5291699 < baseStart_5291699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291709 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_5291709 : Nat := 118140960795 + 5291709 * 2 ^ 59
def prefixEnd_5291709 : Nat := 4983230072969 + 3 ^ 40 * 5291709 * 2
def baseEnd_5291709 : Nat := 2717190200722941897901379

theorem tailTrace_5291709 : CollatzResearch.WordTrace tailWord_5291709 prefixEnd_5291709 2717190200722941897901379 := by
  unfold tailWord_5291709
  simp only [CollatzResearch.WordTrace]
  refine ⟨193004483186049519790942181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128669655457366346527294787 193004483186049519790942181)
  ·
    refine ⟨36188340597384284960801659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193004483186049519790942181 36188340597384284960801659)
    ·
      refine ⟨54282510896076427441202489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36188340597384284960801659 54282510896076427441202489)
      ·
        refine ⟨40711883172057320580901867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54282510896076427441202489 40711883172057320580901867)
        ·
          refine ⟨61067824758085980871352801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40711883172057320580901867 61067824758085980871352801)
          ·
            refine ⟨45800868568564485653514601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61067824758085980871352801 45800868568564485653514601)
            ·
              refine ⟨34350651426423364240135951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45800868568564485653514601 34350651426423364240135951)
              ·
                refine ⟨51525977139635046360203927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34350651426423364240135951 51525977139635046360203927)
                ·
                  refine ⟨77288965709452569540305891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51525977139635046360203927 77288965709452569540305891)
                  ·
                    refine ⟨115933448564178854310458837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77288965709452569540305891 115933448564178854310458837)
                    ·
                      refine ⟨2717190200722941897901379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115933448564178854310458837 2717190200722941897901379)
                      ·
                        rfl

theorem cell23_5291709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_5291709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291709 prefixEnd_5291709 := by exact prefixLift 5291709
  have htrace : WordTrace (prefixWord ++ tailWord_5291709) baseStart_5291709 baseEnd_5291709 := by
    simpa [prefixWord, tailWord_5291709, baseEnd_5291709] using wordTrace_append hprefix tailTrace_5291709
  have hstable : (prefixWord ++ tailWord_5291709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291709).length < 2 ^ (prefixWord ++ tailWord_5291709).sum := by decide
  have hdescent : baseEnd_5291709 < baseStart_5291709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291719 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_5291719 : Nat := 118140960795 + 5291719 * 2 ^ 59
def prefixEnd_5291719 : Nat := 4983230072969 + 3 ^ 40 * 5291719 * 2
def baseEnd_5291719 : Nat := 2717195335529486858776333

theorem tailTrace_5291719 : CollatzResearch.WordTrace tailWord_5291719 prefixEnd_5291719 2717195335529486858776333 := by
  unfold tailWord_5291719
  simp only [CollatzResearch.WordTrace]
  refine ⟨193004847916013291498806211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128669898610675527665870807 193004847916013291498806211)
  ·
    refine ⟨289507271874019937248209317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193004847916013291498806211 289507271874019937248209317)
    ·
      refine ⟨54282613476378738234039247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289507271874019937248209317 54282613476378738234039247)
      ·
        refine ⟨81423920214568107351058871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54282613476378738234039247 81423920214568107351058871)
        ·
          refine ⟨122135880321852161026588307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81423920214568107351058871 122135880321852161026588307)
          ·
            refine ⟨183203820482778241539882461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122135880321852161026588307 183203820482778241539882461)
            ·
              refine ⟨68701432681041840577455923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183203820482778241539882461 68701432681041840577455923)
              ·
                refine ⟨103052149021562760866183885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68701432681041840577455923 103052149021562760866183885)
                ·
                  refine ⟨38644555883086035324818957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103052149021562760866183885 38644555883086035324818957)
                  ·
                    refine ⟨14491708456157263246807109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38644555883086035324818957 14491708456157263246807109)
                    ·
                      refine ⟨2717195335529486858776333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14491708456157263246807109 2717195335529486858776333)
                      ·
                        rfl

theorem cell23_5291719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_5291719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291719 prefixEnd_5291719 := by exact prefixLift 5291719
  have htrace : WordTrace (prefixWord ++ tailWord_5291719) baseStart_5291719 baseEnd_5291719 := by
    simpa [prefixWord, tailWord_5291719, baseEnd_5291719] using wordTrace_append hprefix tailTrace_5291719
  have hstable : (prefixWord ++ tailWord_5291719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291719).length < 2 ^ (prefixWord ++ tailWord_5291719).sum := by decide
  have hdescent : baseEnd_5291719 < baseStart_5291719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291736 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_5291736 : Nat := 118140960795 + 5291736 * 2 ^ 59
def prefixEnd_5291736 : Nat := 4983230072969 + 3 ^ 40 * 5291736 * 2
def baseEnd_5291736 : Nat := 2717204064700613292263755

theorem tailTrace_5291736 : CollatzResearch.WordTrace tailWord_5291736 prefixEnd_5291736 2717204064700613292263755 := by
  unfold tailWord_5291736
  simp only [CollatzResearch.WordTrace]
  refine ⟨96502733978475851701087531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128670311971301135601450041 96502733978475851701087531)
  ·
    refine ⟨144754100967713777551631297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96502733978475851701087531 144754100967713777551631297)
    ·
      refine ⟨108565575725785333163723473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144754100967713777551631297 108565575725785333163723473)
      ·
        refine ⟨81424181794338999872792605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108565575725785333163723473 81424181794338999872792605)
        ·
          refine ⟨30534068172877124952297227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81424181794338999872792605 30534068172877124952297227)
          ·
            refine ⟨45801102259315687428445841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30534068172877124952297227 45801102259315687428445841)
            ·
              refine ⟨34350826694486765571334381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45801102259315687428445841 34350826694486765571334381)
              ·
                refine ⟨12881560010432537089250393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34350826694486765571334381 12881560010432537089250393)
                ·
                  refine ⟨9661170007824402816937795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12881560010432537089250393 9661170007824402816937795)
                  ·
                    refine ⟨14491755011736604225406693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9661170007824402816937795 14491755011736604225406693)
                    ·
                      refine ⟨2717204064700613292263755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14491755011736604225406693 2717204064700613292263755)
                      ·
                        rfl

theorem cell23_5291736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_5291736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291736 prefixEnd_5291736 := by exact prefixLift 5291736
  have htrace : WordTrace (prefixWord ++ tailWord_5291736) baseStart_5291736 baseEnd_5291736 := by
    simpa [prefixWord, tailWord_5291736, baseEnd_5291736] using wordTrace_append hprefix tailTrace_5291736
  have hstable : (prefixWord ++ tailWord_5291736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291736).length < 2 ^ (prefixWord ++ tailWord_5291736).sum := by decide
  have hdescent : baseEnd_5291736 < baseStart_5291736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291756 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 3]
def baseStart_5291756 : Nat := 118140960795 + 5291756 * 2 ^ 59
def prefixEnd_5291756 : Nat := 4983230072969 + 3 ^ 40 * 5291756 * 2
def baseEnd_5291756 : Nat := 2717214334313703214013663

theorem tailTrace_5291756 : CollatzResearch.WordTrace tailWord_5291756 prefixEnd_5291756 2717214334313703214013663 := by
  unfold tailWord_5291756
  simp only [CollatzResearch.WordTrace]
  refine ⟨96503098708439623408951561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128670798277919497878602081 96503098708439623408951561)
  ·
    refine ⟨72377324031329717556713671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96503098708439623408951561 72377324031329717556713671)
    ·
      refine ⟨108565986046994576335070507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72377324031329717556713671 108565986046994576335070507)
      ·
        refine ⟨162848979070491864502605761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108565986046994576335070507 162848979070491864502605761)
        ·
          refine ⟨122136734302868898376954321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162848979070491864502605761 122136734302868898376954321)
          ·
            refine ⟨91602550727151673782715741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122136734302868898376954321 91602550727151673782715741)
            ·
              refine ⟨34350956522681877668518403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91602550727151673782715741 34350956522681877668518403)
              ·
                refine ⟨51526434784022816502777605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34350956522681877668518403 51526434784022816502777605)
                ·
                  refine ⟨9661206522004278094270801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51526434784022816502777605 9661206522004278094270801)
                  ·
                    refine ⟨7245904891503208570703101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9661206522004278094270801 7245904891503208570703101)
                    ·
                      refine ⟨2717214334313703214013663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7245904891503208570703101 2717214334313703214013663)
                      ·
                        rfl

theorem cell23_5291756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_5291756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291756 prefixEnd_5291756 := by exact prefixLift 5291756
  have htrace : WordTrace (prefixWord ++ tailWord_5291756) baseStart_5291756 baseEnd_5291756 := by
    simpa [prefixWord, tailWord_5291756, baseEnd_5291756] using wordTrace_append hprefix tailTrace_5291756
  have hstable : (prefixWord ++ tailWord_5291756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291756).length < 2 ^ (prefixWord ++ tailWord_5291756).sum := by decide
  have hdescent : baseEnd_5291756 < baseStart_5291756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291759 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 8]
def baseStart_5291759 : Nat := 118140960795 + 5291759 * 2 ^ 59
def prefixEnd_5291759 : Nat := 4983230072969 + 3 ^ 40 * 5291759 * 2
def baseEnd_5291759 : Nat := 301912874972851855808461

theorem tailTrace_5291759 : CollatzResearch.WordTrace tailWord_5291759 prefixEnd_5291759 301912874972851855808461 := by
  unfold tailWord_5291759
  simp only [CollatzResearch.WordTrace]
  refine ⟨193006306835868378330262331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128670871223912252220174887 193006306835868378330262331)
  ·
    refine ⟨289509460253802567495393497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193006306835868378330262331 289509460253802567495393497)
    ·
      refine ⟨217132095190351925621545123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289509460253802567495393497 217132095190351925621545123)
      ·
        refine ⟨325698142785527888432317685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217132095190351925621545123 325698142785527888432317685)
        ·
          refine ⟨30534200886143239540529783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 325698142785527888432317685 30534200886143239540529783)
          ·
            refine ⟨45801301329214859310794675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30534200886143239540529783 45801301329214859310794675)
            ·
              refine ⟨68701951993822288966192013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45801301329214859310794675 68701951993822288966192013)
              ·
                refine ⟨25763231997683358362322005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68701951993822288966192013 25763231997683358362322005)
                ·
                  refine ⟨301912874972851855808461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25763231997683358362322005 301912874972851855808461)
                  ·
                    rfl

theorem cell23_5291759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 8].length) (baseStart_5291759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291759 prefixEnd_5291759 := by exact prefixLift 5291759
  have htrace : WordTrace (prefixWord ++ tailWord_5291759) baseStart_5291759 baseEnd_5291759 := by
    simpa [prefixWord, tailWord_5291759, baseEnd_5291759] using wordTrace_append hprefix tailTrace_5291759
  have hstable : (prefixWord ++ tailWord_5291759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291759).length < 2 ^ (prefixWord ++ tailWord_5291759).sum := by decide
  have hdescent : baseEnd_5291759 < baseStart_5291759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291763 : List Nat := [1, 1, 1, 2, 2, 3, 2, 6, 1, 4]
def baseStart_5291763 : Nat := 118140960795 + 5291763 * 2 ^ 59
def prefixEnd_5291763 : Nat := 4983230072969 + 3 ^ 40 * 5291763 * 2
def baseEnd_5291763 : Nat := 905739309559428228875377

theorem tailTrace_5291763 : CollatzResearch.WordTrace tailWord_5291763 prefixEnd_5291763 905739309559428228875377 := by
  unfold tailWord_5291763
  simp only [CollatzResearch.WordTrace]
  refine ⟨193006452727853887013407943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128670968485235924675605295 193006452727853887013407943)
  ·
    refine ⟨289509679091780830520111915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193006452727853887013407943 289509679091780830520111915)
    ·
      refine ⟨434264518637671245780167873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289509679091780830520111915 434264518637671245780167873)
      ·
        refine ⟨325698388978253434335125905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434264518637671245780167873 325698388978253434335125905)
        ·
          refine ⟨244273791733690075751344429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325698388978253434335125905 244273791733690075751344429)
          ·
            refine ⟨91602671900133778406754161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244273791733690075751344429 91602671900133778406754161)
            ·
              refine ⟨68702003925100333805065621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91602671900133778406754161 68702003925100333805065621)
              ·
                refine ⟨3220406433989078147112451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68702003925100333805065621 3220406433989078147112451)
                ·
                  refine ⟨4830609650983617220668677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220406433989078147112451 4830609650983617220668677)
                  ·
                    refine ⟨905739309559428228875377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4830609650983617220668677 905739309559428228875377)
                    ·
                      rfl

theorem cell23_5291763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 1, 4].length) (baseStart_5291763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291763 prefixEnd_5291763 := by exact prefixLift 5291763
  have htrace : WordTrace (prefixWord ++ tailWord_5291763) baseStart_5291763 baseEnd_5291763 := by
    simpa [prefixWord, tailWord_5291763, baseEnd_5291763] using wordTrace_append hprefix tailTrace_5291763
  have hstable : (prefixWord ++ tailWord_5291763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291763).length < 2 ^ (prefixWord ++ tailWord_5291763).sum := by decide
  have hdescent : baseEnd_5291763 < baseStart_5291763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291779 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 6]
def baseStart_5291779 : Nat := 118140960795 + 5291779 * 2 ^ 59
def prefixEnd_5291779 : Nat := 4983230072969 + 3 ^ 40 * 5291779 * 2
def baseEnd_5291779 : Nat := 2717226144368756624026057

theorem tailTrace_5291779 : CollatzResearch.WordTrace tailWord_5291779 prefixEnd_5291779 2717226144368756624026057 := by
  unfold tailWord_5291779
  simp only [CollatzResearch.WordTrace]
  refine ⟨193007036295795921745990391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128671357530530614497326927 193007036295795921745990391)
  ·
    refine ⟨289510554443693882618985587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193007036295795921745990391 289510554443693882618985587)
    ·
      refine ⟨434265831665540823928478381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289510554443693882618985587 434265831665540823928478381)
      ·
        refine ⟨162849686874577808973179393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434265831665540823928478381 162849686874577808973179393)
        ·
          refine ⟨122137265155933356729884545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162849686874577808973179393 122137265155933356729884545)
          ·
            refine ⟨91602948866950017547413409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122137265155933356729884545 91602948866950017547413409)
            ·
              refine ⟨68702211650212513160560057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91602948866950017547413409 68702211650212513160560057)
              ·
                refine ⟨51526658737659384870420043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68702211650212513160560057 51526658737659384870420043)
                ·
                  refine ⟨77289988106489077305630065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51526658737659384870420043 77289988106489077305630065)
                  ·
                    refine ⟨57967491079866807979222549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77289988106489077305630065 57967491079866807979222549)
                    ·
                      refine ⟨2717226144368756624026057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57967491079866807979222549 2717226144368756624026057)
                      ·
                        rfl

theorem cell23_5291779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_5291779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291779 prefixEnd_5291779 := by exact prefixLift 5291779
  have htrace : WordTrace (prefixWord ++ tailWord_5291779) baseStart_5291779 baseEnd_5291779 := by
    simpa [prefixWord, tailWord_5291779, baseEnd_5291779] using wordTrace_append hprefix tailTrace_5291779
  have hstable : (prefixWord ++ tailWord_5291779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291779).length < 2 ^ (prefixWord ++ tailWord_5291779).sum := by decide
  have hdescent : baseEnd_5291779 < baseStart_5291779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291836 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 1, 6]
def baseStart_5291836 : Nat := 118140960795 + 5291836 * 2 ^ 59
def prefixEnd_5291836 : Nat := 4983230072969 + 3 ^ 40 * 5291836 * 2
def baseEnd_5291836 : Nat := 905751804255354300337765

theorem tailTrace_5291836 : CollatzResearch.WordTrace tailWord_5291836 prefixEnd_5291836 905751804255354300337765 := by
  unfold tailWord_5291836
  simp only [CollatzResearch.WordTrace]
  refine ⟨96504557628294710240407681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128672743504392946987210241 96504557628294710240407681)
  ·
    refine ⟨72378418221221032680305761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96504557628294710240407681 72378418221221032680305761)
    ·
      refine ⟨54283813665915774510229321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72378418221221032680305761 54283813665915774510229321)
      ·
        refine ⟨40712860249436830882671991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54283813665915774510229321 40712860249436830882671991)
        ·
          refine ⟨61069290374155246324007987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40712860249436830882671991 61069290374155246324007987)
          ·
            refine ⟨91603935561232869486011981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61069290374155246324007987 91603935561232869486011981)
            ·
              refine ⟨34351475835462326057254493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91603935561232869486011981 34351475835462326057254493)
              ·
                refine ⟨12881803438298372271470435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34351475835462326057254493 12881803438298372271470435)
                ·
                  refine ⟨19322705157447558407205653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12881803438298372271470435 19322705157447558407205653)
                  ·
                    refine ⟨905751804255354300337765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19322705157447558407205653 905751804255354300337765)
                    ·
                      rfl

theorem cell23_5291836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_5291836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291836 prefixEnd_5291836 := by exact prefixLift 5291836
  have htrace : WordTrace (prefixWord ++ tailWord_5291836) baseStart_5291836 baseEnd_5291836 := by
    simpa [prefixWord, tailWord_5291836, baseEnd_5291836] using wordTrace_append hprefix tailTrace_5291836
  have hstable : (prefixWord ++ tailWord_5291836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291836).length < 2 ^ (prefixWord ++ tailWord_5291836).sum := by decide
  have hdescent : baseEnd_5291836 < baseStart_5291836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291860 : List Nat := [2, 4, 1, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_5291860 : Nat := 118140960795 + 5291860 * 2 ^ 59
def prefixEnd_5291860 : Nat := 4983230072969 + 3 ^ 40 * 5291860 * 2
def baseEnd_5291860 : Nat := 2717267736301770807113185

theorem tailTrace_5291860 : CollatzResearch.WordTrace tailWord_5291860 prefixEnd_5291860 2717267736301770807113185 := by
  unfold tailWord_5291860
  simp only [CollatzResearch.WordTrace]
  refine ⟨96504995304251236289844517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128673327072334981719792689 96504995304251236289844517)
  ·
    refine ⟨18094686619547106804345847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96504995304251236289844517 18094686619547106804345847)
    ·
      refine ⟨27142029929320660206518771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18094686619547106804345847 27142029929320660206518771)
      ·
        refine ⟨40713044893980990309778157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27142029929320660206518771 40713044893980990309778157)
        ·
          refine ⟨15267391835242871366166809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40713044893980990309778157 15267391835242871366166809)
          ·
            refine ⟨11450543876432153524625107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15267391835242871366166809 11450543876432153524625107)
            ·
              refine ⟨17175815814648230286937661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11450543876432153524625107 17175815814648230286937661)
              ·
                refine ⟨6440930930493086357601623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17175815814648230286937661 6440930930493086357601623)
                ·
                  refine ⟨9661396395739629536402435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6440930930493086357601623 9661396395739629536402435)
                  ·
                    refine ⟨14492094593609444304603653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9661396395739629536402435 14492094593609444304603653)
                    ·
                      refine ⟨2717267736301770807113185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14492094593609444304603653 2717267736301770807113185)
                      ·
                        rfl

theorem cell23_5291860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_5291860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291860 prefixEnd_5291860 := by exact prefixLift 5291860
  have htrace : WordTrace (prefixWord ++ tailWord_5291860) baseStart_5291860 baseEnd_5291860 := by
    simpa [prefixWord, tailWord_5291860, baseEnd_5291860] using wordTrace_append hprefix tailTrace_5291860
  have hstable : (prefixWord ++ tailWord_5291860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291860).length < 2 ^ (prefixWord ++ tailWord_5291860).sum := by decide
  have hdescent : baseEnd_5291860 < baseStart_5291860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291911 : List Nat := [1, 1, 4, 2, 4, 2, 1, 3, 1, 2, 2]
def baseStart_5291911 : Nat := 118140960795 + 5291911 * 2 ^ 59
def prefixEnd_5291911 : Nat := 4983230072969 + 3 ^ 40 * 5291911 * 2
def baseEnd_5291911 : Nat := 2717293923815150107575451

theorem tailTrace_5291911 : CollatzResearch.WordTrace tailWord_5291911 prefixEnd_5291911 2717293923815150107575451 := by
  unfold tailWord_5291911
  simp only [CollatzResearch.WordTrace]
  refine ⟨193011850731317708289795587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128674567154211805526530391 193011850731317708289795587)
  ·
    refine ⟨289517776096976562434693381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193011850731317708289795587 289517776096976562434693381)
    ·
      refine ⟨54284583018183105456505009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289517776096976562434693381 54284583018183105456505009)
      ·
        refine ⟨40713437263637329092378757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54284583018183105456505009 40713437263637329092378757)
        ·
          refine ⟨7633769486931999204821017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40713437263637329092378757 7633769486931999204821017)
          ·
            refine ⟨5725327115198999403615763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7633769486931999204821017 5725327115198999403615763)
            ·
              refine ⟨8587990672798499105423645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5725327115198999403615763 8587990672798499105423645)
              ·
                refine ⟨3220496502299437164533867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8587990672798499105423645 3220496502299437164533867)
                ·
                  refine ⟨4830744753449155746800801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220496502299437164533867 4830744753449155746800801)
                  ·
                    refine ⟨3623058565086866810100601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4830744753449155746800801 3623058565086866810100601)
                    ·
                      refine ⟨2717293923815150107575451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623058565086866810100601 2717293923815150107575451)
                      ·
                        rfl

theorem cell23_5291911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_5291911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291911 prefixEnd_5291911 := by exact prefixLift 5291911
  have htrace : WordTrace (prefixWord ++ tailWord_5291911) baseStart_5291911 baseEnd_5291911 := by
    simpa [prefixWord, tailWord_5291911, baseEnd_5291911] using wordTrace_append hprefix tailTrace_5291911
  have hstable : (prefixWord ++ tailWord_5291911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291911).length < 2 ^ (prefixWord ++ tailWord_5291911).sum := by decide
  have hdescent : baseEnd_5291911 < baseStart_5291911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291916 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_5291916 : Nat := 118140960795 + 5291916 * 2 ^ 59
def prefixEnd_5291916 : Nat := 4983230072969 + 3 ^ 40 * 5291916 * 2
def baseEnd_5291916 : Nat := 2717296491218422588012927

theorem tailTrace_5291916 : CollatzResearch.WordTrace tailWord_5291916 prefixEnd_5291916 2717296491218422588012927 := by
  unfold tailWord_5291916
  simp only [CollatzResearch.WordTrace]
  refine ⟨96506016548149797071863801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128674688730866396095818401 96506016548149797071863801)
  ·
    refine ⟨72379512411112347803897851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96506016548149797071863801 72379512411112347803897851)
    ·
      refine ⟨108569268616668521705846777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72379512411112347803897851 108569268616668521705846777)
      ·
        refine ⟨81426951462501391279385083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108569268616668521705846777 81426951462501391279385083)
        ·
          refine ⟨122140427193752086919077625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81426951462501391279385083 122140427193752086919077625)
          ·
            refine ⟨91605320395314065189308219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122140427193752086919077625 91605320395314065189308219)
            ·
              refine ⟨137407980592971097783962329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91605320395314065189308219 137407980592971097783962329)
              ·
                refine ⟨103055985444728323337971747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137407980592971097783962329 103055985444728323337971747)
                ·
                  refine ⟨154583978167092485006957621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103055985444728323337971747 154583978167092485006957621)
                  ·
                    refine ⟨14492247953164920469402277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 154583978167092485006957621 14492247953164920469402277)
                    ·
                      refine ⟨2717296491218422588012927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14492247953164920469402277 2717296491218422588012927)
                      ·
                        rfl

theorem cell23_5291916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_5291916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291916 prefixEnd_5291916 := by exact prefixLift 5291916
  have htrace : WordTrace (prefixWord ++ tailWord_5291916) baseStart_5291916 baseEnd_5291916 := by
    simpa [prefixWord, tailWord_5291916, baseEnd_5291916] using wordTrace_append hprefix tailTrace_5291916
  have hstable : (prefixWord ++ tailWord_5291916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291916).length < 2 ^ (prefixWord ++ tailWord_5291916).sum := by decide
  have hdescent : baseEnd_5291916 < baseStart_5291916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291928 : List Nat := [2, 1, 2, 6, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5291928 : Nat := 118140960795 + 5291928 * 2 ^ 59
def prefixEnd_5291928 : Nat := 4983230072969 + 3 ^ 40 * 5291928 * 2
def baseEnd_5291928 : Nat := 2717302652986276541062873

theorem tailTrace_5291928 : CollatzResearch.WordTrace tailWord_5291928 prefixEnd_5291928 2717302652986276541062873 := by
  unfold tailWord_5291928
  simp only [CollatzResearch.WordTrace]
  refine ⟨96506235386128060096582219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128674980514837413462109625 96506235386128060096582219)
  ·
    refine ⟨144759353079192090144873329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96506235386128060096582219 144759353079192090144873329)
    ·
      refine ⟨108569514809394067608654997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144759353079192090144873329 108569514809394067608654997)
      ·
        refine ⟨5089196006690346919155703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108569514809394067608654997 5089196006690346919155703)
        ·
          refine ⟨7633794010035520378733555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5089196006690346919155703 7633794010035520378733555)
          ·
            refine ⟨11450691015053280568100333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7633794010035520378733555 11450691015053280568100333)
            ·
              refine ⟨4294009130644980213037625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11450691015053280568100333 4294009130644980213037625)
              ·
                refine ⟨3220506847983735159778219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4294009130644980213037625 3220506847983735159778219)
                ·
                  refine ⟨4830760271975602739667329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220506847983735159778219 4830760271975602739667329)
                  ·
                    refine ⟨3623070203981702054750497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4830760271975602739667329 3623070203981702054750497)
                    ·
                      refine ⟨2717302652986276541062873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623070203981702054750497 2717302652986276541062873)
                      ·
                        rfl

theorem cell23_5291928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5291928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291928 prefixEnd_5291928 := by exact prefixLift 5291928
  have htrace : WordTrace (prefixWord ++ tailWord_5291928) baseStart_5291928 baseEnd_5291928 := by
    simpa [prefixWord, tailWord_5291928, baseEnd_5291928] using wordTrace_append hprefix tailTrace_5291928
  have hstable : (prefixWord ++ tailWord_5291928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291928).length < 2 ^ (prefixWord ++ tailWord_5291928).sum := by decide
  have hdescent : baseEnd_5291928 < baseStart_5291928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291936 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 5]
def baseStart_5291936 : Nat := 118140960795 + 5291936 * 2 ^ 59
def prefixEnd_5291936 : Nat := 4983230072969 + 3 ^ 40 * 5291936 * 2
def baseEnd_5291936 : Nat := 2717306760831512509762835

theorem tailTrace_5291936 : CollatzResearch.WordTrace tailWord_5291936 prefixEnd_5291936 2717306760831512509762835 := by
  unfold tailWord_5291936
  simp only [CollatzResearch.WordTrace]
  refine ⟨96506381278113568779727831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128675175037484758372970441 96506381278113568779727831)
  ·
    refine ⟨144759571917170353169591747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96506381278113568779727831 144759571917170353169591747)
    ·
      refine ⟨217139357875755529754387621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144759571917170353169591747 217139357875755529754387621)
      ·
        refine ⟨40713629601704161828947679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217139357875755529754387621 40713629601704161828947679)
        ·
          refine ⟨61070444402556242743421519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40713629601704161828947679 61070444402556242743421519)
          ·
            refine ⟨91605666603834364115132279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61070444402556242743421519 91605666603834364115132279)
            ·
              refine ⟨137408499905751546172698419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91605666603834364115132279 137408499905751546172698419)
              ·
                refine ⟨206112749858627319259047629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137408499905751546172698419 206112749858627319259047629)
                ·
                  refine ⟨77292281196985244722142861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206112749858627319259047629 77292281196985244722142861)
                  ·
                    refine ⟨28984605448869466770803573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77292281196985244722142861 28984605448869466770803573)
                    ·
                      refine ⟨2717306760831512509762835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28984605448869466770803573 2717306760831512509762835)
                      ·
                        rfl

theorem cell23_5291936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_5291936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291936 prefixEnd_5291936 := by exact prefixLift 5291936
  have htrace : WordTrace (prefixWord ++ tailWord_5291936) baseStart_5291936 baseEnd_5291936 := by
    simpa [prefixWord, tailWord_5291936, baseEnd_5291936] using wordTrace_append hprefix tailTrace_5291936
  have hstable : (prefixWord ++ tailWord_5291936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291936).length < 2 ^ (prefixWord ++ tailWord_5291936).sum := by decide
  have hdescent : baseEnd_5291936 < baseStart_5291936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291953 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_5291953 : Nat := 118140960795 + 5291953 * 2 ^ 59
def prefixEnd_5291953 : Nat := 4983230072969 + 3 ^ 40 * 5291953 * 2
def baseEnd_5291953 : Nat := 2717315490002638943250257

theorem tailTrace_5291953 : CollatzResearch.WordTrace tailWord_5291953 prefixEnd_5291953 2717315490002638943250257 := by
  unfold tailWord_5291953
  simp only [CollatzResearch.WordTrace]
  refine ⟨193013382597165549462824513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128675588398110366308549675 193013382597165549462824513)
  ·
    refine ⟨144760036947874162097118385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193013382597165549462824513 144760036947874162097118385)
    ·
      refine ⟨108570027710905621572838789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144760036947874162097118385 108570027710905621572838789)
      ·
        refine ⟨20356880195794804044907273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108570027710905621572838789 20356880195794804044907273)
        ·
          refine ⟨15267660146846103033680455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20356880195794804044907273 15267660146846103033680455)
          ·
            refine ⟨22901490220269154550520683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15267660146846103033680455 22901490220269154550520683)
            ·
              refine ⟨34352235330403731825781025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22901490220269154550520683 34352235330403731825781025)
              ·
                refine ⟨25764176497802798869335769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34352235330403731825781025 25764176497802798869335769)
                ·
                  refine ⟨19323132373352099152001827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25764176497802798869335769 19323132373352099152001827)
                  ·
                    refine ⟨28984698560028148728002741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19323132373352099152001827 28984698560028148728002741)
                    ·
                      refine ⟨2717315490002638943250257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28984698560028148728002741 2717315490002638943250257)
                      ·
                        rfl

theorem cell23_5291953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_5291953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291953 prefixEnd_5291953 := by exact prefixLift 5291953
  have htrace : WordTrace (prefixWord ++ tailWord_5291953) baseStart_5291953 baseEnd_5291953 := by
    simpa [prefixWord, tailWord_5291953, baseEnd_5291953] using wordTrace_append hprefix tailTrace_5291953
  have hstable : (prefixWord ++ tailWord_5291953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291953).length < 2 ^ (prefixWord ++ tailWord_5291953).sum := by decide
  have hdescent : baseEnd_5291953 < baseStart_5291953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291983 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 3]
def baseStart_5291983 : Nat := 118140960795 + 5291983 * 2 ^ 59
def prefixEnd_5291983 : Nat := 4983230072969 + 3 ^ 40 * 5291983 * 2
def baseEnd_5291983 : Nat := 2717330894422273825875119

theorem tailTrace_5291983 : CollatzResearch.WordTrace tailWord_5291983 prefixEnd_5291983 2717330894422273825875119 := by
  unfold tailWord_5291983
  simp only [CollatzResearch.WordTrace]
  refine ⟨193014476787056864586416603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128676317858037909724277735 193014476787056864586416603)
  ·
    refine ⟨289521715180585296879624905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193014476787056864586416603 289521715180585296879624905)
    ·
      refine ⟨217141286385438972659718679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289521715180585296879624905 217141286385438972659718679)
      ·
        refine ⟨325711929578158458989578019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217141286385438972659718679 325711929578158458989578019)
        ·
          refine ⟨488567894367237688484367029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325711929578158458989578019 488567894367237688484367029)
          ·
            refine ⟨45803240096928533295409409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 488567894367237688484367029 45803240096928533295409409)
            ·
              refine ⟨34352430072696399971557057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45803240096928533295409409 34352430072696399971557057)
              ·
                refine ⟨25764322554522299978667793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34352430072696399971557057 25764322554522299978667793)
                ·
                  refine ⟨19323241915891724984000845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25764322554522299978667793 19323241915891724984000845)
                  ·
                    refine ⟨7246215718459396869000317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19323241915891724984000845 7246215718459396869000317)
                    ·
                      refine ⟨2717330894422273825875119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7246215718459396869000317 2717330894422273825875119)
                      ·
                        rfl

theorem cell23_5291983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 3].length) (baseStart_5291983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291983 prefixEnd_5291983 := by exact prefixLift 5291983
  have htrace : WordTrace (prefixWord ++ tailWord_5291983) baseStart_5291983 baseEnd_5291983 := by
    simpa [prefixWord, tailWord_5291983, baseEnd_5291983] using wordTrace_append hprefix tailTrace_5291983
  have hstable : (prefixWord ++ tailWord_5291983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291983).length < 2 ^ (prefixWord ++ tailWord_5291983).sum := by decide
  have hdescent : baseEnd_5291983 < baseStart_5291983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292010 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_5292010 : Nat := 118140960795 + 5292010 * 2 ^ 59
def prefixEnd_5292010 : Nat := 4983230072969 + 3 ^ 40 * 5292010 * 2
def baseEnd_5292010 : Nat := 2717344758399945220237495

theorem tailTrace_5292010 : CollatzResearch.WordTrace tailWord_5292010 prefixEnd_5292010 2717344758399945220237495 := by
  unfold tailWord_5292010
  simp only [CollatzResearch.WordTrace]
  refine ⟨48253865389489762049412371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128676974371972698798432989 48253865389489762049412371)
  ·
    refine ⟨72380798084234643074118557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48253865389489762049412371 72380798084234643074118557)
    ·
      refine ⟨27142799281587991152794459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72380798084234643074118557 27142799281587991152794459)
      ·
        refine ⟨40714198922381986729191689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27142799281587991152794459 40714198922381986729191689)
        ·
          refine ⟨30535649191786490046893767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40714198922381986729191689 30535649191786490046893767)
          ·
            refine ⟨45803473787679735070340651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30535649191786490046893767 45803473787679735070340651)
            ·
              refine ⟨68705210681519602605510977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45803473787679735070340651 68705210681519602605510977)
              ·
                refine ⟨51528908011139701954133233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68705210681519602605510977 51528908011139701954133233)
                ·
                  refine ⟨38646681008354776465599925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51528908011139701954133233 38646681008354776465599925)
                  ·
                    refine ⟨3623126344533260293649993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38646681008354776465599925 3623126344533260293649993)
                    ·
                      refine ⟨2717344758399945220237495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623126344533260293649993 2717344758399945220237495)
                      ·
                        rfl

theorem cell23_5292010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_5292010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292010 prefixEnd_5292010 := by exact prefixLift 5292010
  have htrace : WordTrace (prefixWord ++ tailWord_5292010) baseStart_5292010 baseEnd_5292010 := by
    simpa [prefixWord, tailWord_5292010, baseEnd_5292010] using wordTrace_append hprefix tailTrace_5292010
  have hstable : (prefixWord ++ tailWord_5292010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292010).length < 2 ^ (prefixWord ++ tailWord_5292010).sum := by decide
  have hdescent : baseEnd_5292010 < baseStart_5292010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292040 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 4, 4, 2]
def baseStart_5292040 : Nat := 118140960795 + 5292040 * 2 ^ 59
def prefixEnd_5292040 : Nat := 4983230072969 + 3 ^ 40 * 5292040 * 2
def baseEnd_5292040 : Nat := 2717360162819580102862357

theorem tailTrace_5292040 : CollatzResearch.WordTrace tailWord_5292040 prefixEnd_5292040 2717360162819580102862357 := by
  unfold tailWord_5292040
  simp only [CollatzResearch.WordTrace]
  refine ⟨96508277873925181660620787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128677703831900242214161049 96508277873925181660620787)
  ·
    refine ⟨144762416810887772490931181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96508277873925181660620787 144762416810887772490931181)
    ·
      refine ⟨54285906304082914684099193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144762416810887772490931181 54285906304082914684099193)
      ·
        refine ⟨40714429728062186013074395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54285906304082914684099193 40714429728062186013074395)
        ·
          refine ⟨61071644592093279019611593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40714429728062186013074395 61071644592093279019611593)
          ·
            refine ⟨45803733444069959264708695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61071644592093279019611593 45803733444069959264708695)
            ·
              refine ⟨68705600166104938897063043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45803733444069959264708695 68705600166104938897063043)
              ·
                refine ⟨103058400249157408345594565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68705600166104938897063043 103058400249157408345594565)
                ·
                  refine ⟨19323450046717014064798981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103058400249157408345594565 19323450046717014064798981)
                  ·
                    refine ⟨3623146883759440137149809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19323450046717014064798981 3623146883759440137149809)
                    ·
                      refine ⟨2717360162819580102862357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623146883759440137149809 2717360162819580102862357)
                      ·
                        rfl

theorem cell23_5292040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_5292040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292040 prefixEnd_5292040 := by exact prefixLift 5292040
  have htrace : WordTrace (prefixWord ++ tailWord_5292040) baseStart_5292040 baseEnd_5292040 := by
    simpa [prefixWord, tailWord_5292040, baseEnd_5292040] using wordTrace_append hprefix tailTrace_5292040
  have hstable : (prefixWord ++ tailWord_5292040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292040).length < 2 ^ (prefixWord ++ tailWord_5292040).sum := by decide
  have hdescent : baseEnd_5292040 < baseStart_5292040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292060 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_5292060 : Nat := 118140960795 + 5292060 * 2 ^ 59
def prefixEnd_5292060 : Nat := 4983230072969 + 3 ^ 40 * 5292060 * 2
def baseEnd_5292060 : Nat := 2717370432432670024612265

theorem tailTrace_5292060 : CollatzResearch.WordTrace tailWord_5292060 prefixEnd_5292060 2717370432432670024612265 := by
  unfold tailWord_5292060
  simp only [CollatzResearch.WordTrace]
  refine ⟨96508642603888953368484817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128678190138518604491313089 96508642603888953368484817)
  ·
    refine ⟨72381481952916715026363613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96508642603888953368484817 72381481952916715026363613)
    ·
      refine ⟨27143055732343768134886355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72381481952916715026363613 27143055732343768134886355)
      ·
        refine ⟨40714583598515652202329533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27143055732343768134886355 40714583598515652202329533)
        ·
          refine ⟨15267968849443369575873575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40714583598515652202329533 15267968849443369575873575)
          ·
            refine ⟨22901953274165054363810363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15267968849443369575873575 22901953274165054363810363)
            ·
              refine ⟨34352929911247581545715545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22901953274165054363810363 34352929911247581545715545)
              ·
                refine ⟨25764697433435686159286659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34352929911247581545715545 25764697433435686159286659)
                ·
                  refine ⟨38647046150153529238929989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25764697433435686159286659 38647046150153529238929989)
                  ·
                    refine ⟨7246321153153786732299373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38647046150153529238929989 7246321153153786732299373)
                    ·
                      refine ⟨2717370432432670024612265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7246321153153786732299373 2717370432432670024612265)
                      ·
                        rfl

theorem cell23_5292060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_5292060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292060 prefixEnd_5292060 := by exact prefixLift 5292060
  have htrace : WordTrace (prefixWord ++ tailWord_5292060) baseStart_5292060 baseEnd_5292060 := by
    simpa [prefixWord, tailWord_5292060, baseEnd_5292060] using wordTrace_append hprefix tailTrace_5292060
  have hstable : (prefixWord ++ tailWord_5292060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292060).length < 2 ^ (prefixWord ++ tailWord_5292060).sum := by decide
  have hdescent : baseEnd_5292060 < baseStart_5292060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292094 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_5292094 : Nat := 118140960795 + 5292094 * 2 ^ 59
def prefixEnd_5292094 : Nat := 4983230072969 + 3 ^ 40 * 5292094 * 2
def baseEnd_5292094 : Nat := 2717387890774922891587109

theorem tailTrace_5292094 : CollatzResearch.WordTrace tailWord_5292094 prefixEnd_5292094 2717387890774922891587109 := by
  unfold tailWord_5292094
  simp only [CollatzResearch.WordTrace]
  refine ⟨24127315661206841317963417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128679016859769820362471557 24127315661206841317963417)
  ·
    refine ⟨18095486745905130988472563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24127315661206841317963417 18095486745905130988472563)
    ·
      refine ⟨27143230118857696482708845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18095486745905130988472563 27143230118857696482708845)
      ·
        refine ⟨10178711294571636181015817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27143230118857696482708845 10178711294571636181015817)
        ·
          refine ⟨7634033470928727135761863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10178711294571636181015817 7634033470928727135761863)
          ·
            refine ⟨11451050206393090703642795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7634033470928727135761863 11451050206393090703642795)
            ·
              refine ⟨17176575309589636055464193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11451050206393090703642795 17176575309589636055464193)
              ·
                refine ⟨12882431482192227041598145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17176575309589636055464193 12882431482192227041598145)
                ·
                  refine ⟨9661823611644170281198609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12882431482192227041598145 9661823611644170281198609)
                  ·
                    refine ⟨7246367708733127710898957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9661823611644170281198609 7246367708733127710898957)
                    ·
                      refine ⟨2717387890774922891587109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7246367708733127710898957 2717387890774922891587109)
                      ·
                        rfl

theorem cell23_5292094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_5292094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292094 prefixEnd_5292094 := by exact prefixLift 5292094
  have htrace : WordTrace (prefixWord ++ tailWord_5292094) baseStart_5292094 baseEnd_5292094 := by
    simpa [prefixWord, tailWord_5292094, baseEnd_5292094] using wordTrace_append hprefix tailTrace_5292094
  have hstable : (prefixWord ++ tailWord_5292094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292094).length < 2 ^ (prefixWord ++ tailWord_5292094).sum := by decide
  have hdescent : baseEnd_5292094 < baseStart_5292094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292113 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_5292113 : Nat := 118140960795 + 5292113 * 2 ^ 59
def prefixEnd_5292113 : Nat := 4983230072969 + 3 ^ 40 * 5292113 * 2
def baseEnd_5292113 : Nat := 2717397646907358317249521

theorem tailTrace_5292113 : CollatzResearch.WordTrace tailWord_5292113 prefixEnd_5292113 2717397646907358317249521 := by
  unfold tailWord_5292113
  simp only [CollatzResearch.WordTrace]
  refine ⟨193019218276585896788648993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128679478851057264525765995 193019218276585896788648993)
  ·
    refine ⟨144764413707439422591486745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193019218276585896788648993 144764413707439422591486745)
    ·
      refine ⟨108573310280579566943615059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144764413707439422591486745 108573310280579566943615059)
      ·
        refine ⟨162859965420869350415422589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108573310280579566943615059 162859965420869350415422589)
        ·
          refine ⟨61072487032826006405783471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162859965420869350415422589 61072487032826006405783471)
          ·
            refine ⟨91608730549239009608675207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61072487032826006405783471 91608730549239009608675207)
            ·
              refine ⟨137413095823858514413012811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91608730549239009608675207 137413095823858514413012811)
              ·
                refine ⟨206119643735787771619519217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137413095823858514413012811 206119643735787771619519217)
                ·
                  refine ⟨154589732801840828714639413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206119643735787771619519217 154589732801840828714639413)
                  ·
                    refine ⟨14492787450172577691997445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 154589732801840828714639413 14492787450172577691997445)
                    ·
                      refine ⟨2717397646907358317249521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14492787450172577691997445 2717397646907358317249521)
                      ·
                        rfl

theorem cell23_5292113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_5292113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292113 prefixEnd_5292113 := by exact prefixLift 5292113
  have htrace : WordTrace (prefixWord ++ tailWord_5292113) baseStart_5292113 baseEnd_5292113 := by
    simpa [prefixWord, tailWord_5292113, baseEnd_5292113] using wordTrace_append hprefix tailTrace_5292113
  have hstable : (prefixWord ++ tailWord_5292113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292113).length < 2 ^ (prefixWord ++ tailWord_5292113).sum := by decide
  have hdescent : baseEnd_5292113 < baseStart_5292113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292114 : List Nat := [3, 2, 2, 1, 4, 2, 2, 1, 6]
def baseStart_5292114 : Nat := 118140960795 + 5292114 * 2 ^ 59
def prefixEnd_5292114 : Nat := 4983230072969 + 3 ^ 40 * 5292114 * 2
def baseEnd_5292114 : Nat := 301933128932001423704113

theorem tailTrace_5292114 : CollatzResearch.WordTrace tailWord_5292114 prefixEnd_5292114 301933128932001423704113 := by
  unfold tailWord_5292114
  simp only [CollatzResearch.WordTrace]
  refine ⟨48254813687395568489858849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128679503166388182639623597 48254813687395568489858849)
  ·
    refine ⟨36191110265546676367394137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48254813687395568489858849 36191110265546676367394137)
    ·
      refine ⟨27143332699160007275545603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36191110265546676367394137 27143332699160007275545603)
      ·
        refine ⟨40714999048740010913318405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27143332699160007275545603 40714999048740010913318405)
        ·
          refine ⟨7634062321638752046247201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40714999048740010913318405 7634062321638752046247201)
          ·
            refine ⟨5725546741229064034685401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7634062321638752046247201 5725546741229064034685401)
            ·
              refine ⟨4294160055921798026014051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5725546741229064034685401 4294160055921798026014051)
              ·
                refine ⟨6441240083882697039021077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4294160055921798026014051 6441240083882697039021077)
                ·
                  refine ⟨301933128932001423704113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6441240083882697039021077 301933128932001423704113)
                  ·
                    rfl

theorem cell23_5292114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_5292114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292114 prefixEnd_5292114 := by exact prefixLift 5292114
  have htrace : WordTrace (prefixWord ++ tailWord_5292114) baseStart_5292114 baseEnd_5292114 := by
    simpa [prefixWord, tailWord_5292114, baseEnd_5292114] using wordTrace_append hprefix tailTrace_5292114
  have hstable : (prefixWord ++ tailWord_5292114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292114).length < 2 ^ (prefixWord ++ tailWord_5292114).sum := by decide
  have hdescent : baseEnd_5292114 < baseStart_5292114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292140 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 1, 6]
def baseStart_5292140 : Nat := 118140960795 + 5292140 * 2 ^ 59
def prefixEnd_5292140 : Nat := 4983230072969 + 3 ^ 40 * 5292140 * 2
def baseEnd_5292140 : Nat := 905803836961676570537299

theorem tailTrace_5292140 : CollatzResearch.WordTrace tailWord_5292140 prefixEnd_5292140 905803836961676570537299 := by
  unfold tailWord_5292140
  simp only [CollatzResearch.WordTrace]
  refine ⟨96510101523744040199940937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128680135364992053599921249 96510101523744040199940937)
  ·
    refine ⟨72382576142808030149955703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96510101523744040199940937 72382576142808030149955703)
    ·
      refine ⟨108573864214212045224933555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72382576142808030149955703 108573864214212045224933555)
      ·
        refine ⟨162860796321318067837400333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108573864214212045224933555 162860796321318067837400333)
        ·
          refine ⟨61072798620494275439025125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162860796321318067837400333 61072798620494275439025125)
          ·
            refine ⟨11451149741342676644817211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61072798620494275439025125 11451149741342676644817211)
            ·
              refine ⟨17176724612014014967225817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11451149741342676644817211 17176724612014014967225817)
              ·
                refine ⟨12882543459010511225419363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17176724612014014967225817 12882543459010511225419363)
                ·
                  refine ⟨19323815188515766838129045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12882543459010511225419363 19323815188515766838129045)
                  ·
                    refine ⟨905803836961676570537299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19323815188515766838129045 905803836961676570537299)
                    ·
                      rfl

theorem cell23_5292140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_5292140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292140 prefixEnd_5292140 := by exact prefixLift 5292140
  have htrace : WordTrace (prefixWord ++ tailWord_5292140) baseStart_5292140 baseEnd_5292140 := by
    simpa [prefixWord, tailWord_5292140, baseEnd_5292140] using wordTrace_append hprefix tailTrace_5292140
  have hstable : (prefixWord ++ tailWord_5292140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292140).length < 2 ^ (prefixWord ++ tailWord_5292140).sum := by decide
  have hdescent : baseEnd_5292140 < baseStart_5292140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292153 : List Nat := [1, 2, 1, 3, 4, 12]
def baseStart_5292153 : Nat := 118140960795 + 5292153 * 2 ^ 59
def prefixEnd_5292153 : Nat := 4983230072969 + 3 ^ 40 * 5292153 * 2
def baseEnd_5292153 : Nat := 11182790889438428645059

theorem tailTrace_5292153 : CollatzResearch.WordTrace tailWord_5292153 prefixEnd_5292153 11182790889438428645059 := by
  unfold tailWord_5292153
  simp only [CollatzResearch.WordTrace]
  refine ⟨193020677196440983620105113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128680451464293989080070075 193020677196440983620105113)
  ·
    refine ⟨144765507897330737715078835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193020677196440983620105113 144765507897330737715078835)
    ·
      refine ⟨217148261845996106572618253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144765507897330737715078835 217148261845996106572618253)
      ·
        refine ⟨81430598192248539964731845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217148261845996106572618253 81430598192248539964731845)
        ·
          refine ⟨15268237161046601243387221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81430598192248539964731845 15268237161046601243387221)
          ·
            refine ⟨11182790889438428645059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15268237161046601243387221 11182790889438428645059)
            ·
              rfl

theorem cell23_5292153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 12].length) (baseStart_5292153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292153 prefixEnd_5292153 := by exact prefixLift 5292153
  have htrace : WordTrace (prefixWord ++ tailWord_5292153) baseStart_5292153 baseEnd_5292153 := by
    simpa [prefixWord, tailWord_5292153, baseEnd_5292153] using wordTrace_append hprefix tailTrace_5292153
  have hstable : (prefixWord ++ tailWord_5292153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292153).length < 2 ^ (prefixWord ++ tailWord_5292153).sum := by decide
  have hdescent : baseEnd_5292153 < baseStart_5292153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292157 : List Nat := [1, 4, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_5292157 : Nat := 118140960795 + 5292157 * 2 ^ 59
def prefixEnd_5292157 : Nat := 4983230072969 + 3 ^ 40 * 5292157 * 2
def baseEnd_5292157 : Nat := 905806746685385381699773

theorem tailTrace_5292157 : CollatzResearch.WordTrace tailWord_5292157 prefixEnd_5292157 905806746685385381699773 := by
  unfold tailWord_5292157
  simp only [CollatzResearch.WordTrace]
  refine ⟨193020823088426492303250725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128680548725617661535500483 193020823088426492303250725)
  ·
    refine ⟨36191404329079967306859511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193020823088426492303250725 36191404329079967306859511)
    ·
      refine ⟨54287106493619950960289267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36191404329079967306859511 54287106493619950960289267)
      ·
        refine ⟨81430659740429926440433901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54287106493619950960289267 81430659740429926440433901)
        ·
          refine ⟨30536497402661222415162713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81430659740429926440433901 30536497402661222415162713)
          ·
            refine ⟨22902373051995916811372035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30536497402661222415162713 22902373051995916811372035)
            ·
              refine ⟨34353559577993875217058053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22902373051995916811372035 34353559577993875217058053)
              ·
                refine ⟨6441292420873851603198385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34353559577993875217058053 6441292420873851603198385)
                ·
                  refine ⟨4830969315655388702398789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6441292420873851603198385 4830969315655388702398789)
                  ·
                    refine ⟨905806746685385381699773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4830969315655388702398789 905806746685385381699773)
                    ·
                      rfl

theorem cell23_5292157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_5292157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292157 prefixEnd_5292157 := by exact prefixLift 5292157
  have htrace : WordTrace (prefixWord ++ tailWord_5292157) baseStart_5292157 baseEnd_5292157 := by
    simpa [prefixWord, tailWord_5292157, baseEnd_5292157] using wordTrace_append hprefix tailTrace_5292157
  have hstable : (prefixWord ++ tailWord_5292157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292157).length < 2 ^ (prefixWord ++ tailWord_5292157).sum := by decide
  have hdescent : baseEnd_5292157 < baseStart_5292157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292164 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_5292164 : Nat := 118140960795 + 5292164 * 2 ^ 59
def prefixEnd_5292164 : Nat := 4983230072969 + 3 ^ 40 * 5292164 * 2
def baseEnd_5292164 : Nat := 2717423834420737617711787

theorem tailTrace_5292164 : CollatzResearch.WordTrace tailWord_5292164 prefixEnd_5292164 2717423834420737617711787 := by
  unfold tailWord_5292164
  simp only [CollatzResearch.WordTrace]
  refine ⟨96510539199700566249377773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128680718932934088332503697 96510539199700566249377773)
  ·
    refine ⟨36191452199887712343516665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96510539199700566249377773 36191452199887712343516665)
    ·
      refine ⟨27143589149915784257637499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36191452199887712343516665 27143589149915784257637499)
      ·
        refine ⟨40715383724873676386456249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27143589149915784257637499 40715383724873676386456249)
        ·
          refine ⟨30536537793655257289842187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40715383724873676386456249 30536537793655257289842187)
          ·
            refine ⟨45804806690482885934763281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30536537793655257289842187 45804806690482885934763281)
            ·
              refine ⟨34353605017862164451072461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45804806690482885934763281 34353605017862164451072461)
              ·
                refine ⟨12882601881698311669152173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34353605017862164451072461 12882601881698311669152173)
                ·
                  refine ⟨4830975705636866875932065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12882601881698311669152173 4830975705636866875932065)
                  ·
                    refine ⟨3623231779227650156949049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4830975705636866875932065 3623231779227650156949049)
                    ·
                      refine ⟨2717423834420737617711787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623231779227650156949049 2717423834420737617711787)
                      ·
                        rfl

theorem cell23_5292164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_5292164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292164 prefixEnd_5292164 := by exact prefixLift 5292164
  have htrace : WordTrace (prefixWord ++ tailWord_5292164) baseStart_5292164 baseEnd_5292164 := by
    simpa [prefixWord, tailWord_5292164, baseEnd_5292164] using wordTrace_append hprefix tailTrace_5292164
  have hstable : (prefixWord ++ tailWord_5292164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292164).length < 2 ^ (prefixWord ++ tailWord_5292164).sum := by decide
  have hdescent : baseEnd_5292164 < baseStart_5292164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292170 : List Nat := [3, 1, 2, 3, 1, 2, 3, 8]
def baseStart_5292170 : Nat := 118140960795 + 5292170 * 2 ^ 59
def prefixEnd_5292170 : Nat := 4983230072969 + 3 ^ 40 * 5292170 * 2
def baseEnd_5292170 : Nat := 100645441307580170156917

theorem tailTrace_5292170 : CollatzResearch.WordTrace tailWord_5292170 prefixEnd_5292170 100645441307580170156917 := by
  unfold tailWord_5292170
  simp only [CollatzResearch.WordTrace]
  refine ⟨48255324309344848880868491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128680864824919597015649309 48255324309344848880868491)
  ·
    refine ⟨72382986464017273321302737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48255324309344848880868491 72382986464017273321302737)
    ·
      refine ⟨54287239848012954990977053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72382986464017273321302737 54287239848012954990977053)
      ·
        refine ⟨20357714943004858121616395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54287239848012954990977053 20357714943004858121616395)
        ·
          refine ⟨30536572414507287182424593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20357714943004858121616395 30536572414507287182424593)
          ·
            refine ⟨22902429310880465386818445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30536572414507287182424593 22902429310880465386818445)
            ·
              refine ⟨8588410991580174520056917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22902429310880465386818445 8588410991580174520056917)
              ·
                refine ⟨100645441307580170156917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8588410991580174520056917 100645441307580170156917)
                ·
                  rfl

theorem cell23_5292170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 8].length) (baseStart_5292170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292170 prefixEnd_5292170 := by exact prefixLift 5292170
  have htrace : WordTrace (prefixWord ++ tailWord_5292170) baseStart_5292170 baseEnd_5292170 := by
    simpa [prefixWord, tailWord_5292170, baseEnd_5292170] using wordTrace_append hprefix tailTrace_5292170
  have hstable : (prefixWord ++ tailWord_5292170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292170).length < 2 ^ (prefixWord ++ tailWord_5292170).sum := by decide
  have hdescent : baseEnd_5292170 < baseStart_5292170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292197 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 4, 1, 3]
def baseStart_5292197 : Nat := 118140960795 + 5292197 * 2 ^ 59
def prefixEnd_5292197 : Nat := 4983230072969 + 3 ^ 40 * 5292197 * 2
def baseEnd_5292197 : Nat := 2717440779282335988599135

theorem tailTrace_5292197 : CollatzResearch.WordTrace tailWord_5292197 prefixEnd_5292197 2717440779282335988599135 := by
  unfold tailWord_5292197
  simp only [CollatzResearch.WordTrace]
  refine ⟨193022282008281579134706845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128681521338854386089804563 193022282008281579134706845)
  ·
    refine ⟨72383355753105592175515067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193022282008281579134706845 72383355753105592175515067)
    ·
      refine ⟨108575033629658388263272601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72383355753105592175515067 108575033629658388263272601)
      ·
        refine ⟨81431275222243791197454451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108575033629658388263272601 81431275222243791197454451)
        ·
          refine ⟨122146912833365686796181677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81431275222243791197454451 122146912833365686796181677)
          ·
            refine ⟨45805092312512132548568129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122146912833365686796181677 45805092312512132548568129)
            ·
              refine ⟨34353819234384099411426097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45805092312512132548568129 34353819234384099411426097)
              ·
                refine ⟨25765364425788074558569573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34353819234384099411426097 25765364425788074558569573)
                ·
                  refine ⟨4831005829835263979731795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25765364425788074558569573 4831005829835263979731795)
                  ·
                    refine ⟨7246508744752895969597693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4831005829835263979731795 7246508744752895969597693)
                    ·
                      refine ⟨2717440779282335988599135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7246508744752895969597693 2717440779282335988599135)
                      ·
                        rfl

theorem cell23_5292197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_5292197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292197 prefixEnd_5292197 := by exact prefixLift 5292197
  have htrace : WordTrace (prefixWord ++ tailWord_5292197) baseStart_5292197 baseEnd_5292197 := by
    simpa [prefixWord, tailWord_5292197, baseEnd_5292197] using wordTrace_append hprefix tailTrace_5292197
  have hstable : (prefixWord ++ tailWord_5292197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292197).length < 2 ^ (prefixWord ++ tailWord_5292197).sum := by decide
  have hdescent : baseEnd_5292197 < baseStart_5292197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292250 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_5292250 : Nat := 118140960795 + 5292250 * 2 ^ 59
def prefixEnd_5292250 : Nat := 4983230072969 + 3 ^ 40 * 5292250 * 2
def baseEnd_5292250 : Nat := 2717467993757024281236391

theorem tailTrace_5292250 : CollatzResearch.WordTrace tailWord_5292250 prefixEnd_5292250 2717467993757024281236391 := by
  unfold tailWord_5292250
  simp only [CollatzResearch.WordTrace]
  refine ⟨48256053769272392296596551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128682810051393046124257469 48256053769272392296596551)
  ·
    refine ⟨72384080653908588444894827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48256053769272392296596551 72384080653908588444894827)
    ·
      refine ⟨108576120980862882667342241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72384080653908588444894827 108576120980862882667342241)
      ·
        refine ⟨81432090735647162000506681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108576120980862882667342241 81432090735647162000506681)
        ·
          refine ⟨61074068051735371500380011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81432090735647162000506681 61074068051735371500380011)
          ·
            refine ⟨91611102077603057250570017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61074068051735371500380011 91611102077603057250570017)
            ·
              refine ⟨68708326558202292937927513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91611102077603057250570017 68708326558202292937927513)
              ·
                refine ⟨51531244918651719703445635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68708326558202292937927513 51531244918651719703445635)
                ·
                  refine ⟨77296867377977579555168453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51531244918651719703445635 77296867377977579555168453)
                  ·
                    refine ⟨14493162633370796166594085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77296867377977579555168453 14493162633370796166594085)
                    ·
                      refine ⟨2717467993757024281236391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14493162633370796166594085 2717467993757024281236391)
                      ·
                        rfl

theorem cell23_5292250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_5292250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292250 prefixEnd_5292250 := by exact prefixLift 5292250
  have htrace : WordTrace (prefixWord ++ tailWord_5292250) baseStart_5292250 baseEnd_5292250 := by
    simpa [prefixWord, tailWord_5292250, baseEnd_5292250] using wordTrace_append hprefix tailTrace_5292250
  have hstable : (prefixWord ++ tailWord_5292250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292250).length < 2 ^ (prefixWord ++ tailWord_5292250).sum := by decide
  have hdescent : baseEnd_5292250 < baseStart_5292250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292270 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_5292270 : Nat := 118140960795 + 5292270 * 2 ^ 59
def prefixEnd_5292270 : Nat := 4983230072969 + 3 ^ 40 * 5292270 * 2
def baseEnd_5292270 : Nat := 2717478263370114202986299

theorem tailTrace_5292270 : CollatzResearch.WordTrace tailWord_5292270 prefixEnd_5292270 2717478263370114202986299 := by
  unfold tailWord_5292270
  simp only [CollatzResearch.WordTrace]
  refine ⟨24128118067127139075264283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128683296358011408401409509 24128118067127139075264283)
  ·
    refine ⟨36192177100690708612896425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24128118067127139075264283 36192177100690708612896425)
    ·
      refine ⟨27144132825518031459672319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36192177100690708612896425 27144132825518031459672319)
      ·
        refine ⟨40716199238277047189508479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27144132825518031459672319 40716199238277047189508479)
        ·
          refine ⟨61074298857415570784262719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40716199238277047189508479 61074298857415570784262719)
          ·
            refine ⟨91611448286123356176394079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61074298857415570784262719 91611448286123356176394079)
            ·
              refine ⟨137417172429185034264591119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91611448286123356176394079 137417172429185034264591119)
              ·
                refine ⟨206125758643777551396886679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137417172429185034264591119 206125758643777551396886679)
                ·
                  refine ⟨309188637965666327095330019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206125758643777551396886679 309188637965666327095330019)
                  ·
                    refine ⟨463782956948499490642995029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 309188637965666327095330019 463782956948499490642995029)
                    ·
                      refine ⟨2717478263370114202986299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 463782956948499490642995029 2717478263370114202986299)
                      ·
                        rfl

theorem cell23_5292270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_5292270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292270 prefixEnd_5292270 := by exact prefixLift 5292270
  have htrace : WordTrace (prefixWord ++ tailWord_5292270) baseStart_5292270 baseEnd_5292270 := by
    simpa [prefixWord, tailWord_5292270, baseEnd_5292270] using wordTrace_append hprefix tailTrace_5292270
  have hstable : (prefixWord ++ tailWord_5292270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292270).length < 2 ^ (prefixWord ++ tailWord_5292270).sum := by decide
  have hdescent : baseEnd_5292270 < baseStart_5292270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292300 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_5292300 : Nat := 118140960795 + 5292300 * 2 ^ 59
def prefixEnd_5292300 : Nat := 4983230072969 + 3 ^ 40 * 5292300 * 2
def baseEnd_5292300 : Nat := 2717493667789749085611161

theorem tailTrace_5292300 : CollatzResearch.WordTrace tailWord_5292300 prefixEnd_5292300 2717493667789749085611161 := by
  unfold tailWord_5292300
  simp only [CollatzResearch.WordTrace]
  refine ⟨96513019363454213862853177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128684025817938951817137569 96513019363454213862853177)
  ·
    refine ⟨72384764522590660397139883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96513019363454213862853177 72384764522590660397139883)
    ·
      refine ⟨108577146783885990595709825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72384764522590660397139883 108577146783885990595709825)
      ·
        refine ⟨81432860087914492946782369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108577146783885990595709825 81432860087914492946782369)
        ·
          refine ⟨61074645065935869710086777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81432860087914492946782369 61074645065935869710086777)
          ·
            refine ⟨45805983799451902282565083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61074645065935869710086777 45805983799451902282565083)
            ·
              refine ⟨68708975699177853423847625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45805983799451902282565083 68708975699177853423847625)
              ·
                refine ⟨51531731774383390067885719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68708975699177853423847625 51531731774383390067885719)
                ·
                  refine ⟨77297597661575085101828579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51531731774383390067885719 77297597661575085101828579)
                  ·
                    refine ⟨115946396492362627652742869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77297597661575085101828579 115946396492362627652742869)
                    ·
                      refine ⟨2717493667789749085611161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115946396492362627652742869 2717493667789749085611161)
                      ·
                        rfl

theorem cell23_5292300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_5292300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292300 prefixEnd_5292300 := by exact prefixLift 5292300
  have htrace : WordTrace (prefixWord ++ tailWord_5292300) baseStart_5292300 baseEnd_5292300 := by
    simpa [prefixWord, tailWord_5292300, baseEnd_5292300] using wordTrace_append hprefix tailTrace_5292300
  have hstable : (prefixWord ++ tailWord_5292300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292300).length < 2 ^ (prefixWord ++ tailWord_5292300).sum := by decide
  have hdescent : baseEnd_5292300 < baseStart_5292300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292328 : List Nat := [2, 1, 5, 1, 3, 2, 2, 2, 5]
def baseStart_5292328 : Nat := 118140960795 + 5292328 * 2 ^ 59
def prefixEnd_5292328 : Nat := 4983230072969 + 3 ^ 40 * 5292328 * 2
def baseEnd_5292328 : Nat := 301945338360897219562337

theorem tailTrace_5292328 : CollatzResearch.WordTrace tailWord_5292328 prefixEnd_5292328 301945338360897219562337 := by
  unfold tailWord_5292328
  simp only [CollatzResearch.WordTrace]
  refine ⟨96513529985403494253862819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128684706647204659005150425 96513529985403494253862819)
  ·
    refine ⟨144770294978105241380794229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96513529985403494253862819 144770294978105241380794229)
    ·
      refine ⟨13572215154197366379449459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144770294978105241380794229 13572215154197366379449459)
      ·
        refine ⟨20358322731296049569174189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13572215154197366379449459 20358322731296049569174189)
        ·
          refine ⟨7634371024236018588440321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20358322731296049569174189 7634371024236018588440321)
          ·
            refine ⟨5725778268177013941330241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7634371024236018588440321 5725778268177013941330241)
            ·
              refine ⟨4294333701132760455997681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5725778268177013941330241 4294333701132760455997681)
              ·
                refine ⟨3220750275849570341998261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4294333701132760455997681 3220750275849570341998261)
                ·
                  refine ⟨301945338360897219562337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3220750275849570341998261 301945338360897219562337)
                  ·
                    rfl

theorem cell23_5292328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 5].length) (baseStart_5292328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292328 prefixEnd_5292328 := by exact prefixLift 5292328
  have htrace : WordTrace (prefixWord ++ tailWord_5292328) baseStart_5292328 baseEnd_5292328 := by
    simpa [prefixWord, tailWord_5292328, baseEnd_5292328] using wordTrace_append hprefix tailTrace_5292328
  have hstable : (prefixWord ++ tailWord_5292328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292328).length < 2 ^ (prefixWord ++ tailWord_5292328).sum := by decide
  have hdescent : baseEnd_5292328 < baseStart_5292328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292428 : List Nat := [2, 2, 1, 2, 1, 4, 3, 3, 1, 1, 3]
def baseStart_5292428 : Nat := 118140960795 + 5292428 * 2 ^ 59
def prefixEnd_5292428 : Nat := 4983230072969 + 3 ^ 40 * 5292428 * 2
def baseEnd_5292428 : Nat := 2717559393313524584810573

theorem tailTrace_5292428 : CollatzResearch.WordTrace tailWord_5292428 prefixEnd_5292428 2717559393313524584810573 := by
  unfold tailWord_5292428
  simp only [CollatzResearch.WordTrace]
  refine ⟨96515353635222352793182969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128687138180296470390910625 96515353635222352793182969)
  ·
    refine ⟨72386515226416764594887227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96515353635222352793182969 72386515226416764594887227)
    ·
      refine ⟨108579772839625146892330841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72386515226416764594887227 108579772839625146892330841)
      ·
        refine ⟨81434829629718860169248131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108579772839625146892330841 81434829629718860169248131)
        ·
          refine ⟨122152244444578290253872197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81434829629718860169248131 122152244444578290253872197)
          ·
            refine ⟨22903545833358429422601037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122152244444578290253872197 22903545833358429422601037)
            ·
              refine ⟨8588829687509411033475389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22903545833358429422601037 8588829687509411033475389)
              ·
                refine ⟨3220811132816029137553271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8588829687509411033475389 3220811132816029137553271)
                ·
                  refine ⟨4831216699224043706329907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220811132816029137553271 4831216699224043706329907)
                  ·
                    refine ⟨7246825048836065559494861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4831216699224043706329907 7246825048836065559494861)
                    ·
                      refine ⟨2717559393313524584810573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7246825048836065559494861 2717559393313524584810573)
                      ·
                        rfl

theorem cell23_5292428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_5292428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292428 prefixEnd_5292428 := by exact prefixLift 5292428
  have htrace : WordTrace (prefixWord ++ tailWord_5292428) baseStart_5292428 baseEnd_5292428 := by
    simpa [prefixWord, tailWord_5292428, baseEnd_5292428] using wordTrace_append hprefix tailTrace_5292428
  have hstable : (prefixWord ++ tailWord_5292428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292428).length < 2 ^ (prefixWord ++ tailWord_5292428).sum := by decide
  have hdescent : baseEnd_5292428 < baseStart_5292428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292445 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_5292445 : Nat := 118140960795 + 5292445 * 2 ^ 59
def prefixEnd_5292445 : Nat := 4983230072969 + 3 ^ 40 * 5292445 * 2
def baseEnd_5292445 : Nat := 2717568122484651018297995

theorem tailTrace_5292445 : CollatzResearch.WordTrace tailWord_5292445 prefixEnd_5292445 2717568122484651018297995 := by
  unfold tailWord_5292445
  simp only [CollatzResearch.WordTrace]
  refine ⟨193031327311383117489734789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128687551540922078326489859 193031327311383117489734789)
  ·
    refine ⟨36193373870884334529325273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193031327311383117489734789 36193373870884334529325273)
    ·
      refine ⟨27145030403163250896993955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36193373870884334529325273 27145030403163250896993955)
      ·
        refine ⟨40717545604744876345490933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27145030403163250896993955 40717545604744876345490933)
        ·
          refine ⟨3817269900444832157389775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40717545604744876345490933 3817269900444832157389775)
          ·
            refine ⟨5725904850667248236084663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3817269900444832157389775 5725904850667248236084663)
            ·
              refine ⟨8588857276000872354126995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5725904850667248236084663 8588857276000872354126995)
              ·
                refine ⟨12883285914001308531190493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8588857276000872354126995 12883285914001308531190493)
                ·
                  refine ⟨4831232217750490699196435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12883285914001308531190493 4831232217750490699196435)
                  ·
                    refine ⟨7246848326625736048794653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4831232217750490699196435 7246848326625736048794653)
                    ·
                      refine ⟨2717568122484651018297995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7246848326625736048794653 2717568122484651018297995)
                      ·
                        rfl

theorem cell23_5292445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_5292445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292445 prefixEnd_5292445 := by exact prefixLift 5292445
  have htrace : WordTrace (prefixWord ++ tailWord_5292445) baseStart_5292445 baseEnd_5292445 := by
    simpa [prefixWord, tailWord_5292445, baseEnd_5292445] using wordTrace_append hprefix tailTrace_5292445
  have hstable : (prefixWord ++ tailWord_5292445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292445).length < 2 ^ (prefixWord ++ tailWord_5292445).sum := by decide
  have hdescent : baseEnd_5292445 < baseStart_5292445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292447 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 6]
def baseStart_5292447 : Nat := 118140960795 + 5292447 * 2 ^ 59
def prefixEnd_5292447 : Nat := 4983230072969 + 3 ^ 40 * 5292447 * 2
def baseEnd_5292447 : Nat := 2717569149445960010472985

theorem tailTrace_5292447 : CollatzResearch.WordTrace tailWord_5292447 prefixEnd_5292447 2717569149445960010472985 := by
  unfold tailWord_5292447
  simp only [CollatzResearch.WordTrace]
  refine ⟨193031400257375871831307595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128687600171583914554205063 193031400257375871831307595)
  ·
    refine ⟨289547100386063807746961393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193031400257375871831307595 289547100386063807746961393)
    ·
      refine ⟨217160325289547855810221045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289547100386063807746961393 217160325289547855810221045)
      ·
        refine ⟨20358780495895111482208223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 217160325289547855810221045 20358780495895111482208223)
        ·
          refine ⟨30538170743842667223312335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20358780495895111482208223 30538170743842667223312335)
          ·
            refine ⟨45807256115764000834968503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30538170743842667223312335 45807256115764000834968503)
            ·
              refine ⟨68710884173646001252452755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45807256115764000834968503 68710884173646001252452755)
              ·
                refine ⟨103066326260469001878679133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68710884173646001252452755 103066326260469001878679133)
                ·
                  refine ⟨38649872347675875704504675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103066326260469001878679133 38649872347675875704504675)
                  ·
                    refine ⟨57974808521513813556757013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38649872347675875704504675 57974808521513813556757013)
                    ·
                      refine ⟨2717569149445960010472985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57974808521513813556757013 2717569149445960010472985)
                      ·
                        rfl

theorem cell23_5292447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_5292447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292447 prefixEnd_5292447 := by exact prefixLift 5292447
  have htrace : WordTrace (prefixWord ++ tailWord_5292447) baseStart_5292447 baseEnd_5292447 := by
    simpa [prefixWord, tailWord_5292447, baseEnd_5292447] using wordTrace_append hprefix tailTrace_5292447
  have hstable : (prefixWord ++ tailWord_5292447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292447).length < 2 ^ (prefixWord ++ tailWord_5292447).sum := by decide
  have hdescent : baseEnd_5292447 < baseStart_5292447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292471 : List Nat := [1, 1, 3, 1, 3, 3, 3, 2, 1, 2, 3]
def baseStart_5292471 : Nat := 118140960795 + 5292471 * 2 ^ 59
def prefixEnd_5292471 : Nat := 4983230072969 + 3 ^ 40 * 5292471 * 2
def baseEnd_5292471 : Nat := 2717581472981667916572875

theorem tailTrace_5292471 : CollatzResearch.WordTrace tailWord_5292471 prefixEnd_5292471 2717581472981667916572875 := by
  unfold tailWord_5292471
  simp only [CollatzResearch.WordTrace]
  refine ⟨193032275609288923930181267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128688183739525949286787511 193032275609288923930181267)
  ·
    refine ⟨289548413413933385895271901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193032275609288923930181267 289548413413933385895271901)
    ·
      refine ⟨108580655030225019710726963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289548413413933385895271901 108580655030225019710726963)
      ·
        refine ⟨162870982545337529566090445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108580655030225019710726963 162870982545337529566090445)
        ·
          refine ⟨61076618454501573587283917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162870982545337529566090445 61076618454501573587283917)
          ·
            refine ⟨22903731920438090095231469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61076618454501573587283917 22903731920438090095231469)
            ·
              refine ⟨8588899470164283785711801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22903731920438090095231469 8588899470164283785711801)
              ·
                refine ⟨6441674602623212839283851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8588899470164283785711801 6441674602623212839283851)
                ·
                  refine ⟨9662511903934819258925777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6441674602623212839283851 9662511903934819258925777)
                  ·
                    refine ⟨7246883927951114444194333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9662511903934819258925777 7246883927951114444194333)
                    ·
                      refine ⟨2717581472981667916572875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7246883927951114444194333 2717581472981667916572875)
                      ·
                        rfl

theorem cell23_5292471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_5292471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292471 prefixEnd_5292471 := by exact prefixLift 5292471
  have htrace : WordTrace (prefixWord ++ tailWord_5292471) baseStart_5292471 baseEnd_5292471 := by
    simpa [prefixWord, tailWord_5292471, baseEnd_5292471] using wordTrace_append hprefix tailTrace_5292471
  have hstable : (prefixWord ++ tailWord_5292471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292471).length < 2 ^ (prefixWord ++ tailWord_5292471).sum := by decide
  have hdescent : baseEnd_5292471 < baseStart_5292471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292488 : List Nat := [2, 1, 3, 1, 3, 3, 3, 1, 1, 2, 3]
def baseStart_5292488 : Nat := 118140960795 + 5292488 * 2 ^ 59
def prefixEnd_5292488 : Nat := 4983230072969 + 3 ^ 40 * 5292488 * 2
def baseEnd_5292488 : Nat := 2717590202152794350060297

theorem tailTrace_5292488 : CollatzResearch.WordTrace tailWord_5292488 prefixEnd_5292488 2717590202152794350060297 := by
  unfold tailWord_5292488
  simp only [CollatzResearch.WordTrace]
  refine ⟨96516447825113667916775059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128688597100151557222366745 96516447825113667916775059)
  ·
    refine ⟨144774671737670501875162589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96516447825113667916775059 144774671737670501875162589)
    ·
      refine ⟨54290501901626438203185971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144774671737670501875162589 54290501901626438203185971)
      ·
        refine ⟨81435752852439657304778957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54290501901626438203185971 81435752852439657304778957)
        ·
          refine ⟨30538407319664871489292109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81435752852439657304778957 30538407319664871489292109)
          ·
            refine ⟨11451902744874326808484541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30538407319664871489292109 11451902744874326808484541)
            ·
              refine ⟨4294463529327872553181703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11451902744874326808484541 4294463529327872553181703)
              ·
                refine ⟨6441695293991808829772555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4294463529327872553181703 6441695293991808829772555)
                ·
                  refine ⟨9662542940987713244658833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6441695293991808829772555 9662542940987713244658833)
                  ·
                    refine ⟨7246907205740784933494125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9662542940987713244658833 7246907205740784933494125)
                    ·
                      refine ⟨2717590202152794350060297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7246907205740784933494125 2717590202152794350060297)
                      ·
                        rfl

theorem cell23_5292488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_5292488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292488 prefixEnd_5292488 := by exact prefixLift 5292488
  have htrace : WordTrace (prefixWord ++ tailWord_5292488) baseStart_5292488 baseEnd_5292488 := by
    simpa [prefixWord, tailWord_5292488, baseEnd_5292488] using wordTrace_append hprefix tailTrace_5292488
  have hstable : (prefixWord ++ tailWord_5292488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292488).length < 2 ^ (prefixWord ++ tailWord_5292488).sum := by decide
  have hdescent : baseEnd_5292488 < baseStart_5292488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292497 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_5292497 : Nat := 118140960795 + 5292497 * 2 ^ 59
def prefixEnd_5292497 : Nat := 4983230072969 + 3 ^ 40 * 5292497 * 2
def baseEnd_5292497 : Nat := 2717594823478684814847755

theorem tailTrace_5292497 : CollatzResearch.WordTrace tailWord_5292497 prefixEnd_5292497 2717594823478684814847755 := by
  unfold tailWord_5292497
  simp only [CollatzResearch.WordTrace]
  refine ⟨193033223907194730370627745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128688815938129820247085163 193033223907194730370627745)
  ·
    refine ⟨144774917930396047777970809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193033223907194730370627745 144774917930396047777970809)
    ·
      refine ⟨108581188447797035833478107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144774917930396047777970809 108581188447797035833478107)
      ·
        refine ⟨162871782671695553750217161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108581188447797035833478107 162871782671695553750217161)
        ·
          refine ⟨122153837003771665312662871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162871782671695553750217161 122153837003771665312662871)
          ·
            refine ⟨183230755505657497968994307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122153837003771665312662871 183230755505657497968994307)
            ·
              refine ⟨274846133258486246953491461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183230755505657497968994307 274846133258486246953491461)
              ·
                refine ⟨51533649985966171303779649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274846133258486246953491461 51533649985966171303779649)
                ·
                  refine ⟨38650237489474628477834737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51533649985966171303779649 38650237489474628477834737)
                  ·
                    refine ⟨28987678117105971358376053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38650237489474628477834737 28987678117105971358376053)
                    ·
                      refine ⟨2717594823478684814847755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28987678117105971358376053 2717594823478684814847755)
                      ·
                        rfl

theorem cell23_5292497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_5292497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292497 prefixEnd_5292497 := by exact prefixLift 5292497
  have htrace : WordTrace (prefixWord ++ tailWord_5292497) baseStart_5292497 baseEnd_5292497 := by
    simpa [prefixWord, tailWord_5292497, baseEnd_5292497] using wordTrace_append hprefix tailTrace_5292497
  have hstable : (prefixWord ++ tailWord_5292497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292497).length < 2 ^ (prefixWord ++ tailWord_5292497).sum := by decide
  have hdescent : baseEnd_5292497 < baseStart_5292497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292502 : List Nat := [5, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_5292502 : Nat := 118140960795 + 5292502 * 2 ^ 59
def prefixEnd_5292502 : Nat := 4983230072969 + 3 ^ 40 * 5292502 * 2
def baseEnd_5292502 : Nat := 2717597390881957295285233

theorem tailTrace_5292502 : CollatzResearch.WordTrace tailWord_5292502 prefixEnd_5292502 2717597390881957295285233 := by
  unfold tailWord_5292502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12064587892011038514034985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128688937514784410816373173 12064587892011038514034985)
  ·
    refine ⟨9048440919008278885526239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12064587892011038514034985 9048440919008278885526239)
    ·
      refine ⟨13572661378512418328289359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9048440919008278885526239 13572661378512418328289359)
      ·
        refine ⟨20358992067768627492434039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13572661378512418328289359 20358992067768627492434039)
        ·
          refine ⟨30538488101652941238651059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20358992067768627492434039 30538488101652941238651059)
          ·
            refine ⟨45807732152479411857976589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30538488101652941238651059 45807732152479411857976589)
            ·
              refine ⟨17177899557179779446741221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45807732152479411857976589 17177899557179779446741221)
              ·
                refine ⟨3220856166971208646263979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17177899557179779446741221 3220856166971208646263979)
                ·
                  refine ⟨4831284250456812969395969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220856166971208646263979 4831284250456812969395969)
                  ·
                    refine ⟨3623463187842609727046977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4831284250456812969395969 3623463187842609727046977)
                    ·
                      refine ⟨2717597390881957295285233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623463187842609727046977 2717597390881957295285233)
                      ·
                        rfl

theorem cell23_5292502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_5292502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292502 prefixEnd_5292502 := by exact prefixLift 5292502
  have htrace : WordTrace (prefixWord ++ tailWord_5292502) baseStart_5292502 baseEnd_5292502 := by
    simpa [prefixWord, tailWord_5292502, baseEnd_5292502] using wordTrace_append hprefix tailTrace_5292502
  have hstable : (prefixWord ++ tailWord_5292502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292502).length < 2 ^ (prefixWord ++ tailWord_5292502).sum := by decide
  have hdescent : baseEnd_5292502 < baseStart_5292502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292511 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 3, 3, 2]
def baseStart_5292511 : Nat := 118140960795 + 5292511 * 2 ^ 59
def prefixEnd_5292511 : Nat := 4983230072969 + 3 ^ 40 * 5292511 * 2
def baseEnd_5292511 : Nat := 2717602012207847760072691

theorem tailTrace_5292511 : CollatzResearch.WordTrace tailWord_5292511 prefixEnd_5292511 2717602012207847760072691 := by
  unfold tailWord_5292511
  simp only [CollatzResearch.WordTrace]
  refine ⟨193033734529144010761637387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128689156352762673841091591 193033734529144010761637387)
  ·
    refine ⟨289550601793716016142456081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193033734529144010761637387 289550601793716016142456081)
    ·
      refine ⟨217162951345287012106842061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289550601793716016142456081 217162951345287012106842061)
      ·
        refine ⟨81436106754482629540065773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217162951345287012106842061 81436106754482629540065773)
        ·
          refine ⟨30538540032930986077524665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81436106754482629540065773 30538540032930986077524665)
          ·
            refine ⟨22903905024698239558143499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30538540032930986077524665 22903905024698239558143499)
            ·
              refine ⟨34355857537047359337215249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22903905024698239558143499 34355857537047359337215249)
              ·
                refine ⟨25766893152785519502911437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34355857537047359337215249 25766893152785519502911437)
                ·
                  refine ⟨9662584932294569813591789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25766893152785519502911437 9662584932294569813591789)
                  ·
                    refine ⟨3623469349610463680096921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9662584932294569813591789 3623469349610463680096921)
                    ·
                      refine ⟨2717602012207847760072691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623469349610463680096921 2717602012207847760072691)
                      ·
                        rfl

theorem cell23_5292511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_5292511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292511 prefixEnd_5292511 := by exact prefixLift 5292511
  have htrace : WordTrace (prefixWord ++ tailWord_5292511) baseStart_5292511 baseEnd_5292511 := by
    simpa [prefixWord, tailWord_5292511, baseEnd_5292511] using wordTrace_append hprefix tailTrace_5292511
  have hstable : (prefixWord ++ tailWord_5292511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292511).length < 2 ^ (prefixWord ++ tailWord_5292511).sum := by decide
  have hdescent : baseEnd_5292511 < baseStart_5292511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292534 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_5292534 : Nat := 118140960795 + 5292534 * 2 ^ 59
def prefixEnd_5292534 : Nat := 4983230072969 + 3 ^ 40 * 5292534 * 2
def baseEnd_5292534 : Nat := 905871274087633723361695

theorem tailTrace_5292534 : CollatzResearch.WordTrace tailWord_5292534 prefixEnd_5292534 905871274087633723361695 := by
  unfold tailWord_5292534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12064660838003792855607791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128689715605373790459816437 12064660838003792855607791)
  ·
    refine ⟨18096991257005689283411687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12064660838003792855607791 18096991257005689283411687)
    ·
      refine ⟨27145486885508533925117531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18096991257005689283411687 27145486885508533925117531)
      ·
        refine ⟨40718230328262800887676297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27145486885508533925117531 40718230328262800887676297)
        ·
          refine ⟨30538672746197100665757223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40718230328262800887676297 30538672746197100665757223)
          ·
            refine ⟨45808009119295650998635835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30538672746197100665757223 45808009119295650998635835)
            ·
              refine ⟨68712013678943476497953753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45808009119295650998635835 68712013678943476497953753)
              ·
                refine ⟨51534010259207607373465315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68712013678943476497953753 51534010259207607373465315)
                ·
                  refine ⟨77301015388811411060197973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51534010259207607373465315 77301015388811411060197973)
                  ·
                    refine ⟨905871274087633723361695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77301015388811411060197973 905871274087633723361695)
                    ·
                      rfl

theorem cell23_5292534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_5292534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292534 prefixEnd_5292534 := by exact prefixLift 5292534
  have htrace : WordTrace (prefixWord ++ tailWord_5292534) baseStart_5292534 baseEnd_5292534 := by
    simpa [prefixWord, tailWord_5292534, baseEnd_5292534] using wordTrace_append hprefix tailTrace_5292534
  have hstable : (prefixWord ++ tailWord_5292534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292534).length < 2 ^ (prefixWord ++ tailWord_5292534).sum := by decide
  have hdescent : baseEnd_5292534 < baseStart_5292534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292541 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 1, 4, 2]
def baseStart_5292541 : Nat := 118140960795 + 5292541 * 2 ^ 59
def prefixEnd_5292541 : Nat := 4983230072969 + 3 ^ 40 * 5292541 * 2
def baseEnd_5292541 : Nat := 2717617416627482642697553

theorem tailTrace_5292541 : CollatzResearch.WordTrace tailWord_5292541 prefixEnd_5292541 2717617416627482642697553 := by
  unfold tailWord_5292541
  simp only [CollatzResearch.WordTrace]
  refine ⟨193034828719035325885229477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128689885812690217256819651 193034828719035325885229477)
  ·
    refine ⟨36194030384819123603480527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193034828719035325885229477 36194030384819123603480527)
    ·
      refine ⟨54291045577228685405220791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36194030384819123603480527 54291045577228685405220791)
      ·
        refine ⟨81436568365843028107831187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54291045577228685405220791 81436568365843028107831187)
        ·
          refine ⟨122154852548764542161746781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81436568365843028107831187 122154852548764542161746781)
          ·
            refine ⟨45808069705786703310655043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122154852548764542161746781 45808069705786703310655043)
            ·
              refine ⟨68712104558680054965982565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45808069705786703310655043 68712104558680054965982565)
              ·
                refine ⟨12883519604752510306121731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68712104558680054965982565 12883519604752510306121731)
                ·
                  refine ⟨19325279407128765459182597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12883519604752510306121731 19325279407128765459182597)
                  ·
                    refine ⟨3623489888836643523596737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19325279407128765459182597 3623489888836643523596737)
                    ·
                      refine ⟨2717617416627482642697553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623489888836643523596737 2717617416627482642697553)
                      ·
                        rfl

theorem cell23_5292541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_5292541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292541 prefixEnd_5292541 := by exact prefixLift 5292541
  have htrace : WordTrace (prefixWord ++ tailWord_5292541) baseStart_5292541 baseEnd_5292541 := by
    simpa [prefixWord, tailWord_5292541, baseEnd_5292541] using wordTrace_append hprefix tailTrace_5292541
  have hstable : (prefixWord ++ tailWord_5292541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292541).length < 2 ^ (prefixWord ++ tailWord_5292541).sum := by decide
  have hdescent : baseEnd_5292541 < baseStart_5292541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292545 : List Nat := [1, 2, 4, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_5292545 : Nat := 118140960795 + 5292545 * 2 ^ 59
def prefixEnd_5292545 : Nat := 4983230072969 + 3 ^ 40 * 5292545 * 2
def baseEnd_5292545 : Nat := 2717619470550100627047535

theorem tailTrace_5292545 : CollatzResearch.WordTrace tailWord_5292545 prefixEnd_5292545 2717619470550100627047535 := by
  unfold tailWord_5292545
  simp only [CollatzResearch.WordTrace]
  refine ⟨193034974611020834568375089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128689983074013889712250059 193034974611020834568375089)
  ·
    refine ⟨144776230958265625926281317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193034974611020834568375089 144776230958265625926281317)
    ·
      refine ⟨27145543304674804861177747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144776230958265625926281317 27145543304674804861177747)
      ·
        refine ⟨40718314957012207291766621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27145543304674804861177747 40718314957012207291766621)
        ·
          refine ⟨15269368108879577734412483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40718314957012207291766621 15269368108879577734412483)
          ·
            refine ⟨22904052163319366601618725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15269368108879577734412483 22904052163319366601618725)
            ·
              refine ⟨4294509780622381237803511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22904052163319366601618725 4294509780622381237803511)
              ·
                refine ⟨6441764670933571856705267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4294509780622381237803511 6441764670933571856705267)
                ·
                  refine ⟨9662647006400357785057901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6441764670933571856705267 9662647006400357785057901)
                  ·
                    refine ⟨3623492627400134169396713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9662647006400357785057901 3623492627400134169396713)
                    ·
                      refine ⟨2717619470550100627047535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623492627400134169396713 2717619470550100627047535)
                      ·
                        rfl

theorem cell23_5292545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_5292545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292545 prefixEnd_5292545 := by exact prefixLift 5292545
  have htrace : WordTrace (prefixWord ++ tailWord_5292545) baseStart_5292545 baseEnd_5292545 := by
    simpa [prefixWord, tailWord_5292545, baseEnd_5292545] using wordTrace_append hprefix tailTrace_5292545
  have hstable : (prefixWord ++ tailWord_5292545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292545).length < 2 ^ (prefixWord ++ tailWord_5292545).sum := by decide
  have hdescent : baseEnd_5292545 < baseStart_5292545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292547 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 9]
def baseStart_5292547 : Nat := 118140960795 + 5292547 * 2 ^ 59
def prefixEnd_5292547 : Nat := 4983230072969 + 3 ^ 40 * 5292547 * 2
def baseEnd_5292547 : Nat := 301957833056823291024725

theorem tailTrace_5292547 : CollatzResearch.WordTrace tailWord_5292547 prefixEnd_5292547 301957833056823291024725 := by
  unfold tailWord_5292547
  simp only [CollatzResearch.WordTrace]
  refine ⟨193035047557013588909947895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128690031704675725939965263 193035047557013588909947895)
  ·
    refine ⟨289552571335520383364921843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193035047557013588909947895 289552571335520383364921843)
    ·
      refine ⟨434328857003280575047382765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289552571335520383364921843 434328857003280575047382765)
      ·
        refine ⟨162873321376230215642768537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434328857003280575047382765 162873321376230215642768537)
        ·
          refine ⟨122154991032172661732076403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162873321376230215642768537 122154991032172661732076403)
          ·
            refine ⟨183232486548258992598114605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122154991032172661732076403 183232486548258992598114605)
            ·
              refine ⟨68712182455597122224292977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183232486548258992598114605 68712182455597122224292977)
              ·
                refine ⟨51534136841697841668219733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68712182455597122224292977 51534136841697841668219733)
                ·
                  refine ⟨301957833056823291024725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51534136841697841668219733 301957833056823291024725)
                  ·
                    rfl

theorem cell23_5292547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 9].length) (baseStart_5292547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292547 prefixEnd_5292547 := by exact prefixLift 5292547
  have htrace : WordTrace (prefixWord ++ tailWord_5292547) baseStart_5292547 baseEnd_5292547 := by
    simpa [prefixWord, tailWord_5292547, baseEnd_5292547] using wordTrace_append hprefix tailTrace_5292547
  have hstable : (prefixWord ++ tailWord_5292547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292547).length < 2 ^ (prefixWord ++ tailWord_5292547).sum := by decide
  have hdescent : baseEnd_5292547 < baseStart_5292547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292554 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_5292554 : Nat := 118140960795 + 5292554 * 2 ^ 59
def prefixEnd_5292554 : Nat := 4983230072969 + 3 ^ 40 * 5292554 * 2
def baseEnd_5292554 : Nat := 2717624091875991091834993

theorem tailTrace_5292554 : CollatzResearch.WordTrace tailWord_5292554 prefixEnd_5292554 2717624091875991091834993 := by
  unfold tailWord_5292554
  simp only [CollatzResearch.WordTrace]
  refine ⟨48258825716997057276363179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128690201911992152736968477 48258825716997057276363179)
  ·
    refine ⟨72388238575495585914544769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48258825716997057276363179 72388238575495585914544769)
    ·
      refine ⟨54291178931621689435908577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72388238575495585914544769 54291178931621689435908577)
      ·
        refine ⟨40718384198716267076931433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54291178931621689435908577 40718384198716267076931433)
        ·
          refine ⟨30538788149037200307698575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40718384198716267076931433 30538788149037200307698575)
          ·
            refine ⟨45808182223555800461547863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30538788149037200307698575 45808182223555800461547863)
            ·
              refine ⟨68712273335333700692321795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45808182223555800461547863 68712273335333700692321795)
              ·
                refine ⟨103068410003000551038482693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68712273335333700692321795 103068410003000551038482693)
                ·
                  refine ⟨19325326875562603319715505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103068410003000551038482693 19325326875562603319715505)
                  ·
                    refine ⟨14493995156671952489786629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19325326875562603319715505 14493995156671952489786629)
                    ·
                      refine ⟨2717624091875991091834993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14493995156671952489786629 2717624091875991091834993)
                      ·
                        rfl

theorem cell23_5292554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_5292554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292554 prefixEnd_5292554 := by exact prefixLift 5292554
  have htrace : WordTrace (prefixWord ++ tailWord_5292554) baseStart_5292554 baseEnd_5292554 := by
    simpa [prefixWord, tailWord_5292554, baseEnd_5292554] using wordTrace_append hprefix tailTrace_5292554
  have hstable : (prefixWord ++ tailWord_5292554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292554).length < 2 ^ (prefixWord ++ tailWord_5292554).sum := by decide
  have hdescent : baseEnd_5292554 < baseStart_5292554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292594 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_5292594 : Nat := 118140960795 + 5292594 * 2 ^ 59
def prefixEnd_5292594 : Nat := 4983230072969 + 3 ^ 40 * 5292594 * 2
def baseEnd_5292594 : Nat := 905881543700723645111603

theorem tailTrace_5292594 : CollatzResearch.WordTrace tailWord_5292594 prefixEnd_5292594 905881543700723645111603 := by
  unfold tailWord_5292594
  simp only [CollatzResearch.WordTrace]
  refine ⟨48259190446960828984227209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128691174525228877291272557 48259190446960828984227209)
  ·
    refine ⟨36194392835220621738170407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48259190446960828984227209 36194392835220621738170407)
    ·
      refine ⟨54291589252830932607255611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36194392835220621738170407 54291589252830932607255611)
      ·
        refine ⟨81437383879246398910883417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54291589252830932607255611 81437383879246398910883417)
        ·
          refine ⟨61078037909434799183162563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81437383879246398910883417 61078037909434799183162563)
          ·
            refine ⟨91617056864152198774743845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61078037909434799183162563 91617056864152198774743845)
            ·
              refine ⟨17178198162028537270264471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91617056864152198774743845 17178198162028537270264471)
              ·
                refine ⟨25767297243042805905396707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17178198162028537270264471 25767297243042805905396707)
                ·
                  refine ⟨38650945864564208858095061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25767297243042805905396707 38650945864564208858095061)
                  ·
                    refine ⟨905881543700723645111603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38650945864564208858095061 905881543700723645111603)
                    ·
                      rfl

theorem cell23_5292594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_5292594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292594 prefixEnd_5292594 := by exact prefixLift 5292594
  have htrace : WordTrace (prefixWord ++ tailWord_5292594) baseStart_5292594 baseEnd_5292594 := by
    simpa [prefixWord, tailWord_5292594, baseEnd_5292594] using wordTrace_append hprefix tailTrace_5292594
  have hstable : (prefixWord ++ tailWord_5292594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292594).length < 2 ^ (prefixWord ++ tailWord_5292594).sum := by decide
  have hdescent : baseEnd_5292594 < baseStart_5292594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292621 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_5292621 : Nat := 118140960795 + 5292621 * 2 ^ 59
def prefixEnd_5292621 : Nat := 4983230072969 + 3 ^ 40 * 5292621 * 2
def baseEnd_5292621 : Nat := 2717658495079842329697185

theorem tailTrace_5292621 : CollatzResearch.WordTrace tailWord_5292621 prefixEnd_5292621 2717658495079842329697185 := by
  unfold tailWord_5292621
  simp only [CollatzResearch.WordTrace]
  refine ⟨193037746558745499548141717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128691831039163666365427811 193037746558745499548141717)
  ·
    refine ⟨9048644369941195291319143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 193037746558745499548141717 9048644369941195291319143)
    ·
      refine ⟨13572966554911792936978715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9048644369941195291319143 13572966554911792936978715)
      ·
        refine ⟨20359449832367689405468073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13572966554911792936978715 20359449832367689405468073)
        ·
          refine ⟨15269587374275767054101055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20359449832367689405468073 15269587374275767054101055)
          ·
            refine ⟨22904381061413650581151583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15269587374275767054101055 22904381061413650581151583)
            ·
              refine ⟨34356571592120475871727375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22904381061413650581151583 34356571592120475871727375)
              ·
                refine ⟨51534857388180713807591063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34356571592120475871727375 51534857388180713807591063)
                ·
                  refine ⟨77302286082271070711386595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51534857388180713807591063 77302286082271070711386595)
                  ·
                    refine ⟨115953429123406606067079893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77302286082271070711386595 115953429123406606067079893)
                    ·
                      refine ⟨2717658495079842329697185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115953429123406606067079893 2717658495079842329697185)
                      ·
                        rfl

theorem cell23_5292621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_5292621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292621 prefixEnd_5292621 := by exact prefixLift 5292621
  have htrace : WordTrace (prefixWord ++ tailWord_5292621) baseStart_5292621 baseEnd_5292621 := by
    simpa [prefixWord, tailWord_5292621, baseEnd_5292621] using wordTrace_append hprefix tailTrace_5292621
  have hstable : (prefixWord ++ tailWord_5292621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292621).length < 2 ^ (prefixWord ++ tailWord_5292621).sum := by decide
  have hdescent : baseEnd_5292621 < baseStart_5292621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292631 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 1, 6, 2]
def baseStart_5292631 : Nat := 118140960795 + 5292631 * 2 ^ 59
def prefixEnd_5292631 : Nat := 4983230072969 + 3 ^ 40 * 5292631 * 2
def baseEnd_5292631 : Nat := 2717663629886387290572139

theorem tailTrace_5292631 : CollatzResearch.WordTrace tailWord_5292631 prefixEnd_5292631 2717663629886387290572139 := by
  unfold tailWord_5292631
  simp only [CollatzResearch.WordTrace]
  refine ⟨193038111288709271256005747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128692074192472847504003831 193038111288709271256005747)
  ·
    refine ⟨289557166933063906884008621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193038111288709271256005747 289557166933063906884008621)
    ·
      refine ⟨108583937599898965081503233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289557166933063906884008621 108583937599898965081503233)
      ·
        refine ⟨81437953199924223811127425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108583937599898965081503233 81437953199924223811127425)
        ·
          refine ⟨61078464899943167858345569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81437953199924223811127425 61078464899943167858345569)
          ·
            refine ⟨45808848674957375893759177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61078464899943167858345569 45808848674957375893759177)
            ·
              refine ⟨34356636506218031920319383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45808848674957375893759177 34356636506218031920319383)
              ·
                refine ⟨51534954759327047880479075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34356636506218031920319383 51534954759327047880479075)
                ·
                  refine ⟨77302432138990571820718613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51534954759327047880479075 77302432138990571820718613)
                  ·
                    refine ⟨3623551506515183054096185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77302432138990571820718613 3623551506515183054096185)
                    ·
                      refine ⟨2717663629886387290572139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623551506515183054096185 2717663629886387290572139)
                      ·
                        rfl

theorem cell23_5292631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_5292631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292631 prefixEnd_5292631 := by exact prefixLift 5292631
  have htrace : WordTrace (prefixWord ++ tailWord_5292631) baseStart_5292631 baseEnd_5292631 := by
    simpa [prefixWord, tailWord_5292631, baseEnd_5292631] using wordTrace_append hprefix tailTrace_5292631
  have hstable : (prefixWord ++ tailWord_5292631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292631).length < 2 ^ (prefixWord ++ tailWord_5292631).sum := by decide
  have hdescent : baseEnd_5292631 < baseStart_5292631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292675 : List Nat := [1, 1, 1, 3, 3, 1, 6, 2, 1, 4]
def baseStart_5292675 : Nat := 118140960795 + 5292675 * 2 ^ 59
def prefixEnd_5292675 : Nat := 4983230072969 + 3 ^ 40 * 5292675 * 2
def baseEnd_5292675 : Nat := 905895407678395039473979

theorem tailTrace_5292675 : CollatzResearch.WordTrace tailWord_5292675 prefixEnd_5292675 905895407678395039473979 := by
  unfold tailWord_5292675
  simp only [CollatzResearch.WordTrace]
  refine ⟨193039716100549866770607479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128693144067033244513738319 193039716100549866770607479)
  ·
    refine ⟨289559574150824800155911219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193039716100549866770607479 289559574150824800155911219)
    ·
      refine ⟨434339361226237200233866829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289559574150824800155911219 434339361226237200233866829)
      ·
        refine ⟨162877260459838950087700061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434339361226237200233866829 162877260459838950087700061)
        ·
          refine ⟨61078972672439606282887523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162877260459838950087700061 61078972672439606282887523)
          ·
            refine ⟨91618459008659409424331285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61078972672439606282887523 91618459008659409424331285)
            ·
              refine ⟨4294615266030909816765529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91618459008659409424331285 4294615266030909816765529)
              ·
                refine ⟨3220961449523182362574147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4294615266030909816765529 3220961449523182362574147)
                ·
                  refine ⟨4831442174284773543861221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220961449523182362574147 4831442174284773543861221)
                  ·
                    refine ⟨905895407678395039473979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4831442174284773543861221 905895407678395039473979)
                    ·
                      rfl

theorem cell23_5292675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 1, 4].length) (baseStart_5292675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292675 prefixEnd_5292675 := by exact prefixLift 5292675
  have htrace : WordTrace (prefixWord ++ tailWord_5292675) baseStart_5292675 baseEnd_5292675 := by
    simpa [prefixWord, tailWord_5292675, baseEnd_5292675] using wordTrace_append hprefix tailTrace_5292675
  have hstable : (prefixWord ++ tailWord_5292675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292675).length < 2 ^ (prefixWord ++ tailWord_5292675).sum := by decide
  have hdescent : baseEnd_5292675 < baseStart_5292675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292691 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 3, 5, 2]
def baseStart_5292691 : Nat := 118140960795 + 5292691 * 2 ^ 59
def prefixEnd_5292691 : Nat := 4983230072969 + 3 ^ 40 * 5292691 * 2
def baseEnd_5292691 : Nat := 2717694438725657055821863

theorem tailTrace_5292691 : CollatzResearch.WordTrace tailWord_5292691 prefixEnd_5292691 2717694438725657055821863 := by
  unfold tailWord_5292691
  simp only [CollatzResearch.WordTrace]
  refine ⟨193040299668491901503189927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128693533112327934335459951 193040299668491901503189927)
  ·
    refine ⟨289560449502737852254784891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193040299668491901503189927 289560449502737852254784891)
    ·
      refine ⟨434340674254106778382177337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289560449502737852254784891 434340674254106778382177337)
      ·
        refine ⟨325755505690580083786633003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434340674254106778382177337 325755505690580083786633003)
        ·
          refine ⟨488633258535870125679949505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325755505690580083786633003 488633258535870125679949505)
          ·
            refine ⟨366474943901902594259962129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488633258535870125679949505 366474943901902594259962129)
            ·
              refine ⟨274856207926426945694971597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366474943901902594259962129 274856207926426945694971597)
              ·
                refine ⟨103071077972410104635614349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274856207926426945694971597 103071077972410104635614349)
                ·
                  refine ⟨38651654239653789238355381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103071077972410104635614349 38651654239653789238355381)
                  ·
                    refine ⟨3623592584967542741095817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38651654239653789238355381 3623592584967542741095817)
                    ·
                      refine ⟨2717694438725657055821863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623592584967542741095817 2717694438725657055821863)
                      ·
                        rfl

theorem cell23_5292691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 5, 2].length) (baseStart_5292691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292691 prefixEnd_5292691 := by exact prefixLift 5292691
  have htrace : WordTrace (prefixWord ++ tailWord_5292691) baseStart_5292691 baseEnd_5292691 := by
    simpa [prefixWord, tailWord_5292691, baseEnd_5292691] using wordTrace_append hprefix tailTrace_5292691
  have hstable : (prefixWord ++ tailWord_5292691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292691).length < 2 ^ (prefixWord ++ tailWord_5292691).sum := by decide
  have hdescent : baseEnd_5292691 < baseStart_5292691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292701 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_5292701 : Nat := 118140960795 + 5292701 * 2 ^ 59
def prefixEnd_5292701 : Nat := 4983230072969 + 3 ^ 40 * 5292701 * 2
def baseEnd_5292701 : Nat := 905899857844067338898939

theorem tailTrace_5292701 : CollatzResearch.WordTrace tailWord_5292701 prefixEnd_5292701 905899857844067338898939 := by
  unfold tailWord_5292701
  simp only [CollatzResearch.WordTrace]
  refine ⟨193040664398455673211053957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128693776265637115474035971 193040664398455673211053957)
  ·
    refine ⟨36195124574710438727072617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193040664398455673211053957 36195124574710438727072617)
    ·
      refine ⟨27146343431032829045304463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36195124574710438727072617 27146343431032829045304463)
      ·
        refine ⟨40719515146549243567956695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27146343431032829045304463 40719515146549243567956695)
        ·
          refine ⟨61079272719823865351935043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40719515146549243567956695 61079272719823865351935043)
          ·
            refine ⟨91618909079735798027902565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61079272719823865351935043 91618909079735798027902565)
            ·
              refine ⟨17178545452450462130231731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91618909079735798027902565 17178545452450462130231731)
              ·
                refine ⟨25767818178675693195347597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17178545452450462130231731 25767818178675693195347597)
                ·
                  refine ⟨9662931817003384948255349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25767818178675693195347597 9662931817003384948255349)
                  ·
                    refine ⟨905899857844067338898939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9662931817003384948255349 905899857844067338898939)
                    ·
                      rfl

theorem cell23_5292701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_5292701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292701 prefixEnd_5292701 := by exact prefixLift 5292701
  have htrace : WordTrace (prefixWord ++ tailWord_5292701) baseStart_5292701 baseEnd_5292701 := by
    simpa [prefixWord, tailWord_5292701, baseEnd_5292701] using wordTrace_append hprefix tailTrace_5292701
  have hstable : (prefixWord ++ tailWord_5292701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292701).length < 2 ^ (prefixWord ++ tailWord_5292701).sum := by decide
  have hdescent : baseEnd_5292701 < baseStart_5292701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292708 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 1, 5, 2]
def baseStart_5292708 : Nat := 118140960795 + 5292708 * 2 ^ 59
def prefixEnd_5292708 : Nat := 4983230072969 + 3 ^ 40 * 5292708 * 2
def baseEnd_5292708 : Nat := 2717703167896783489309285

theorem tailTrace_5292708 : CollatzResearch.WordTrace tailWord_5292708 prefixEnd_5292708 2717703167896783489309285 := by
  unfold tailWord_5292708
  simp only [CollatzResearch.WordTrace]
  refine ⟨96520459854715156703279389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128693946472953542271039185 96520459854715156703279389)
  ·
    refine ⟨36195172445518183763729771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96520459854715156703279389 36195172445518183763729771)
    ·
      refine ⟨54292758668277275645594657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36195172445518183763729771 54292758668277275645594657)
      ·
        refine ⟨40719569001207956734195993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54292758668277275645594657 40719569001207956734195993)
        ·
          refine ⟨30539676750905967550646995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40719569001207956734195993 30539676750905967550646995)
          ·
            refine ⟨45809515126358951325970493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30539676750905967550646995 45809515126358951325970493)
            ·
              refine ⟨17178568172384606747238935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45809515126358951325970493 17178568172384606747238935)
              ·
                refine ⟨25767852258576910120858403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17178568172384606747238935 25767852258576910120858403)
                ·
                  refine ⟨38651778387865365181287605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25767852258576910120858403 38651778387865365181287605)
                  ·
                    refine ⟨3623604223862377985745713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38651778387865365181287605 3623604223862377985745713)
                    ·
                      refine ⟨2717703167896783489309285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623604223862377985745713 2717703167896783489309285)
                      ·
                        rfl

theorem cell23_5292708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_5292708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292708 prefixEnd_5292708 := by exact prefixLift 5292708
  have htrace : WordTrace (prefixWord ++ tailWord_5292708) baseStart_5292708 baseEnd_5292708 := by
    simpa [prefixWord, tailWord_5292708, baseEnd_5292708] using wordTrace_append hprefix tailTrace_5292708
  have hstable : (prefixWord ++ tailWord_5292708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292708).length < 2 ^ (prefixWord ++ tailWord_5292708).sum := by decide
  have hdescent : baseEnd_5292708 < baseStart_5292708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292748 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 1, 6]
def baseStart_5292748 : Nat := 118140960795 + 5292748 * 2 ^ 59
def prefixEnd_5292748 : Nat := 4983230072969 + 3 ^ 40 * 5292748 * 2
def baseEnd_5292748 : Nat := 905907902374321110936367

theorem tailTrace_5292748 : CollatzResearch.WordTrace tailWord_5292748 prefixEnd_5292748 905907902374321110936367 := by
  unfold tailWord_5292748
  simp only [CollatzResearch.WordTrace]
  refine ⟨96521189314642700119007449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128694919086190266825343265 96521189314642700119007449)
  ·
    refine ⟨72390891985982025089255587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96521189314642700119007449 72390891985982025089255587)
    ·
      refine ⟨108586337978973037633883381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72390891985982025089255587 108586337978973037633883381)
      ·
        refine ⟨10179969185528722278176567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108586337978973037633883381 10179969185528722278176567)
        ·
          refine ⟨15269953778293083417264851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10179969185528722278176567 15269953778293083417264851)
          ·
            refine ⟨22904930667439625125897277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15269953778293083417264851 22904930667439625125897277)
            ·
              refine ⟨8589349000289859422211479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22904930667439625125897277 8589349000289859422211479)
              ·
                refine ⟨12884023500434789133317219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8589349000289859422211479 12884023500434789133317219)
                ·
                  refine ⟨19326035250652183699975829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12884023500434789133317219 19326035250652183699975829)
                  ·
                    refine ⟨905907902374321110936367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19326035250652183699975829 905907902374321110936367)
                    ·
                      rfl

theorem cell23_5292748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_5292748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292748 prefixEnd_5292748 := by exact prefixLift 5292748
  have htrace : WordTrace (prefixWord ++ tailWord_5292748) baseStart_5292748 baseEnd_5292748 := by
    simpa [prefixWord, tailWord_5292748, baseEnd_5292748] using wordTrace_append hprefix tailTrace_5292748
  have hstable : (prefixWord ++ tailWord_5292748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292748).length < 2 ^ (prefixWord ++ tailWord_5292748).sum := by decide
  have hdescent : baseEnd_5292748 < baseStart_5292748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292841 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 4, 2, 4]
def baseStart_5292841 : Nat := 118140960795 + 5292841 * 2 ^ 59
def prefixEnd_5292841 : Nat := 4983230072969 + 3 ^ 40 * 5292841 * 2
def baseEnd_5292841 : Nat := 2717771460823831468946173

theorem tailTrace_5292841 : CollatzResearch.WordTrace tailWord_5292841 prefixEnd_5292841 2717771460823831468946173 := by
  unfold tailWord_5292841
  simp only [CollatzResearch.WordTrace]
  refine ⟨193045770617948477121150377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128697180411965651414100251 193045770617948477121150377)
  ·
    refine ⟨144784327963461357840862783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193045770617948477121150377 144784327963461357840862783)
    ·
      refine ⟨217176491945192036761294175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144784327963461357840862783 217176491945192036761294175)
      ·
        refine ⟨325764737917788055141941263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217176491945192036761294175 325764737917788055141941263)
        ·
          refine ⟨488647106876682082712911895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325764737917788055141941263 488647106876682082712911895)
          ·
            refine ⟨732970660315023124069367843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488647106876682082712911895 732970660315023124069367843)
            ·
              refine ⟨1099455990472534686104051765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732970660315023124069367843 1099455990472534686104051765)
              ·
                refine ⟨103073999106800126822254853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1099455990472534686104051765 103073999106800126822254853)
                ·
                  refine ⟨19326374832525023779172785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103073999106800126822254853 19326374832525023779172785)
                  ·
                    refine ⟨14494781124393767834379589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19326374832525023779172785 14494781124393767834379589)
                    ·
                      refine ⟨2717771460823831468946173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14494781124393767834379589 2717771460823831468946173)
                      ·
                        rfl

theorem cell23_5292841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_5292841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292841 prefixEnd_5292841 := by exact prefixLift 5292841
  have htrace : WordTrace (prefixWord ++ tailWord_5292841) baseStart_5292841 baseEnd_5292841 := by
    simpa [prefixWord, tailWord_5292841, baseEnd_5292841] using wordTrace_append hprefix tailTrace_5292841
  have hstable : (prefixWord ++ tailWord_5292841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292841).length < 2 ^ (prefixWord ++ tailWord_5292841).sum := by decide
  have hdescent : baseEnd_5292841 < baseStart_5292841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292885 : List Nat := [1, 3, 2, 2, 2, 1, 4, 3, 5]
def baseStart_5292885 : Nat := 118140960795 + 5292885 * 2 ^ 59
def prefixEnd_5292885 : Nat := 4983230072969 + 3 ^ 40 * 5292885 * 2
def baseEnd_5292885 : Nat := 301977117108069921866219

theorem tailTrace_5292885 : CollatzResearch.WordTrace tailWord_5292885 prefixEnd_5292885 301977117108069921866219 := by
  unfold tailWord_5292885
  simp only [CollatzResearch.WordTrace]
  refine ⟨193047375429789072635752109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128698250286526048423834739 193047375429789072635752109)
  ·
    refine ⟨72392765786170902238407041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193047375429789072635752109 72392765786170902238407041)
    ·
      refine ⟨54294574339628176678805281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72392765786170902238407041 54294574339628176678805281)
      ·
        refine ⟨40720930754721132509103961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54294574339628176678805281 40720930754721132509103961)
        ·
          refine ⟨30540698066040849381827971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40720930754721132509103961 30540698066040849381827971)
          ·
            refine ⟨45811047099061274072741957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30540698066040849381827971 45811047099061274072741957)
            ·
              refine ⟨8589571331073988888639117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45811047099061274072741957 8589571331073988888639117)
              ·
                refine ⟨3221089249152745833239669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8589571331073988888639117 3221089249152745833239669)
                ·
                  refine ⟨301977117108069921866219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3221089249152745833239669 301977117108069921866219)
                  ·
                    rfl

theorem cell23_5292885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_5292885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292885 prefixEnd_5292885 := by exact prefixLift 5292885
  have htrace : WordTrace (prefixWord ++ tailWord_5292885) baseStart_5292885 baseEnd_5292885 := by
    simpa [prefixWord, tailWord_5292885, baseEnd_5292885] using wordTrace_append hprefix tailTrace_5292885
  have hstable : (prefixWord ++ tailWord_5292885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292885).length < 2 ^ (prefixWord ++ tailWord_5292885).sum := by decide
  have hdescent : baseEnd_5292885 < baseStart_5292885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292928 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 5, 4]
def baseStart_5292928 : Nat := 118140960795 + 5292928 * 2 ^ 59
def prefixEnd_5292928 : Nat := 4983230072969 + 3 ^ 40 * 5292928 * 2
def baseEnd_5292928 : Nat := 905938711213590876186091

theorem tailTrace_5292928 : CollatzResearch.WordTrace tailWord_5292928 prefixEnd_5292928 905938711213590876186091 := by
  unfold tailWord_5292928
  simp only [CollatzResearch.WordTrace]
  refine ⟨96524471884316645489783719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128699295845755527319711625 96524471884316645489783719)
  ·
    refine ⟨144786707826474968234675579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96524471884316645489783719 144786707826474968234675579)
    ·
      refine ⟨217180061739712452352013369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144786707826474968234675579 217180061739712452352013369)
      ·
        refine ⟨162885046304784339264010027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217180061739712452352013369 162885046304784339264010027)
        ·
          refine ⟨244327569457176508896015041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162885046304784339264010027 244327569457176508896015041)
          ·
            refine ⟨183245677092882381672011281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244327569457176508896015041 183245677092882381672011281)
            ·
              refine ⟨137434257819661786254008461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183245677092882381672011281 137434257819661786254008461)
              ·
                refine ⟨51537846682373169845253173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137434257819661786254008461 51537846682373169845253173)
                ·
                  refine ⟨4831673126472484672992485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51537846682373169845253173 4831673126472484672992485)
                  ·
                    refine ⟨905938711213590876186091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4831673126472484672992485 905938711213590876186091)
                    ·
                      rfl

theorem cell23_5292928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 5, 4].length) (baseStart_5292928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292928 prefixEnd_5292928 := by exact prefixLift 5292928
  have htrace : WordTrace (prefixWord ++ tailWord_5292928) baseStart_5292928 baseEnd_5292928 := by
    simpa [prefixWord, tailWord_5292928, baseEnd_5292928] using wordTrace_append hprefix tailTrace_5292928
  have hstable : (prefixWord ++ tailWord_5292928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292928).length < 2 ^ (prefixWord ++ tailWord_5292928).sum := by decide
  have hdescent : baseEnd_5292928 < baseStart_5292928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292962 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_5292962 : Nat := 118140960795 + 5292962 * 2 ^ 59
def prefixEnd_5292962 : Nat := 4983230072969 + 3 ^ 40 * 5292962 * 2
def baseEnd_5292962 : Nat := 905944530661008498511039

theorem tailTrace_5292962 : CollatzResearch.WordTrace tailWord_5292962 prefixEnd_5292962 905944530661008498511039 := by
  unfold tailWord_5292962
  simp only [CollatzResearch.WordTrace]
  refine ⟨48262545962627528696576285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128700122567006743190870093 48262545962627528696576285)
  ·
    refine ⟨18098454735985323261216107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48262545962627528696576285 18098454735985323261216107)
    ·
      refine ⟨27147682103977984891824161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18098454735985323261216107 27147682103977984891824161)
      ·
        refine ⟨20360761577983488668868121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27147682103977984891824161 20360761577983488668868121)
        ·
          refine ⟨15270571183487616501651091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20360761577983488668868121 15270571183487616501651091)
          ·
            refine ⟨22905856775231424752476637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15270571183487616501651091 22905856775231424752476637)
            ·
              refine ⟨8589696290711784282178739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22905856775231424752476637 8589696290711784282178739)
              ·
                refine ⟨12884544436067676423268109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8589696290711784282178739 12884544436067676423268109)
                ·
                  refine ⟨4831704163525378658725541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12884544436067676423268109 4831704163525378658725541)
                  ·
                    refine ⟨905944530661008498511039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4831704163525378658725541 905944530661008498511039)
                    ·
                      rfl

theorem cell23_5292962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_5292962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292962 prefixEnd_5292962 := by exact prefixLift 5292962
  have htrace : WordTrace (prefixWord ++ tailWord_5292962) baseStart_5292962 baseEnd_5292962 := by
    simpa [prefixWord, tailWord_5292962, baseEnd_5292962] using wordTrace_append hprefix tailTrace_5292962
  have hstable : (prefixWord ++ tailWord_5292962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292962).length < 2 ^ (prefixWord ++ tailWord_5292962).sum := by decide
  have hdescent : baseEnd_5292962 < baseStart_5292962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5292995 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 6, 3, 2]
def baseStart_5292995 : Nat := 118140960795 + 5292995 * 2 ^ 59
def prefixEnd_5292995 : Nat := 4983230072969 + 3 ^ 40 * 5292995 * 2
def baseEnd_5292995 : Nat := 2717850536844623866420465

theorem tailTrace_5292995 : CollatzResearch.WordTrace tailWord_5292995 prefixEnd_5292995 2717850536844623866420465 := by
  unfold tailWord_5292995
  simp only [CollatzResearch.WordTrace]
  refine ⟨193051387459390561422256439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128700924972927040948170959 193051387459390561422256439)
  ·
    refine ⟨289577081189085842133384659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193051387459390561422256439 289577081189085842133384659)
    ·
      refine ⟨434365621783628763200076989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289577081189085842133384659 434365621783628763200076989)
      ·
        refine ⟨162887108168860786200028871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434365621783628763200076989 162887108168860786200028871)
        ·
          refine ⟨244330662253291179300043307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162887108168860786200028871 244330662253291179300043307)
          ·
            refine ⟨366495993379936768950064961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244330662253291179300043307 366495993379936768950064961)
            ·
              refine ⟨274871995034952576712548721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366495993379936768950064961 274871995034952576712548721)
              ·
                refine ⟨206153996276214432534411541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274871995034952576712548721 206153996276214432534411541)
                ·
                  refine ⟨9663468575447551525050541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 206153996276214432534411541 9663468575447551525050541)
                  ·
                    refine ⟨3623800715792831821893953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9663468575447551525050541 3623800715792831821893953)
                    ·
                      refine ⟨2717850536844623866420465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623800715792831821893953 2717850536844623866420465)
                      ·
                        rfl

theorem cell23_5292995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 3, 2].length) (baseStart_5292995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5292995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5292995 prefixEnd_5292995 := by exact prefixLift 5292995
  have htrace : WordTrace (prefixWord ++ tailWord_5292995) baseStart_5292995 baseEnd_5292995 := by
    simpa [prefixWord, tailWord_5292995, baseEnd_5292995] using wordTrace_append hprefix tailTrace_5292995
  have hstable : (prefixWord ++ tailWord_5292995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5292995).length < 2 ^ (prefixWord ++ tailWord_5292995).sum := by decide
  have hdescent : baseEnd_5292995 < baseStart_5292995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5292995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293013 : List Nat := [1, 3, 2, 3, 4, 1, 2, 2, 1, 4]
def baseStart_5293013 : Nat := 118140960795 + 5293013 * 2 ^ 59
def prefixEnd_5293013 : Nat := 4983230072969 + 3 ^ 40 * 5293013 * 2
def baseEnd_5293013 : Nat := 905953259832134931998461

theorem tailTrace_5293013 : CollatzResearch.WordTrace tailWord_5293013 prefixEnd_5293013 905953259832134931998461 := by
  unfold tailWord_5293013
  simp only [CollatzResearch.WordTrace]
  refine ⟨193052043973325350496411693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128701362648883566997607795 193052043973325350496411693)
  ·
    refine ⟨72394516489997006436154385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193052043973325350496411693 72394516489997006436154385)
    ·
      refine ⟨54295887367497754827115789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72394516489997006436154385 54295887367497754827115789)
      ·
        refine ⟨20360957762811658060168421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54295887367497754827115789 20360957762811658060168421)
        ·
          refine ⟨3817679580527185886281579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20360957762811658060168421 3817679580527185886281579)
          ·
            refine ⟨5726519370790778829422369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3817679580527185886281579 5726519370790778829422369)
            ·
              refine ⟨4294889528093084122066777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5726519370790778829422369 4294889528093084122066777)
              ·
                refine ⟨3221167146069813091550083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4294889528093084122066777 3221167146069813091550083)
                ·
                  refine ⟨4831750719104719637325125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221167146069813091550083 4831750719104719637325125)
                  ·
                    refine ⟨905953259832134931998461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4831750719104719637325125 905953259832134931998461)
                    ·
                      rfl

theorem cell23_5293013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_5293013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293013 prefixEnd_5293013 := by exact prefixLift 5293013
  have htrace : WordTrace (prefixWord ++ tailWord_5293013) baseStart_5293013 baseEnd_5293013 := by
    simpa [prefixWord, tailWord_5293013, baseEnd_5293013] using wordTrace_append hprefix tailTrace_5293013
  have hstable : (prefixWord ++ tailWord_5293013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293013).length < 2 ^ (prefixWord ++ tailWord_5293013).sum := by decide
  have hdescent : baseEnd_5293013 < baseStart_5293013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293025 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 2, 6, 2]
def baseStart_5293025 : Nat := 118140960795 + 5293025 * 2 ^ 59
def prefixEnd_5293025 : Nat := 4983230072969 + 3 ^ 40 * 5293025 * 2
def baseEnd_5293025 : Nat := 2717865941264258749045327

theorem tailTrace_5293025 : CollatzResearch.WordTrace tailWord_5293025 prefixEnd_5293025 2717865941264258749045327 := by
  unfold tailWord_5293025
  simp only [CollatzResearch.WordTrace]
  refine ⟨193052481649281876545848529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128701654432854584363899019 193052481649281876545848529)
  ·
    refine ⟨144789361236961407409386397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193052481649281876545848529 144789361236961407409386397)
    ·
      refine ⟨54296010463860527778519899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144789361236961407409386397 54296010463860527778519899)
      ·
        refine ⟨81444015695790791667779849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54296010463860527778519899 81444015695790791667779849)
        ·
          refine ⟨61083011771843093750834887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81444015695790791667779849 61083011771843093750834887)
          ·
            refine ⟨91624517657764640626252331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61083011771843093750834887 91624517657764640626252331)
            ·
              refine ⟨137436776486646960939378497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91624517657764640626252331 137436776486646960939378497)
              ·
                refine ⟨103077582364985220704533873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137436776486646960939378497 103077582364985220704533873)
                ·
                  refine ⟨77308186773738915528400405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103077582364985220704533873 77308186773738915528400405)
                  ·
                    refine ⟨3623821255019011665393769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77308186773738915528400405 3623821255019011665393769)
                    ·
                      refine ⟨2717865941264258749045327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623821255019011665393769 2717865941264258749045327)
                      ·
                        rfl

theorem cell23_5293025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_5293025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293025 prefixEnd_5293025 := by exact prefixLift 5293025
  have htrace : WordTrace (prefixWord ++ tailWord_5293025) baseStart_5293025 baseEnd_5293025 := by
    simpa [prefixWord, tailWord_5293025, baseEnd_5293025] using wordTrace_append hprefix tailTrace_5293025
  have hstable : (prefixWord ++ tailWord_5293025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293025).length < 2 ^ (prefixWord ++ tailWord_5293025).sum := by decide
  have hdescent : baseEnd_5293025 < baseStart_5293025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293046 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_5293046 : Nat := 118140960795 + 5293046 * 2 ^ 59
def prefixEnd_5293046 : Nat := 4983230072969 + 3 ^ 40 * 5293046 * 2
def baseEnd_5293046 : Nat := 2717876724358003166882731

theorem tailTrace_5293046 : CollatzResearch.WordTrace tailWord_5293046 prefixEnd_5293046 2717876724358003166882731 := by
  unfold tailWord_5293046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12065827973887862320772687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128702165054803864754908661 12065827973887862320772687)
  ·
    refine ⟨18098741960831793481159031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12065827973887862320772687 18098741960831793481159031)
    ·
      refine ⟨27148112941247690221738547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18098741960831793481159031 27148112941247690221738547)
      ·
        refine ⟨40722169411871535332607821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27148112941247690221738547 40722169411871535332607821)
        ·
          refine ⟨15270813529451825749727933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40722169411871535332607821 15270813529451825749727933)
          ·
            refine ⟨5726555073544434656147975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15270813529451825749727933 5726555073544434656147975)
            ·
              refine ⟨8589832610316651984221963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5726555073544434656147975 8589832610316651984221963)
              ·
                refine ⟨12884748915474977976332945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8589832610316651984221963 12884748915474977976332945)
                ·
                  refine ⟨9663561686606233482249709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12884748915474977976332945 9663561686606233482249709)
                  ·
                    refine ⟨3623835632477337555843641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9663561686606233482249709 3623835632477337555843641)
                    ·
                      refine ⟨2717876724358003166882731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623835632477337555843641 2717876724358003166882731)
                      ·
                        rfl

theorem cell23_5293046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_5293046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293046 prefixEnd_5293046 := by exact prefixLift 5293046
  have htrace : WordTrace (prefixWord ++ tailWord_5293046) baseStart_5293046 baseEnd_5293046 := by
    simpa [prefixWord, tailWord_5293046, baseEnd_5293046] using wordTrace_append hprefix tailTrace_5293046
  have hstable : (prefixWord ++ tailWord_5293046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293046).length < 2 ^ (prefixWord ++ tailWord_5293046).sum := by decide
  have hdescent : baseEnd_5293046 < baseStart_5293046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293110 : List Nat := [5, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_5293110 : Nat := 118140960795 + 5293110 * 2 ^ 59
def prefixEnd_5293110 : Nat := 4983230072969 + 3 ^ 40 * 5293110 * 2
def baseEnd_5293110 : Nat := 2717909587119890916482437

theorem tailTrace_5293110 : CollatzResearch.WordTrace tailWord_5293110 prefixEnd_5293110 2717909587119890916482437 := by
  unfold tailWord_5293110
  simp only [CollatzResearch.WordTrace]
  refine ⟨12065973865873371003918299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128703721235982624041795189 12065973865873371003918299)
  ·
    refine ⟨18098960798810056505877449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12065973865873371003918299 18098960798810056505877449)
    ·
      refine ⟨13574220599107542379408087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18098960798810056505877449 13574220599107542379408087)
      ·
        refine ⟨20361330898661313569112131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13574220599107542379408087 20361330898661313569112131)
        ·
          refine ⟨30541996347991970353668197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20361330898661313569112131 30541996347991970353668197)
          ·
            refine ⟨5726624315248494441312787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30541996347991970353668197 5726624315248494441312787)
            ·
              refine ⟨8589936472872741661969181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5726624315248494441312787 8589936472872741661969181)
              ·
                refine ⟨3221226177327278123238443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8589936472872741661969181 3221226177327278123238443)
                ·
                  refine ⟨4831839265990917184857665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221226177327278123238443 4831839265990917184857665)
                  ·
                    refine ⟨3623879449493187888643249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4831839265990917184857665 3623879449493187888643249)
                    ·
                      refine ⟨2717909587119890916482437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3623879449493187888643249 2717909587119890916482437)
                      ·
                        rfl

theorem cell23_5293110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_5293110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293110 prefixEnd_5293110 := by exact prefixLift 5293110
  have htrace : WordTrace (prefixWord ++ tailWord_5293110) baseStart_5293110 baseEnd_5293110 := by
    simpa [prefixWord, tailWord_5293110, baseEnd_5293110] using wordTrace_append hprefix tailTrace_5293110
  have hstable : (prefixWord ++ tailWord_5293110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293110).length < 2 ^ (prefixWord ++ tailWord_5293110).sum := by decide
  have hdescent : baseEnd_5293110 < baseStart_5293110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293126 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_5293126 : Nat := 118140960795 + 5293126 * 2 ^ 59
def prefixEnd_5293126 : Nat := 4983230072969 + 3 ^ 40 * 5293126 * 2
def baseEnd_5293126 : Nat := 2717917802810362853882363

theorem tailTrace_5293126 : CollatzResearch.WordTrace tailWord_5293126 prefixEnd_5293126 2717917802810362853882363 := by
  unfold tailWord_5293126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6033005169434874087352351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 128704110281277313863516821 6033005169434874087352351)
  ·
    refine ⟨9049507754152311131028527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6033005169434874087352351 9049507754152311131028527)
    ·
      refine ⟨13574261631228466696542791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9049507754152311131028527 13574261631228466696542791)
      ·
        refine ⟨20361392446842700044814187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13574261631228466696542791 20361392446842700044814187)
        ·
          refine ⟨30542088670264050067221281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20361392446842700044814187 30542088670264050067221281)
          ·
            refine ⟨22906566502698037550415961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30542088670264050067221281 22906566502698037550415961)
            ·
              refine ⟨17179924877023528162811971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22906566502698037550415961 17179924877023528162811971)
              ·
                refine ⟨25769887315535292244217957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17179924877023528162811971 25769887315535292244217957)
                ·
                  refine ⟨4831853871662867295790867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25769887315535292244217957 4831853871662867295790867)
                  ·
                    refine ⟨7247780807494300943686301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4831853871662867295790867 7247780807494300943686301)
                    ·
                      refine ⟨2717917802810362853882363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7247780807494300943686301 2717917802810362853882363)
                      ·
                        rfl

theorem cell23_5293126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_5293126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293126 prefixEnd_5293126 := by exact prefixLift 5293126
  have htrace : WordTrace (prefixWord ++ tailWord_5293126) baseStart_5293126 baseEnd_5293126 := by
    simpa [prefixWord, tailWord_5293126, baseEnd_5293126] using wordTrace_append hprefix tailTrace_5293126
  have hstable : (prefixWord ++ tailWord_5293126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293126).length < 2 ^ (prefixWord ++ tailWord_5293126).sum := by decide
  have hdescent : baseEnd_5293126 < baseStart_5293126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293189 : List Nat := [1, 3, 1, 1, 6, 1, 1, 4, 5]
def baseStart_5293189 : Nat := 118140960795 + 5293189 * 2 ^ 59
def prefixEnd_5293189 : Nat := 4983230072969 + 3 ^ 40 * 5293189 * 2
def baseEnd_5293189 : Nat := 301994461343510678599397

theorem tailTrace_5293189 : CollatzResearch.WordTrace tailWord_5293189 prefixEnd_5293189 301994461343510678599397 := by
  unfold tailWord_5293189
  simp only [CollatzResearch.WordTrace]
  refine ⟨193058463220687732554818621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128705642147125155036545747 193058463220687732554818621)
  ·
    refine ⟨72396923707757899708056983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193058463220687732554818621 72396923707757899708056983)
    ·
      refine ⟨108595385561636849562085475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72396923707757899708056983 108595385561636849562085475)
      ·
        refine ⟨162893078342455274343128213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108595385561636849562085475 162893078342455274343128213)
        ·
          refine ⟨7635613047302590984834135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 162893078342455274343128213 7635613047302590984834135)
          ·
            refine ⟨11453419570953886477251203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7635613047302590984834135 11453419570953886477251203)
            ·
              refine ⟨17180129356430829715876805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11453419570953886477251203 17180129356430829715876805)
              ·
                refine ⟨3221274254330780571726901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17180129356430829715876805 3221274254330780571726901)
                ·
                  refine ⟨301994461343510678599397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3221274254330780571726901 301994461343510678599397)
                  ·
                    rfl

theorem cell23_5293189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_5293189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293189 prefixEnd_5293189 := by exact prefixLift 5293189
  have htrace : WordTrace (prefixWord ++ tailWord_5293189) baseStart_5293189 baseEnd_5293189 := by
    simpa [prefixWord, tailWord_5293189, baseEnd_5293189] using wordTrace_append hprefix tailTrace_5293189
  have hstable : (prefixWord ++ tailWord_5293189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293189).length < 2 ^ (prefixWord ++ tailWord_5293189).sum := by decide
  have hdescent : baseEnd_5293189 < baseStart_5293189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293235 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 6]
def baseStart_5293235 : Nat := 118140960795 + 5293235 * 2 ^ 59
def prefixEnd_5293235 : Nat := 4983230072969 + 3 ^ 40 * 5293235 * 2
def baseEnd_5293235 : Nat := 2717973772201702927419361

theorem tailTrace_5293235 : CollatzResearch.WordTrace tailWord_5293235 prefixEnd_5293235 2717973772201702927419361 := by
  unfold tailWord_5293235
  simp only [CollatzResearch.WordTrace]
  refine ⟨193060140978521082410993159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128706760652347388273995439 193060140978521082410993159)
  ·
    refine ⟨289590211467781623616489739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193060140978521082410993159 289590211467781623616489739)
    ·
      refine ⟨434385317201672435424734609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289590211467781623616489739 434385317201672435424734609)
      ·
        refine ⟨325788987901254326568550957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434385317201672435424734609 325788987901254326568550957)
        ·
          refine ⟨122170870462970372463206609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325788987901254326568550957 122170870462970372463206609)
          ·
            refine ⟨91628152847227779347404957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122170870462970372463206609 91628152847227779347404957)
            ·
              refine ⟨34360557317710417255276859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91628152847227779347404957 34360557317710417255276859)
              ·
                refine ⟨51540835976565625882915289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34360557317710417255276859 51540835976565625882915289)
                ·
                  refine ⟨38655626982424219412186467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51540835976565625882915289 38655626982424219412186467)
                  ·
                    refine ⟨57983440473636329118279701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38655626982424219412186467 57983440473636329118279701)
                    ·
                      refine ⟨2717973772201702927419361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57983440473636329118279701 2717973772201702927419361)
                      ·
                        rfl

theorem cell23_5293235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_5293235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293235 prefixEnd_5293235 := by exact prefixLift 5293235
  have htrace : WordTrace (prefixWord ++ tailWord_5293235) baseStart_5293235 baseEnd_5293235 := by
    simpa [prefixWord, tailWord_5293235, baseEnd_5293235] using wordTrace_append hprefix tailTrace_5293235
  have hstable : (prefixWord ++ tailWord_5293235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293235).length < 2 ^ (prefixWord ++ tailWord_5293235).sum := by decide
  have hdescent : baseEnd_5293235 < baseStart_5293235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293242 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3]
def baseStart_5293242 : Nat := 118140960795 + 5293242 * 2 ^ 59
def prefixEnd_5293242 : Nat := 4983230072969 + 3 ^ 40 * 5293242 * 2
def baseEnd_5293242 : Nat := 2717977366566284400031829

theorem tailTrace_5293242 : CollatzResearch.WordTrace tailWord_5293242 prefixEnd_5293242 2717977366566284400031829 := by
  unfold tailWord_5293242
  simp only [CollatzResearch.WordTrace]
  refine ⟨48265099072373930651624495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128706930859663815070998653 48265099072373930651624495)
  ·
    refine ⟨72397648608560895977436743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48265099072373930651624495 72397648608560895977436743)
    ·
      refine ⟨108596472912841343966155115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72397648608560895977436743 108596472912841343966155115)
      ·
        refine ⟨162894709369262015949232673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108596472912841343966155115 162894709369262015949232673)
        ·
          refine ⟨122171032026946511961924505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162894709369262015949232673 122171032026946511961924505)
          ·
            refine ⟨91628274020209883971443379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122171032026946511961924505 91628274020209883971443379)
            ·
              refine ⟨137442411030314825957165069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91628274020209883971443379 137442411030314825957165069)
              ·
                refine ⟨51540904136368059733936901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137442411030314825957165069 51540904136368059733936901)
                ·
                  refine ⟨9663919525569011200113169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51540904136368059733936901 9663919525569011200113169)
                  ·
                    refine ⟨7247939644176758400084877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9663919525569011200113169 7247939644176758400084877)
                    ·
                      refine ⟨2717977366566284400031829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7247939644176758400084877 2717977366566284400031829)
                      ·
                        rfl

theorem cell23_5293242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_5293242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293242 prefixEnd_5293242 := by exact prefixLift 5293242
  have htrace : WordTrace (prefixWord ++ tailWord_5293242) baseStart_5293242 baseEnd_5293242 := by
    simpa [prefixWord, tailWord_5293242, baseEnd_5293242] using wordTrace_append hprefix tailTrace_5293242
  have hstable : (prefixWord ++ tailWord_5293242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293242).length < 2 ^ (prefixWord ++ tailWord_5293242).sum := by decide
  have hdescent : baseEnd_5293242 < baseStart_5293242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293265 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_5293265 : Nat := 118140960795 + 5293265 * 2 ^ 59
def prefixEnd_5293265 : Nat := 4983230072969 + 3 ^ 40 * 5293265 * 2
def baseEnd_5293265 : Nat := 2717989176621337810044223

theorem tailTrace_5293265 : CollatzResearch.WordTrace tailWord_5293265 prefixEnd_5293265 2717989176621337810044223 := by
  unfold tailWord_5293265
  simp only [CollatzResearch.WordTrace]
  refine ⟨193061235168412397534585249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128707490112274931689723499 193061235168412397534585249)
  ·
    refine ⟨144795926376309298150938937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193061235168412397534585249 144795926376309298150938937)
    ·
      refine ⟨108596944782231973613204203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144795926376309298150938937 108596944782231973613204203)
      ·
        refine ⟨162895417173347960419806305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108596944782231973613204203 162895417173347960419806305)
        ·
          refine ⟨122171562880010970314854729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162895417173347960419806305 122171562880010970314854729)
          ·
            refine ⟨91628672160008227736141047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122171562880010970314854729 91628672160008227736141047)
            ·
              refine ⟨137443008240012341604211571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91628672160008227736141047 137443008240012341604211571)
              ·
                refine ⟨206164512360018512406317357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137443008240012341604211571 206164512360018512406317357)
                ·
                  refine ⟨77311692135006942152369009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206164512360018512406317357 77311692135006942152369009)
                  ·
                    refine ⟨57983769101255206614276757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77311692135006942152369009 57983769101255206614276757)
                    ·
                      refine ⟨2717989176621337810044223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57983769101255206614276757 2717989176621337810044223)
                      ·
                        rfl

theorem cell23_5293265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_5293265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293265 prefixEnd_5293265 := by exact prefixLift 5293265
  have htrace : WordTrace (prefixWord ++ tailWord_5293265) baseStart_5293265 baseEnd_5293265 := by
    simpa [prefixWord, tailWord_5293265, baseEnd_5293265] using wordTrace_append hprefix tailTrace_5293265
  have hstable : (prefixWord ++ tailWord_5293265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293265).length < 2 ^ (prefixWord ++ tailWord_5293265).sum := by decide
  have hdescent : baseEnd_5293265 < baseStart_5293265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293299 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 4, 3, 2]
def baseStart_5293299 : Nat := 118140960795 + 5293299 * 2 ^ 59
def prefixEnd_5293299 : Nat := 4983230072969 + 3 ^ 40 * 5293299 * 2
def baseEnd_5293299 : Nat := 2718006634963590677019067

theorem tailTrace_5293299 : CollatzResearch.WordTrace tailWord_5293299 prefixEnd_5293299 2718006634963590677019067 := by
  unfold tailWord_5293299
  simp only [CollatzResearch.WordTrace]
  refine ⟨193062475250289221341322951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128708316833526147560881967 193062475250289221341322951)
  ·
    refine ⟨289593712875433832011984427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193062475250289221341322951 289593712875433832011984427)
    ·
      refine ⟨434390569313150748017976641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289593712875433832011984427 434390569313150748017976641)
      ·
        refine ⟨325792926984863061013482481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434390569313150748017976641 325792926984863061013482481)
        ·
          refine ⟨244344695238647295760111861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325792926984863061013482481 244344695238647295760111861)
          ·
            refine ⟨22907315178623183977510487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 244344695238647295760111861 22907315178623183977510487)
            ·
              refine ⟨34360972767934775966265731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22907315178623183977510487 34360972767934775966265731)
              ·
                refine ⟨51541459151902163949398597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34360972767934775966265731 51541459151902163949398597)
                ·
                  refine ⟨9664023590981655740512237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51541459151902163949398597 9664023590981655740512237)
                  ·
                    refine ⟨3624008846618120902692089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9664023590981655740512237 3624008846618120902692089)
                    ·
                      refine ⟨2718006634963590677019067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624008846618120902692089 2718006634963590677019067)
                      ·
                        rfl

theorem cell23_5293299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 3, 2].length) (baseStart_5293299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293299 prefixEnd_5293299 := by exact prefixLift 5293299
  have htrace : WordTrace (prefixWord ++ tailWord_5293299) baseStart_5293299 baseEnd_5293299 := by
    simpa [prefixWord, tailWord_5293299, baseEnd_5293299] using wordTrace_append hprefix tailTrace_5293299
  have hstable : (prefixWord ++ tailWord_5293299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293299).length < 2 ^ (prefixWord ++ tailWord_5293299).sum := by decide
  have hdescent : baseEnd_5293299 < baseStart_5293299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293302 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_5293302 : Nat := 118140960795 + 5293302 * 2 ^ 59
def prefixEnd_5293302 : Nat := 4983230072969 + 3 ^ 40 * 5293302 * 2
def baseEnd_5293302 : Nat := 2718008175405554165281553

theorem tailTrace_5293302 : CollatzResearch.WordTrace tailWord_5293302 prefixEnd_5293302 2718008175405554165281553 := by
  unfold tailWord_5293302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12066411541829897053355135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128708389779518901902454773 12066411541829897053355135)
  ·
    refine ⟨18099617312744845580032703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12066411541829897053355135 18099617312744845580032703)
    ·
      refine ⟨27149425969117268370049055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18099617312744845580032703 27149425969117268370049055)
      ·
        refine ⟨40724138953675902555073583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27149425969117268370049055 40724138953675902555073583)
        ·
          refine ⟨61086208430513853832610375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40724138953675902555073583 61086208430513853832610375)
          ·
            refine ⟨91629312645770780748915563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61086208430513853832610375 91629312645770780748915563)
            ·
              refine ⟨137443968968656171123373345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91629312645770780748915563 137443968968656171123373345)
              ·
                refine ⟨103082976726492128342530009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137443968968656171123373345 103082976726492128342530009)
                ·
                  refine ⟨77312232544869096256897507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103082976726492128342530009 77312232544869096256897507)
                  ·
                    refine ⟨115968348817303644385346261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77312232544869096256897507 115968348817303644385346261)
                    ·
                      refine ⟨2718008175405554165281553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115968348817303644385346261 2718008175405554165281553)
                      ·
                        rfl

theorem cell23_5293302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_5293302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293302 prefixEnd_5293302 := by exact prefixLift 5293302
  have htrace : WordTrace (prefixWord ++ tailWord_5293302) baseStart_5293302 baseEnd_5293302 := by
    simpa [prefixWord, tailWord_5293302, baseEnd_5293302] using wordTrace_append hprefix tailTrace_5293302
  have hstable : (prefixWord ++ tailWord_5293302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293302).length < 2 ^ (prefixWord ++ tailWord_5293302).sum := by decide
  have hdescent : baseEnd_5293302 < baseStart_5293302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293312 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 4]
def baseStart_5293312 : Nat := 118140960795 + 5293312 * 2 ^ 59
def prefixEnd_5293312 : Nat := 4983230072969 + 3 ^ 40 * 5293312 * 2
def baseEnd_5293312 : Nat := 2718013310212099126156507

theorem tailTrace_5293312 : CollatzResearch.WordTrace tailWord_5293312 prefixEnd_5293312 2718013310212099126156507 := by
  unfold tailWord_5293312
  simp only [CollatzResearch.WordTrace]
  refine ⟨96531474699621062280773095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128708632932828083041030793 96531474699621062280773095)
  ·
    refine ⟨144797212049431593421159643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96531474699621062280773095 144797212049431593421159643)
    ·
      refine ⟨217195818074147390131739465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144797212049431593421159643 217195818074147390131739465)
      ·
        refine ⟨162896863555610542598804599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217195818074147390131739465 162896863555610542598804599)
        ·
          refine ⟨244345295333415813898206899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162896863555610542598804599 244345295333415813898206899)
          ·
            refine ⟨366517943000123720847310349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244345295333415813898206899 366517943000123720847310349)
            ·
              refine ⟨137444228625046395317741381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 366517943000123720847310349 137444228625046395317741381)
              ·
                refine ⟨25770792867196199122076509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137444228625046395317741381 25770792867196199122076509)
                ·
                  refine ⟨9664047325198574670778691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25770792867196199122076509 9664047325198574670778691)
                  ·
                    refine ⟨14496070987797862006168037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9664047325198574670778691 14496070987797862006168037)
                    ·
                      refine ⟨2718013310212099126156507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14496070987797862006168037 2718013310212099126156507)
                      ·
                        rfl

theorem cell23_5293312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_5293312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293312 prefixEnd_5293312 := by exact prefixLift 5293312
  have htrace : WordTrace (prefixWord ++ tailWord_5293312) baseStart_5293312 baseEnd_5293312 := by
    simpa [prefixWord, tailWord_5293312, baseEnd_5293312] using wordTrace_append hprefix tailTrace_5293312
  have hstable : (prefixWord ++ tailWord_5293312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293312).length < 2 ^ (prefixWord ++ tailWord_5293312).sum := by decide
  have hdescent : baseEnd_5293312 < baseStart_5293312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293322 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 1, 6]
def baseStart_5293322 : Nat := 118140960795 + 5293322 * 2 ^ 59
def prefixEnd_5293322 : Nat := 4983230072969 + 3 ^ 40 * 5293322 * 2
def baseEnd_5293322 : Nat := 906006148339548029010487

theorem tailTrace_5293322 : CollatzResearch.WordTrace tailWord_5293322 prefixEnd_5293322 906006148339548029010487 := by
  unfold tailWord_5293322
  simp only [CollatzResearch.WordTrace]
  refine ⟨48265828532301474067352555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128708876086137264179606813 48265828532301474067352555)
  ·
    refine ⟨72398742798452211101028833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48265828532301474067352555 72398742798452211101028833)
    ·
      refine ⟨54299057098839158325771625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72398742798452211101028833 54299057098839158325771625)
      ·
        refine ⟨40724292824129368744328719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54299057098839158325771625 40724292824129368744328719)
        ·
          refine ⟨61086439236194053116493079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40724292824129368744328719 61086439236194053116493079)
          ·
            refine ⟨91629658854291079674739619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61086439236194053116493079 91629658854291079674739619)
            ·
              refine ⟨137444488281436619512109429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91629658854291079674739619 137444488281436619512109429)
              ·
                refine ⟨12885420776384683079260259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137444488281436619512109429 12885420776384683079260259)
                ·
                  refine ⟨19328131164577024618890389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12885420776384683079260259 19328131164577024618890389)
                  ·
                    refine ⟨906006148339548029010487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19328131164577024618890389 906006148339548029010487)
                    ·
                      rfl

theorem cell23_5293322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_5293322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293322 prefixEnd_5293322 := by exact prefixLift 5293322
  have htrace : WordTrace (prefixWord ++ tailWord_5293322) baseStart_5293322 baseEnd_5293322 := by
    simpa [prefixWord, tailWord_5293322, baseEnd_5293322] using wordTrace_append hprefix tailTrace_5293322
  have hstable : (prefixWord ++ tailWord_5293322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293322).length < 2 ^ (prefixWord ++ tailWord_5293322).sum := by decide
  have hdescent : baseEnd_5293322 < baseStart_5293322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293326 : List Nat := [4, 1, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_5293326 : Nat := 118140960795 + 5293326 * 2 ^ 59
def prefixEnd_5293326 : Nat := 4983230072969 + 3 ^ 40 * 5293326 * 2
def baseEnd_5293326 : Nat := 906006832980420690460481

theorem tailTrace_5293326 : CollatzResearch.WordTrace tailWord_5293326 prefixEnd_5293326 906006832980420690460481 := by
  unfold tailWord_5293326
  simp only [CollatzResearch.WordTrace]
  refine ⟨24132932502648925619069479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128708973347460936635037221 24132932502648925619069479)
  ·
    refine ⟨36199398753973388428604219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24132932502648925619069479 36199398753973388428604219)
    ·
      refine ⟨54299098130960082642906329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36199398753973388428604219 54299098130960082642906329)
      ·
        refine ⟨40724323598220061982179747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54299098130960082642906329 40724323598220061982179747)
        ·
          refine ⟨61086485397330092973269621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40724323598220061982179747 61086485397330092973269621)
          ·
            refine ⟨5726858005999696216244027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61086485397330092973269621 5726858005999696216244027)
            ·
              refine ⟨8590287008999544324366041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5726858005999696216244027 8590287008999544324366041)
              ·
                refine ⟨6442715256749658243274531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8590287008999544324366041 6442715256749658243274531)
                ·
                  refine ⟨9664072885124487364911797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6442715256749658243274531 9664072885124487364911797)
                  ·
                    refine ⟨906006832980420690460481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9664072885124487364911797 906006832980420690460481)
                    ·
                      rfl

theorem cell23_5293326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_5293326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293326 prefixEnd_5293326 := by exact prefixLift 5293326
  have htrace : WordTrace (prefixWord ++ tailWord_5293326) baseStart_5293326 baseEnd_5293326 := by
    simpa [prefixWord, tailWord_5293326, baseEnd_5293326] using wordTrace_append hprefix tailTrace_5293326
  have hstable : (prefixWord ++ tailWord_5293326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293326).length < 2 ^ (prefixWord ++ tailWord_5293326).sum := by decide
  have hdescent : baseEnd_5293326 < baseStart_5293326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293349 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 5]
def baseStart_5293349 : Nat := 118140960795 + 5293349 * 2 ^ 59
def prefixEnd_5293349 : Nat := 4983230072969 + 3 ^ 40 * 5293349 * 2
def baseEnd_5293349 : Nat := 2718032308996315481393837

theorem tailTrace_5293349 : CollatzResearch.WordTrace tailWord_5293349 prefixEnd_5293349 2718032308996315481393837 := by
  unfold tailWord_5293349
  simp only [CollatzResearch.WordTrace]
  refine ⟨193064298900108079880643101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128709532600072053253762067 193064298900108079880643101)
  ·
    refine ⟨72399112087540529955241163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193064298900108079880643101 72399112087540529955241163)
    ·
      refine ⟨108598668131310794932861745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72399112087540529955241163 108598668131310794932861745)
      ·
        refine ⟨81449001098483096199646309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108598668131310794932861745 81449001098483096199646309)
        ·
          refine ⟨15271687705965580537433683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81449001098483096199646309 15271687705965580537433683)
          ·
            refine ⟨22907531558948370806150525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15271687705965580537433683 22907531558948370806150525)
            ·
              refine ⟨8590324334605639052306447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22907531558948370806150525 8590324334605639052306447)
              ·
                refine ⟨12885486501908458578459671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8590324334605639052306447 12885486501908458578459671)
                ·
                  refine ⟨19328229752862687867689507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12885486501908458578459671 19328229752862687867689507)
                  ·
                    refine ⟨28992344629294031801534261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19328229752862687867689507 28992344629294031801534261)
                    ·
                      refine ⟨2718032308996315481393837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28992344629294031801534261 2718032308996315481393837)
                      ·
                        rfl

theorem cell23_5293349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_5293349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293349 prefixEnd_5293349 := by exact prefixLift 5293349
  have htrace : WordTrace (prefixWord ++ tailWord_5293349) baseStart_5293349 baseEnd_5293349 := by
    simpa [prefixWord, tailWord_5293349, baseEnd_5293349] using wordTrace_append hprefix tailTrace_5293349
  have hstable : (prefixWord ++ tailWord_5293349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293349).length < 2 ^ (prefixWord ++ tailWord_5293349).sum := by decide
  have hdescent : baseEnd_5293349 < baseStart_5293349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293352 : List Nat := [2, 1, 5, 1, 2, 12]
def baseStart_5293352 : Nat := 118140960795 + 5293352 * 2 ^ 59
def prefixEnd_5293352 : Nat := 4983230072969 + 3 ^ 40 * 5293352 * 2
def baseEnd_5293352 : Nat := 11185324483285098640561

theorem tailTrace_5293352 : CollatzResearch.WordTrace tailWord_5293352 prefixEnd_5293352 11185324483285098640561 := by
  unfold tailWord_5293352
  simp only [CollatzResearch.WordTrace]
  refine ⟨96532204159548605696501155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128709605546064807595334873 96532204159548605696501155)
  ·
    refine ⟨144798306239322908544751733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96532204159548605696501155 144798306239322908544751733)
    ·
      refine ⟨13574841209936522676070475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144798306239322908544751733 13574841209936522676070475)
      ·
        refine ⟨20362261814904784014105713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13574841209936522676070475 20362261814904784014105713)
        ·
          refine ⟨15271696361178588010579285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20362261814904784014105713 15271696361178588010579285)
          ·
            refine ⟨11185324483285098640561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15271696361178588010579285 11185324483285098640561)
            ·
              rfl

theorem cell23_5293352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 12].length) (baseStart_5293352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293352 prefixEnd_5293352 := by exact prefixLift 5293352
  have htrace : WordTrace (prefixWord ++ tailWord_5293352) baseStart_5293352 baseEnd_5293352 := by
    simpa [prefixWord, tailWord_5293352, baseEnd_5293352] using wordTrace_append hprefix tailTrace_5293352
  have hstable : (prefixWord ++ tailWord_5293352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293352).length < 2 ^ (prefixWord ++ tailWord_5293352).sum := by decide
  have hdescent : baseEnd_5293352 < baseStart_5293352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293357 : List Nat := [1, 5, 3, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_5293357 : Nat := 118140960795 + 5293357 * 2 ^ 59
def prefixEnd_5293357 : Nat := 4983230072969 + 3 ^ 40 * 5293357 * 2
def baseEnd_5293357 : Nat := 2718036416841551450093801

theorem tailTrace_5293357 : CollatzResearch.WordTrace tailWord_5293357 prefixEnd_5293357 2718036416841551450093801 := by
  unfold tailWord_5293357
  simp only [CollatzResearch.WordTrace]
  refine ⟨193064590684079097246934325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128709727122719398164622883 193064590684079097246934325)
  ·
    refine ⟨18099805376632415366900093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193064590684079097246934325 18099805376632415366900093)
    ·
      refine ⟨6787427016237155762587535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18099805376632415366900093 6787427016237155762587535)
      ·
        refine ⟨10181140524355733643881303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6787427016237155762587535 10181140524355733643881303)
        ·
          refine ⟨15271710786533600465821955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10181140524355733643881303 15271710786533600465821955)
          ·
            refine ⟨22907566179800400698732933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15271710786533600465821955 22907566179800400698732933)
            ·
              refine ⟨4295168658712575131012425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22907566179800400698732933 4295168658712575131012425)
              ·
                refine ⟨3221376494034431348259319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4295168658712575131012425 3221376494034431348259319)
                ·
                  refine ⟨4832064741051647022388979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221376494034431348259319 4832064741051647022388979)
                  ·
                    refine ⟨7248097111577470533583469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4832064741051647022388979 7248097111577470533583469)
                    ·
                      refine ⟨2718036416841551450093801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7248097111577470533583469 2718036416841551450093801)
                      ·
                        rfl

theorem cell23_5293357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_5293357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293357 prefixEnd_5293357 := by exact prefixLift 5293357
  have htrace : WordTrace (prefixWord ++ tailWord_5293357) baseStart_5293357 baseEnd_5293357 := by
    simpa [prefixWord, tailWord_5293357, baseEnd_5293357] using wordTrace_append hprefix tailTrace_5293357
  have hstable : (prefixWord ++ tailWord_5293357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293357).length < 2 ^ (prefixWord ++ tailWord_5293357).sum := by decide
  have hdescent : baseEnd_5293357 < baseStart_5293357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293379 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 6, 1, 3]
def baseStart_5293379 : Nat := 118140960795 + 5293379 * 2 ^ 59
def prefixEnd_5293379 : Nat := 4983230072969 + 3 ^ 40 * 5293379 * 2
def baseEnd_5293379 : Nat := 2718047713415950364018699

theorem tailTrace_5293379 : CollatzResearch.WordTrace tailWord_5293379 prefixEnd_5293379 2718047713415950364018699 := by
  unfold tailWord_5293379
  simp only [CollatzResearch.WordTrace]
  refine ⟨193065393089999395004235191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128710262059999596669490127 193065393089999395004235191)
  ·
    refine ⟨289598089634999092506352787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193065393089999395004235191 289598089634999092506352787)
    ·
      refine ⟨434397134452498638759529181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289598089634999092506352787 434397134452498638759529181)
      ·
        refine ⟨162898925419686989534823443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434397134452498638759529181 162898925419686989534823443)
        ·
          refine ⟨244348388129530484302235165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162898925419686989534823443 244348388129530484302235165)
          ·
            refine ⟨91630645548573931613338187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244348388129530484302235165 91630645548573931613338187)
            ·
              refine ⟨137445968322860897420007281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91630645548573931613338187 137445968322860897420007281)
              ·
                refine ⟨103084476242145673065005461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137445968322860897420007281 103084476242145673065005461)
                ·
                  refine ⟨4832084823850578424922131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103084476242145673065005461 4832084823850578424922131)
                  ·
                    refine ⟨7248127235775867637383197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4832084823850578424922131 7248127235775867637383197)
                    ·
                      refine ⟨2718047713415950364018699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7248127235775867637383197 2718047713415950364018699)
                      ·
                        rfl

theorem cell23_5293379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_5293379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293379 prefixEnd_5293379 := by exact prefixLift 5293379
  have htrace : WordTrace (prefixWord ++ tailWord_5293379) baseStart_5293379 baseEnd_5293379 := by
    simpa [prefixWord, tailWord_5293379, baseEnd_5293379] using wordTrace_append hprefix tailTrace_5293379
  have hstable : (prefixWord ++ tailWord_5293379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293379).length < 2 ^ (prefixWord ++ tailWord_5293379).sum := by decide
  have hdescent : baseEnd_5293379 < baseStart_5293379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293380 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_5293380 : Nat := 118140960795 + 5293380 * 2 ^ 59
def prefixEnd_5293380 : Nat := 4983230072969 + 3 ^ 40 * 5293380 * 2
def baseEnd_5293380 : Nat := 2718048226896604860106195

theorem tailTrace_5293380 : CollatzResearch.WordTrace tailWord_5293380 prefixEnd_5293380 2718048226896604860106195 := by
  unfold tailWord_5293380
  simp only [CollatzResearch.WordTrace]
  refine ⟨96532714781497886087510797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128710286375330514783347729 96532714781497886087510797)
  ·
    refine ⟨36199768043061707282816549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96532714781497886087510797 36199768043061707282816549)
    ·
      refine ⟨6787456508074070115528103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36199768043061707282816549 6787456508074070115528103)
      ·
        refine ⟨10181184762111105173292155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6787456508074070115528103 10181184762111105173292155)
        ·
          refine ⟨15271777143166657759938233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10181184762111105173292155 15271777143166657759938233)
          ·
            refine ⟨11453832857374993319953675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15271777143166657759938233 11453832857374993319953675)
            ·
              refine ⟨17180749286062489979930513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11453832857374993319953675 17180749286062489979930513)
              ·
                refine ⟨12885561964546867484947885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17180749286062489979930513 12885561964546867484947885)
                ·
                  refine ⟨4832085736705075306855457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12885561964546867484947885 4832085736705075306855457)
                  ·
                    refine ⟨3624064302528806480141593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4832085736705075306855457 3624064302528806480141593)
                    ·
                      refine ⟨2718048226896604860106195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624064302528806480141593 2718048226896604860106195)
                      ·
                        rfl

theorem cell23_5293380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_5293380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293380 prefixEnd_5293380 := by exact prefixLift 5293380
  have htrace : WordTrace (prefixWord ++ tailWord_5293380) baseStart_5293380 baseEnd_5293380 := by
    simpa [prefixWord, tailWord_5293380, baseEnd_5293380] using wordTrace_append hprefix tailTrace_5293380
  have hstable : (prefixWord ++ tailWord_5293380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293380).length < 2 ^ (prefixWord ++ tailWord_5293380).sum := by decide
  have hdescent : baseEnd_5293380 < baseStart_5293380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293392 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 5]
def baseStart_5293392 : Nat := 118140960795 + 5293392 * 2 ^ 59
def prefixEnd_5293392 : Nat := 4983230072969 + 3 ^ 40 * 5293392 * 2
def baseEnd_5293392 : Nat := 2718054388664458813156139

theorem tailTrace_5293392 : CollatzResearch.WordTrace tailWord_5293392 prefixEnd_5293392 2718054388664458813156139 := by
  unfold tailWord_5293392
  simp only [CollatzResearch.WordTrace]
  refine ⟨96532933619476149112229215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128710578159301532149638953 96532933619476149112229215)
  ·
    refine ⟨144799400429214223668343823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96532933619476149112229215 144799400429214223668343823)
    ·
      refine ⟨217199100643821335502515735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144799400429214223668343823 217199100643821335502515735)
      ·
        refine ⟨325798650965732003253773603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217199100643821335502515735 325798650965732003253773603)
        ·
          refine ⟨488697976448598004880660405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325798650965732003253773603 488697976448598004880660405)
          ·
            refine ⟨45815435292056062957561913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 488697976448598004880660405 45815435292056062957561913)
            ·
              refine ⟨34361576469042047218171435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45815435292056062957561913 34361576469042047218171435)
              ·
                refine ⟨51542364703563070827257153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34361576469042047218171435 51542364703563070827257153)
                ·
                  refine ⟨38656773527672303120442865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51542364703563070827257153 38656773527672303120442865)
                  ·
                    refine ⟨28992580145754227340332149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38656773527672303120442865 28992580145754227340332149)
                    ·
                      refine ⟨2718054388664458813156139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28992580145754227340332149 2718054388664458813156139)
                      ·
                        rfl

theorem cell23_5293392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_5293392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293392 prefixEnd_5293392 := by exact prefixLift 5293392
  have htrace : WordTrace (prefixWord ++ tailWord_5293392) baseStart_5293392 baseEnd_5293392 := by
    simpa [prefixWord, tailWord_5293392, baseEnd_5293392] using wordTrace_append hprefix tailTrace_5293392
  have hstable : (prefixWord ++ tailWord_5293392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293392).length < 2 ^ (prefixWord ++ tailWord_5293392).sum := by decide
  have hdescent : baseEnd_5293392 < baseStart_5293392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293396 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_5293396 : Nat := 118140960795 + 5293396 * 2 ^ 59
def prefixEnd_5293396 : Nat := 4983230072969 + 3 ^ 40 * 5293396 * 2
def baseEnd_5293396 : Nat := 2718056442587076797506121

theorem tailTrace_5293396 : CollatzResearch.WordTrace tailWord_5293396 prefixEnd_5293396 2718056442587076797506121 := by
  unfold tailWord_5293396
  simp only [CollatzResearch.WordTrace]
  refine ⟨96533006565468903453802021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128710675420625204605069361 96533006565468903453802021)
  ·
    refine ⟨18099938731025419397587879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96533006565468903453802021 18099938731025419397587879)
    ·
      refine ⟨27149908096538129096381819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18099938731025419397587879 27149908096538129096381819)
      ·
        refine ⟨40724862144807193644572729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27149908096538129096381819 40724862144807193644572729)
        ·
          refine ⟨30543646608605395233429547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40724862144807193644572729 30543646608605395233429547)
          ·
            refine ⟨45815469912908092850144321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30543646608605395233429547 45815469912908092850144321)
            ·
              refine ⟨34361602434681069637608241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45815469912908092850144321 34361602434681069637608241)
              ·
                refine ⟨25771201826010802228206181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34361602434681069637608241 25771201826010802228206181)
                ·
                  refine ⟨4832100342377025417788659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25771201826010802228206181 4832100342377025417788659)
                  ·
                    refine ⟨7248150513565538126682989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4832100342377025417788659 7248150513565538126682989)
                    ·
                      refine ⟨2718056442587076797506121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7248150513565538126682989 2718056442587076797506121)
                      ·
                        rfl

theorem cell23_5293396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_5293396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293396 prefixEnd_5293396 := by exact prefixLift 5293396
  have htrace : WordTrace (prefixWord ++ tailWord_5293396) baseStart_5293396 baseEnd_5293396 := by
    simpa [prefixWord, tailWord_5293396, baseEnd_5293396] using wordTrace_append hprefix tailTrace_5293396
  have hstable : (prefixWord ++ tailWord_5293396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293396).length < 2 ^ (prefixWord ++ tailWord_5293396).sum := by decide
  have hdescent : baseEnd_5293396 < baseStart_5293396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293489 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 4, 5]
def baseStart_5293489 : Nat := 118140960795 + 5293489 * 2 ^ 59
def prefixEnd_5293489 : Nat := 4983230072969 + 3 ^ 40 * 5293489 * 2
def baseEnd_5293489 : Nat := 906034732095981644547731

theorem tailTrace_5293489 : CollatzResearch.WordTrace tailWord_5293489 prefixEnd_5293489 906034732095981644547731 := by
  unfold tailWord_5293489
  simp only [CollatzResearch.WordTrace]
  refine ⟨193069405119600883790739521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128712936746400589193826347 193069405119600883790739521)
  ·
    refine ⟨144802053839700662843054641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193069405119600883790739521 144802053839700662843054641)
    ·
      refine ⟨108601540379775497132290981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144802053839700662843054641 108601540379775497132290981)
      ·
        refine ⟨20362788821207905712304559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108601540379775497132290981 20362788821207905712304559)
        ·
          refine ⟨30544183231811858568456839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20362788821207905712304559 30544183231811858568456839)
          ·
            refine ⟨45816274847717787852685259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30544183231811858568456839 45816274847717787852685259)
            ·
              refine ⟨68724412271576681779027889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45816274847717787852685259 68724412271576681779027889)
              ·
                refine ⟨51543309203682511334270917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68724412271576681779027889 51543309203682511334270917)
                ·
                  refine ⟨9664370475690470875175797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51543309203682511334270917 9664370475690470875175797)
                  ·
                    refine ⟨906034732095981644547731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9664370475690470875175797 906034732095981644547731)
                    ·
                      rfl

theorem cell23_5293489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_5293489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293489 prefixEnd_5293489 := by exact prefixLift 5293489
  have htrace : WordTrace (prefixWord ++ tailWord_5293489) baseStart_5293489 baseEnd_5293489 := by
    simpa [prefixWord, tailWord_5293489, baseEnd_5293489] using wordTrace_append hprefix tailTrace_5293489
  have hstable : (prefixWord ++ tailWord_5293489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293489).length < 2 ^ (prefixWord ++ tailWord_5293489).sum := by decide
  have hdescent : baseEnd_5293489 < baseStart_5293489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293543 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_5293543 : Nat := 118140960795 + 5293543 * 2 ^ 59
def prefixEnd_5293543 : Nat := 4983230072969 + 3 ^ 40 * 5293543 * 2
def baseEnd_5293543 : Nat := 2718131924243287722367945

theorem tailTrace_5293543 : CollatzResearch.WordTrace tailWord_5293543 prefixEnd_5293543 2718131924243287722367945 := by
  unfold tailWord_5293543
  simp only [CollatzResearch.WordTrace]
  refine ⟨193071374661405251013205283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128714249774270167342136855 193071374661405251013205283)
  ·
    refine ⟨289607061992107876519807925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193071374661405251013205283 289607061992107876519807925)
    ·
      refine ⟨27150662061760113423731993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 289607061992107876519807925 27150662061760113423731993)
      ·
        refine ⟨20362996546320085067798995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27150662061760113423731993 20362996546320085067798995)
        ·
          refine ⟨30544494819480127601698493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20362996546320085067798995 30544494819480127601698493)
          ·
            refine ⟨11454185557305047850636935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30544494819480127601698493 11454185557305047850636935)
            ·
              refine ⟨17181278335957571775955403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11454185557305047850636935 17181278335957571775955403)
              ·
                refine ⟨25771917503936357663933105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17181278335957571775955403 25771917503936357663933105)
                ·
                  refine ⟨19328938127952268247949829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25771917503936357663933105 19328938127952268247949829)
                  ·
                    refine ⟨3624175898991050296490593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19328938127952268247949829 3624175898991050296490593)
                    ·
                      refine ⟨2718131924243287722367945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624175898991050296490593 2718131924243287722367945)
                      ·
                        rfl

theorem cell23_5293543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_5293543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293543 prefixEnd_5293543 := by exact prefixLift 5293543
  have htrace : WordTrace (prefixWord ++ tailWord_5293543) baseStart_5293543 baseEnd_5293543 := by
    simpa [prefixWord, tailWord_5293543, baseEnd_5293543] using wordTrace_append hprefix tailTrace_5293543
  have hstable : (prefixWord ++ tailWord_5293543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293543).length < 2 ^ (prefixWord ++ tailWord_5293543).sum := by decide
  have hdescent : baseEnd_5293543 < baseStart_5293543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293559 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 3]
def baseStart_5293559 : Nat := 118140960795 + 5293559 * 2 ^ 59
def prefixEnd_5293559 : Nat := 4983230072969 + 3 ^ 40 * 5293559 * 2
def baseEnd_5293559 : Nat := 2718140139933759659767871

theorem tailTrace_5293559 : CollatzResearch.WordTrace tailWord_5293559 prefixEnd_5293559 2718140139933759659767871 := by
  unfold tailWord_5293559
  simp only [CollatzResearch.WordTrace]
  refine ⟨193071958229347285745787731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128714638819564857163858487 193071958229347285745787731)
  ·
    refine ⟨289607937344020928618681597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193071958229347285745787731 289607937344020928618681597)
    ·
      refine ⟨108602976504007848232005599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289607937344020928618681597 108602976504007848232005599)
      ·
        refine ⟨162904464756011772348008399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108602976504007848232005599 162904464756011772348008399)
        ·
          refine ⟨244356697134017658522012599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162904464756011772348008399 244356697134017658522012599)
          ·
            refine ⟨366535045701026487783018899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244356697134017658522012599 366535045701026487783018899)
            ·
              refine ⟨549802568551539731674528349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366535045701026487783018899 549802568551539731674528349)
              ·
                refine ⟨206175963206827399377948131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 549802568551539731674528349 206175963206827399377948131)
                ·
                  refine ⟨309263944810241099066922197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206175963206827399377948131 309263944810241099066922197)
                  ·
                    refine ⟨7248373706490025759380989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 309263944810241099066922197 7248373706490025759380989)
                    ·
                      refine ⟨2718140139933759659767871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7248373706490025759380989 2718140139933759659767871)
                      ·
                        rfl

theorem cell23_5293559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_5293559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293559 prefixEnd_5293559 := by exact prefixLift 5293559
  have htrace : WordTrace (prefixWord ++ tailWord_5293559) baseStart_5293559 baseEnd_5293559 := by
    simpa [prefixWord, tailWord_5293559, baseEnd_5293559] using wordTrace_append hprefix tailTrace_5293559
  have hstable : (prefixWord ++ tailWord_5293559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293559).length < 2 ^ (prefixWord ++ tailWord_5293559).sum := by decide
  have hdescent : baseEnd_5293559 < baseStart_5293559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293616 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 1, 8, 2]
def baseStart_5293616 : Nat := 118140960795 + 5293616 * 2 ^ 59
def prefixEnd_5293616 : Nat := 4983230072969 + 3 ^ 40 * 5293616 * 2
def baseEnd_5293616 : Nat := 2718169408331065936755109

theorem tailTrace_5293616 : CollatzResearch.WordTrace tailWord_5293616 prefixEnd_5293616 2718169408331065936755109 := by
  unfold tailWord_5293616
  simp only [CollatzResearch.WordTrace]
  refine ⟨96537018595070392240306351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128716024793427189653741801 96537018595070392240306351)
  ·
    refine ⟨144805527892605588360459527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96537018595070392240306351 144805527892605588360459527)
    ·
      refine ⟨217208291838908382540689291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144805527892605588360459527 217208291838908382540689291)
      ·
        refine ⟨325812437758362573811033937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217208291838908382540689291 325812437758362573811033937)
        ·
          refine ⟨244359328318771930358275453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325812437758362573811033937 244359328318771930358275453)
          ·
            refine ⟨91634748119539473884353295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244359328318771930358275453 91634748119539473884353295)
            ·
              refine ⟨137452122179309210826529943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91634748119539473884353295 137452122179309210826529943)
              ·
                refine ⟨206178183268963816239794915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137452122179309210826529943 206178183268963816239794915)
                ·
                  refine ⟨309267274903445724359692373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206178183268963816239794915 309267274903445724359692373)
                  ·
                    refine ⟨3624225877774754582340145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 309267274903445724359692373 3624225877774754582340145)
                    ·
                      refine ⟨2718169408331065936755109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624225877774754582340145 2718169408331065936755109)
                      ·
                        rfl

theorem cell23_5293616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 8, 2].length) (baseStart_5293616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293616 prefixEnd_5293616 := by exact prefixLift 5293616
  have htrace : WordTrace (prefixWord ++ tailWord_5293616) baseStart_5293616 baseEnd_5293616 := by
    simpa [prefixWord, tailWord_5293616, baseEnd_5293616] using wordTrace_append hprefix tailTrace_5293616
  have hstable : (prefixWord ++ tailWord_5293616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293616).length < 2 ^ (prefixWord ++ tailWord_5293616).sum := by decide
  have hdescent : baseEnd_5293616 < baseStart_5293616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293626 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 6, 4]
def baseStart_5293626 : Nat := 118140960795 + 5293626 * 2 ^ 59
def prefixEnd_5293626 : Nat := 4983230072969 + 3 ^ 40 * 5293626 * 2
def baseEnd_5293626 : Nat := 906058181045870299210021

theorem tailTrace_5293626 : CollatzResearch.WordTrace tailWord_5293626 prefixEnd_5293626 906058181045870299210021 := by
  unfold tailWord_5293626
  simp only [CollatzResearch.WordTrace]
  refine ⟨48268600480026139047119183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128716267946736370792317821 48268600480026139047119183)
  ·
    refine ⟨72402900720039208570678775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48268600480026139047119183 72402900720039208570678775)
    ·
      refine ⟨108604351080058812856018163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72402900720039208570678775 108604351080058812856018163)
      ·
        refine ⟨162906526620088219284027245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108604351080058812856018163 162906526620088219284027245)
        ·
          refine ⟨61089947482533082231510217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162906526620088219284027245 61089947482533082231510217)
          ·
            refine ⟨45817460611899811673632663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61089947482533082231510217 45817460611899811673632663)
            ·
              refine ⟨68726190917849717510448995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45817460611899811673632663 68726190917849717510448995)
              ·
                refine ⟨103089286376774576265673493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68726190917849717510448995 103089286376774576265673493)
                ·
                  refine ⟨4832310298911308262453445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103089286376774576265673493 4832310298911308262453445)
                  ·
                    refine ⟨906058181045870299210021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4832310298911308262453445 906058181045870299210021)
                    ·
                      rfl

theorem cell23_5293626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_5293626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293626 prefixEnd_5293626 := by exact prefixLift 5293626
  have htrace : WordTrace (prefixWord ++ tailWord_5293626) baseStart_5293626 baseEnd_5293626 := by
    simpa [prefixWord, tailWord_5293626, baseEnd_5293626] using wordTrace_append hprefix tailTrace_5293626
  have hstable : (prefixWord ++ tailWord_5293626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293626).length < 2 ^ (prefixWord ++ tailWord_5293626).sum := by decide
  have hdescent : baseEnd_5293626 < baseStart_5293626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293633 : List Nat := [1, 2, 5, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_5293633 : Nat := 118140960795 + 5293633 * 2 ^ 59
def prefixEnd_5293633 : Nat := 4983230072969 + 3 ^ 40 * 5293633 * 2
def baseEnd_5293633 : Nat := 2718178137502192370242531

theorem tailTrace_5293633 : CollatzResearch.WordTrace tailWord_5293633 prefixEnd_5293633 2718178137502192370242531 := by
  unfold tailWord_5293633
  simp only [CollatzResearch.WordTrace]
  refine ⟨193074657231079196383981553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128716438154052797589321035 193074657231079196383981553)
  ·
    refine ⟨144805992923309397287986165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193074657231079196383981553 144805992923309397287986165)
    ·
      refine ⟨13575561836560255995748703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144805992923309397287986165 13575561836560255995748703)
      ·
        refine ⟨20363342754840383993623055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13575561836560255995748703 20363342754840383993623055)
        ·
          refine ⟨30545014132260575990434583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20363342754840383993623055 30545014132260575990434583)
          ·
            refine ⟨45817521198390863985651875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30545014132260575990434583 45817521198390863985651875)
            ·
              refine ⟨68726281797586295978477813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45817521198390863985651875 68726281797586295978477813)
              ·
                refine ⟨6443088918523715247982295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68726281797586295978477813 6443088918523715247982295)
                ·
                  refine ⟨9664633377785572871973443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6443088918523715247982295 9664633377785572871973443)
                  ·
                    refine ⟨14496950066678359307960165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9664633377785572871973443 14496950066678359307960165)
                    ·
                      refine ⟨2718178137502192370242531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14496950066678359307960165 2718178137502192370242531)
                      ·
                        rfl

theorem cell23_5293633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_5293633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293633 prefixEnd_5293633 := by exact prefixLift 5293633
  have htrace : WordTrace (prefixWord ++ tailWord_5293633) baseStart_5293633 baseEnd_5293633 := by
    simpa [prefixWord, tailWord_5293633, baseEnd_5293633] using wordTrace_append hprefix tailTrace_5293633
  have hstable : (prefixWord ++ tailWord_5293633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293633).length < 2 ^ (prefixWord ++ tailWord_5293633).sum := by decide
  have hdescent : baseEnd_5293633 < baseStart_5293633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293660 : List Nat := [2, 2, 4, 1, 2, 2, 1, 3, 2, 4]
def baseStart_5293660 : Nat := 118140960795 + 5293660 * 2 ^ 59
def prefixEnd_5293660 : Nat := 4983230072969 + 3 ^ 40 * 5293660 * 2
def baseEnd_5293660 : Nat := 906064000493287921534969

theorem tailTrace_5293660 : CollatzResearch.WordTrace tailWord_5293660 prefixEnd_5293660 906064000493287921534969 := by
  unfold tailWord_5293660
  simp only [CollatzResearch.WordTrace]
  refine ⟨96537821000990689997607217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128717094667987586663476289 96537821000990689997607217)
  ·
    refine ⟨72403365750743017498205413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96537821000990689997607217 72403365750743017498205413)
    ·
      refine ⟨13575631078264315780913515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72403365750743017498205413 13575631078264315780913515)
      ·
        refine ⟨20363446617396473671370273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13575631078264315780913515 20363446617396473671370273)
        ·
          refine ⟨15272584963047355253527705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20363446617396473671370273 15272584963047355253527705)
          ·
            refine ⟨11454438722285516440145779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15272584963047355253527705 11454438722285516440145779)
            ·
              refine ⟨17181658083428274660218669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11454438722285516440145779 17181658083428274660218669)
              ·
                refine ⟨6443121781285602997582001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17181658083428274660218669 6443121781285602997582001)
                ·
                  refine ⟨4832341335964202248186501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6443121781285602997582001 4832341335964202248186501)
                  ·
                    refine ⟨906064000493287921534969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4832341335964202248186501 906064000493287921534969)
                    ·
                      rfl

theorem cell23_5293660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_5293660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293660 prefixEnd_5293660 := by exact prefixLift 5293660
  have htrace : WordTrace (prefixWord ++ tailWord_5293660) baseStart_5293660 baseEnd_5293660 := by
    simpa [prefixWord, tailWord_5293660, baseEnd_5293660] using wordTrace_append hprefix tailTrace_5293660
  have hstable : (prefixWord ++ tailWord_5293660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293660).length < 2 ^ (prefixWord ++ tailWord_5293660).sum := by decide
  have hdescent : baseEnd_5293660 < baseStart_5293660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293710 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2]
def baseStart_5293710 : Nat := 118140960795 + 5293710 * 2 ^ 59
def prefixEnd_5293710 : Nat := 4983230072969 + 3 ^ 40 * 5293710 * 2
def baseEnd_5293710 : Nat := 2718217675512588568979677

theorem tailTrace_5293710 : CollatzResearch.WordTrace tailWord_5293710 prefixEnd_5293710 2718217675512588568979677 := by
  unfold tailWord_5293710
  simp only [CollatzResearch.WordTrace]
  refine ⟨24134683206475029816816823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128718310434533492356356389 24134683206475029816816823)
  ·
    refine ⟨36202024809712544725225235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24134683206475029816816823 36202024809712544725225235)
    ·
      refine ⟨54303037214568817087837853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36202024809712544725225235 54303037214568817087837853)
      ·
        refine ⟨20363638955463306407939195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54303037214568817087837853 20363638955463306407939195)
        ·
          refine ⟨30545458433194959611908793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20363638955463306407939195 30545458433194959611908793)
          ·
            refine ⟨22909093824896219708931595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30545458433194959611908793 22909093824896219708931595)
            ·
              refine ⟨34363640737344329563397393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22909093824896219708931595 34363640737344329563397393)
              ·
                refine ⟨25772730553008247172548045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34363640737344329563397393 25772730553008247172548045)
                ·
                  refine ⟨9664773957378092689705517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25772730553008247172548045 9664773957378092689705517)
                  ·
                    refine ⟨3624290234016784758639569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9664773957378092689705517 3624290234016784758639569)
                    ·
                      refine ⟨2718217675512588568979677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624290234016784758639569 2718217675512588568979677)
                      ·
                        rfl

theorem cell23_5293710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_5293710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293710 prefixEnd_5293710 := by exact prefixLift 5293710
  have htrace : WordTrace (prefixWord ++ tailWord_5293710) baseStart_5293710 baseEnd_5293710 := by
    simpa [prefixWord, tailWord_5293710, baseEnd_5293710] using wordTrace_append hprefix tailTrace_5293710
  have hstable : (prefixWord ++ tailWord_5293710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293710).length < 2 ^ (prefixWord ++ tailWord_5293710).sum := by decide
  have hdescent : baseEnd_5293710 < baseStart_5293710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293750 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5293750 : Nat := 118140960795 + 5293750 * 2 ^ 59
def prefixEnd_5293750 : Nat := 4983230072969 + 3 ^ 40 * 5293750 * 2
def baseEnd_5293750 : Nat := 906079404912922804159831

theorem tailTrace_5293750 : CollatzResearch.WordTrace tailWord_5293750 prefixEnd_5293750 906079404912922804159831 := by
  unfold tailWord_5293750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12067432785728457835374419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128719283047770216910660469 12067432785728457835374419)
  ·
    refine ⟨18101149178592686753061629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12067432785728457835374419 18101149178592686753061629)
    ·
      refine ⟨6787930941972257532398111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18101149178592686753061629 6787930941972257532398111)
      ·
        refine ⟨10181896412958386298597167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6787930941972257532398111 10181896412958386298597167)
        ·
          refine ⟨15272844619437579447895751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10181896412958386298597167 15272844619437579447895751)
          ·
            refine ⟨22909266929156369171843627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15272844619437579447895751 22909266929156369171843627)
            ·
              refine ⟨34363900393734553757765441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22909266929156369171843627 34363900393734553757765441)
              ·
                refine ⟨25772925295300915318324081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34363900393734553757765441 25772925295300915318324081)
                ·
                  refine ⟨19329693971475686488743061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25772925295300915318324081 19329693971475686488743061)
                  ·
                    refine ⟨906079404912922804159831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19329693971475686488743061 906079404912922804159831)
                    ·
                      rfl

theorem cell23_5293750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5293750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293750 prefixEnd_5293750 := by exact prefixLift 5293750
  have htrace : WordTrace (prefixWord ++ tailWord_5293750) baseStart_5293750 baseEnd_5293750 := by
    simpa [prefixWord, tailWord_5293750, baseEnd_5293750] using wordTrace_append hprefix tailTrace_5293750
  have hstable : (prefixWord ++ tailWord_5293750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293750).length < 2 ^ (prefixWord ++ tailWord_5293750).sum := by decide
  have hdescent : baseEnd_5293750 < baseStart_5293750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293774 : List Nat := [4, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2]
def baseStart_5293774 : Nat := 118140960795 + 5293774 * 2 ^ 59
def prefixEnd_5293774 : Nat := 4983230072969 + 3 ^ 40 * 5293774 * 2
def baseEnd_5293774 : Nat := 2718250538274476318579383

theorem tailTrace_5293774 : CollatzResearch.WordTrace tailWord_5293774 prefixEnd_5293774 2718250538274476318579383 := by
  unfold tailWord_5293774
  simp only [CollatzResearch.WordTrace]
  refine ⟨24134974990446047183108047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128719866615712251643242917 24134974990446047183108047)
  ·
    refine ⟨36202462485669070774662071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24134974990446047183108047 36202462485669070774662071)
    ·
      refine ⟨54303693728503606161993107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36202462485669070774662071 54303693728503606161993107)
      ·
        refine ⟨81455540592755409242989661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54303693728503606161993107 81455540592755409242989661)
        ·
          refine ⟨30545827722283278466121123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81455540592755409242989661 30545827722283278466121123)
          ·
            refine ⟨45818741583424917699181685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30545827722283278466121123 45818741583424917699181685)
            ·
              refine ⟨4295507023446086034298283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45818741583424917699181685 4295507023446086034298283)
              ·
                refine ⟨6443260535169129051447425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4295507023446086034298283 6443260535169129051447425)
                ·
                  refine ⟨4832445401376846788585569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6443260535169129051447425 4832445401376846788585569)
                  ·
                    refine ⟨3624334051032635091439177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4832445401376846788585569 3624334051032635091439177)
                    ·
                      refine ⟨2718250538274476318579383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624334051032635091439177 2718250538274476318579383)
                      ·
                        rfl

theorem cell23_5293774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_5293774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293774 prefixEnd_5293774 := by exact prefixLift 5293774
  have htrace : WordTrace (prefixWord ++ tailWord_5293774) baseStart_5293774 baseEnd_5293774 := by
    simpa [prefixWord, tailWord_5293774, baseEnd_5293774] using wordTrace_append hprefix tailTrace_5293774
  have hstable : (prefixWord ++ tailWord_5293774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293774).length < 2 ^ (prefixWord ++ tailWord_5293774).sum := by decide
  have hdescent : baseEnd_5293774 < baseStart_5293774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293776 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 6, 5]
def baseStart_5293776 : Nat := 118140960795 + 5293776 * 2 ^ 59
def prefixEnd_5293776 : Nat := 4983230072969 + 3 ^ 40 * 5293776 * 2
def baseEnd_5293776 : Nat := 906083855078595103584791

theorem tailTrace_5293776 : CollatzResearch.WordTrace tailWord_5293776 prefixEnd_5293776 906083855078595103584791 := by
  unfold tailWord_5293776
  simp only [CollatzResearch.WordTrace]
  refine ⟨96539936434780565903218591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128719915246374087870958121 96539936434780565903218591)
  ·
    refine ⟨144809904652170848854827887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96539936434780565903218591 144809904652170848854827887)
    ·
      refine ⟨217214856978256273282241831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144809904652170848854827887 217214856978256273282241831)
      ·
        refine ⟨325822285467384409923362747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217214856978256273282241831 325822285467384409923362747)
        ·
          refine ⟨488733428201076614885044121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325822285467384409923362747 488733428201076614885044121)
          ·
            refine ⟨366550071150807461163783091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488733428201076614885044121 366550071150807461163783091)
            ·
              refine ⟨549825106726211191745674637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366550071150807461163783091 549825106726211191745674637)
              ·
                refine ⟨206184415022329196904627989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 549825106726211191745674637 206184415022329196904627989)
                ·
                  refine ⟨9664894454171681104904437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 206184415022329196904627989 9664894454171681104904437)
                  ·
                    refine ⟨906083855078595103584791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9664894454171681104904437 906083855078595103584791)
                    ·
                      rfl

theorem cell23_5293776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_5293776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293776 prefixEnd_5293776 := by exact prefixLift 5293776
  have htrace : WordTrace (prefixWord ++ tailWord_5293776) baseStart_5293776 baseEnd_5293776 := by
    simpa [prefixWord, tailWord_5293776, baseEnd_5293776] using wordTrace_append hprefix tailTrace_5293776
  have hstable : (prefixWord ++ tailWord_5293776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293776).length < 2 ^ (prefixWord ++ tailWord_5293776).sum := by decide
  have hdescent : baseEnd_5293776 < baseStart_5293776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293816 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_5293816 : Nat := 118140960795 + 5293816 * 2 ^ 59
def prefixEnd_5293816 : Nat := 4983230072969 + 3 ^ 40 * 5293816 * 2
def baseEnd_5293816 : Nat := 2718272104461965154254189

theorem tailTrace_5293816 : CollatzResearch.WordTrace tailWord_5293816 prefixEnd_5293816 2718272104461965154254189 := by
  unfold tailWord_5293816
  simp only [CollatzResearch.WordTrace]
  refine ⟨96540665894708109318946651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128720887859610812425262201 96540665894708109318946651)
  ·
    refine ⟨144810998842062163978419977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96540665894708109318946651 144810998842062163978419977)
    ·
      refine ⟨108608249131546622983814983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144810998842062163978419977 108608249131546622983814983)
      ·
        refine ⟨162912373697319934475722475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108608249131546622983814983 162912373697319934475722475)
        ·
          refine ⟨244368560545979901713583713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162912373697319934475722475 244368560545979901713583713)
          ·
            refine ⟨183276420409484926285187785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244368560545979901713583713 183276420409484926285187785)
            ·
              refine ⟨137457315307113694713890839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183276420409484926285187785 137457315307113694713890839)
              ·
                refine ⟨206185972960670542070836259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137457315307113694713890839 206185972960670542070836259)
                ·
                  refine ⟨309278959441005813106254389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206185972960670542070836259 309278959441005813106254389)
                  ·
                    refine ⟨28994902447594294978711349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 309278959441005813106254389 28994902447594294978711349)
                    ·
                      refine ⟨2718272104461965154254189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28994902447594294978711349 2718272104461965154254189)
                      ·
                        rfl

theorem cell23_5293816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_5293816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293816 prefixEnd_5293816 := by exact prefixLift 5293816
  have htrace : WordTrace (prefixWord ++ tailWord_5293816) baseStart_5293816 baseEnd_5293816 := by
    simpa [prefixWord, tailWord_5293816, baseEnd_5293816] using wordTrace_append hprefix tailTrace_5293816
  have hstable : (prefixWord ++ tailWord_5293816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293816).length < 2 ^ (prefixWord ++ tailWord_5293816).sum := by decide
  have hdescent : baseEnd_5293816 < baseStart_5293816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293833 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 6, 2, 3]
def baseStart_5293833 : Nat := 118140960795 + 5293833 * 2 ^ 59
def prefixEnd_5293833 : Nat := 4983230072969 + 3 ^ 40 * 5293833 * 2
def baseEnd_5293833 : Nat := 2718280833633091587741611

theorem tailTrace_5293833 : CollatzResearch.WordTrace tailWord_5293833 prefixEnd_5293833 2718280833633091587741611 := by
  unfold tailWord_5293833
  simp only [CollatzResearch.WordTrace]
  refine ⟨193081951830354630541262153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128721301220236420360841435 193081951830354630541262153)
  ·
    refine ⟨144811463872765972905946615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193081951830354630541262153 144811463872765972905946615)
    ·
      refine ⟨217217195809148959358919923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144811463872765972905946615 217217195809148959358919923)
      ·
        refine ⟨325825793713723439038379885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217217195809148959358919923 325825793713723439038379885)
        ·
          refine ⟨122184672642646289639392457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325825793713723439038379885 122184672642646289639392457)
          ·
            refine ⟨91638504481984717229544343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122184672642646289639392457 91638504481984717229544343)
            ·
              refine ⟨137457756722977075844316515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91638504481984717229544343 137457756722977075844316515)
              ·
                refine ⟨206186635084465613766474773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137457756722977075844316515 206186635084465613766474773)
                ·
                  refine ⟨9664998519584325645303505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 206186635084465613766474773 9664998519584325645303505)
                  ·
                    refine ⟨7248748889688244233977629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9664998519584325645303505 7248748889688244233977629)
                    ·
                      refine ⟨2718280833633091587741611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7248748889688244233977629 2718280833633091587741611)
                      ·
                        rfl

theorem cell23_5293833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 2, 3].length) (baseStart_5293833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293833 prefixEnd_5293833 := by exact prefixLift 5293833
  have htrace : WordTrace (prefixWord ++ tailWord_5293833) baseStart_5293833 baseEnd_5293833 := by
    simpa [prefixWord, tailWord_5293833, baseEnd_5293833] using wordTrace_append hprefix tailTrace_5293833
  have hstable : (prefixWord ++ tailWord_5293833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293833).length < 2 ^ (prefixWord ++ tailWord_5293833).sum := by decide
  have hdescent : baseEnd_5293833 < baseStart_5293833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293850 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3]
def baseStart_5293850 : Nat := 118140960795 + 5293850 * 2 ^ 59
def prefixEnd_5293850 : Nat := 4983230072969 + 3 ^ 40 * 5293850 * 2
def baseEnd_5293850 : Nat := 2718289562804218021229033

theorem tailTrace_5293850 : CollatzResearch.WordTrace tailWord_5293850 prefixEnd_5293850 2718289562804218021229033 := by
  unfold tailWord_5293850
  simp only [CollatzResearch.WordTrace]
  refine ⟨48270642967823260611157751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128721714580862028296420669 48270642967823260611157751)
  ·
    refine ⟨72405964451734890916736627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48270642967823260611157751 72405964451734890916736627)
    ·
      refine ⟨108608946677602336375104941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72405964451734890916736627 108608946677602336375104941)
      ·
        refine ⟨40728355004100876140664353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108608946677602336375104941 40728355004100876140664353)
        ·
          refine ⟨30546266253075657105498265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40728355004100876140664353 30546266253075657105498265)
          ·
            refine ⟨22909699689806742829123699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30546266253075657105498265 22909699689806742829123699)
            ·
              refine ⟨34364549534710114243685549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22909699689806742829123699 34364549534710114243685549)
              ·
                refine ⟨12886706075516292841382081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34364549534710114243685549 12886706075516292841382081)
                ·
                  refine ⟨9665029556637219631036561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12886706075516292841382081 9665029556637219631036561)
                  ·
                    refine ⟨7248772167477914723277421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9665029556637219631036561 7248772167477914723277421)
                    ·
                      refine ⟨2718289562804218021229033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7248772167477914723277421 2718289562804218021229033)
                      ·
                        rfl

theorem cell23_5293850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_5293850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293850 prefixEnd_5293850 := by exact prefixLift 5293850
  have htrace : WordTrace (prefixWord ++ tailWord_5293850) baseStart_5293850 baseEnd_5293850 := by
    simpa [prefixWord, tailWord_5293850, baseEnd_5293850] using wordTrace_append hprefix tailTrace_5293850
  have hstable : (prefixWord ++ tailWord_5293850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293850).length < 2 ^ (prefixWord ++ tailWord_5293850).sum := by decide
  have hdescent : baseEnd_5293850 < baseStart_5293850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293874 : List Nat := [3, 2, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_5293874 : Nat := 118140960795 + 5293874 * 2 ^ 59
def prefixEnd_5293874 : Nat := 4983230072969 + 3 ^ 40 * 5293874 * 2
def baseEnd_5293874 : Nat := 906100628779975309109641

theorem tailTrace_5293874 : CollatzResearch.WordTrace tailWord_5293874 prefixEnd_5293874 906100628779975309109641 := by
  unfold tailWord_5293874
  simp only [CollatzResearch.WordTrace]
  refine ⟨48270861805801523635876169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128722298148804063029003117 48270861805801523635876169)
  ·
    refine ⟨36203146354351142726907127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48270861805801523635876169 36203146354351142726907127)
    ·
      refine ⟨54304719531526714090360691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36203146354351142726907127 54304719531526714090360691)
      ·
        refine ⟨81457079297290071135541037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54304719531526714090360691 81457079297290071135541037)
        ·
          refine ⟨30546404736483776675827889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81457079297290071135541037 30546404736483776675827889)
          ·
            refine ⟨22909803552362832506870917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30546404736483776675827889 22909803552362832506870917)
            ·
              refine ⟨4295588166068031095038297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22909803552362832506870917 4295588166068031095038297)
              ·
                refine ⟨3221691124551023321278723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4295588166068031095038297 3221691124551023321278723)
                ·
                  refine ⟨4832536686826534981918085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221691124551023321278723 4832536686826534981918085)
                  ·
                    refine ⟨906100628779975309109641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4832536686826534981918085 906100628779975309109641)
                    ·
                      rfl

theorem cell23_5293874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_5293874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293874 prefixEnd_5293874 := by exact prefixLift 5293874
  have htrace : WordTrace (prefixWord ++ tailWord_5293874) baseStart_5293874 baseEnd_5293874 := by
    simpa [prefixWord, tailWord_5293874, baseEnd_5293874] using wordTrace_append hprefix tailTrace_5293874
  have hstable : (prefixWord ++ tailWord_5293874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293874).length < 2 ^ (prefixWord ++ tailWord_5293874).sum := by decide
  have hdescent : baseEnd_5293874 < baseStart_5293874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293913 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 1, 6]
def baseStart_5293913 : Nat := 118140960795 + 5293913 * 2 ^ 59
def prefixEnd_5293913 : Nat := 4983230072969 + 3 ^ 40 * 5293913 * 2
def baseEnd_5293913 : Nat := 906107304028483758247081

theorem tailTrace_5293913 : CollatzResearch.WordTrace tailWord_5293913 prefixEnd_5293913 906107304028483758247081 := by
  unfold tailWord_5293913
  simp only [CollatzResearch.WordTrace]
  refine ⟨193084869670064804204174393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128723246446709869469449595 193084869670064804204174393)
  ·
    refine ⟨144813652252548603153130795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193084869670064804204174393 144813652252548603153130795)
    ·
      refine ⟨217220478378822904729696193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144813652252548603153130795 217220478378822904729696193)
      ·
        refine ⟨162915358784117178547272145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217220478378822904729696193 162915358784117178547272145)
        ·
          refine ⟨122186519088087883910454109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162915358784117178547272145 122186519088087883910454109)
          ·
            refine ⟨45819944658032956466420291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122186519088087883910454109 45819944658032956466420291)
            ·
              refine ⟨68729916987049434699630437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45819944658032956466420291 68729916987049434699630437)
              ·
                refine ⟨12886859435071769006180707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68729916987049434699630437 12886859435071769006180707)
                ·
                  refine ⟨19330289152607653509271061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12886859435071769006180707 19330289152607653509271061)
                  ·
                    refine ⟨906107304028483758247081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19330289152607653509271061 906107304028483758247081)
                    ·
                      rfl

theorem cell23_5293913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_5293913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293913 prefixEnd_5293913 := by exact prefixLift 5293913
  have htrace : WordTrace (prefixWord ++ tailWord_5293913) baseStart_5293913 baseEnd_5293913 := by
    simpa [prefixWord, tailWord_5293913, baseEnd_5293913] using wordTrace_append hprefix tailTrace_5293913
  have hstable : (prefixWord ++ tailWord_5293913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293913).length < 2 ^ (prefixWord ++ tailWord_5293913).sum := by decide
  have hdescent : baseEnd_5293913 < baseStart_5293913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293914 : List Nat := [3, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3]
def baseStart_5293914 : Nat := 118140960795 + 5293914 * 2 ^ 59
def prefixEnd_5293914 : Nat := 4983230072969 + 3 ^ 40 * 5293914 * 2
def baseEnd_5293914 : Nat := 2718322425566105770828739

theorem tailTrace_5293914 : CollatzResearch.WordTrace tailWord_5293914 prefixEnd_5293914 2718322425566105770828739 := by
  unfold tailWord_5293914
  simp only [CollatzResearch.WordTrace]
  refine ⟨48271226535765295343740199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128723270762040787583307197 48271226535765295343740199)
  ·
    refine ⟨72406839803647943015610299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48271226535765295343740199 72406839803647943015610299)
    ·
      refine ⟨108610259705471914523415449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72406839803647943015610299 108610259705471914523415449)
      ·
        refine ⟨81457694779103935892561587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108610259705471914523415449 81457694779103935892561587)
        ·
          refine ⟨122186542168655903838842381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81457694779103935892561587 122186542168655903838842381)
          ·
            refine ⟨45819953313245963939565893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122186542168655903838842381 45819953313245963939565893)
            ·
              refine ⟨8591241246233618238668605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45819953313245963939565893 8591241246233618238668605)
              ·
                refine ⟨3221715467337606839500727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8591241246233618238668605 3221715467337606839500727)
                ·
                  refine ⟨4832573201006410259251091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221715467337606839500727 4832573201006410259251091)
                  ·
                    refine ⟨7248859801509615388876637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4832573201006410259251091 7248859801509615388876637)
                    ·
                      refine ⟨2718322425566105770828739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7248859801509615388876637 2718322425566105770828739)
                      ·
                        rfl

theorem cell23_5293914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_5293914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293914 prefixEnd_5293914 := by exact prefixLift 5293914
  have htrace : WordTrace (prefixWord ++ tailWord_5293914) baseStart_5293914 baseEnd_5293914 := by
    simpa [prefixWord, tailWord_5293914, baseEnd_5293914] using wordTrace_append hprefix tailTrace_5293914
  have hstable : (prefixWord ++ tailWord_5293914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293914).length < 2 ^ (prefixWord ++ tailWord_5293914).sum := by decide
  have hdescent : baseEnd_5293914 < baseStart_5293914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293957 : List Nat := [1, 3, 1, 1, 3, 2, 4, 2, 1, 2, 3]
def baseStart_5293957 : Nat := 118140960795 + 5293957 * 2 ^ 59
def prefixEnd_5293957 : Nat := 4983230072969 + 3 ^ 40 * 5293957 * 2
def baseEnd_5293957 : Nat := 2718344505234249102591041

theorem tailTrace_5293957 : CollatzResearch.WordTrace tailWord_5293957 prefixEnd_5293957 2718344505234249102591041 := by
  unfold tailWord_5293957
  simp only [CollatzResearch.WordTrace]
  refine ⟨193086474481905399718776125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128724316321270266479184083 193086474481905399718776125)
  ·
    refine ⟨72407427930714524894541047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193086474481905399718776125 72407427930714524894541047)
    ·
      refine ⟨108611141896071787341811571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72407427930714524894541047 108611141896071787341811571)
      ·
        refine ⟨162916712844107681012717357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108611141896071787341811571 162916712844107681012717357)
        ·
          refine ⟨61093767316540380379769009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162916712844107681012717357 61093767316540380379769009)
          ·
            refine ⟨45820325487405285284826757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61093767316540380379769009 45820325487405285284826757)
            ·
              refine ⟨8591311028888490990905017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45820325487405285284826757 8591311028888490990905017)
              ·
                refine ⟨6443483271666368243178763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8591311028888490990905017 6443483271666368243178763)
                ·
                  refine ⟨9665224907499552364768145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6443483271666368243178763 9665224907499552364768145)
                  ·
                    refine ⟨7248918680624664273576109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9665224907499552364768145 7248918680624664273576109)
                    ·
                      refine ⟨2718344505234249102591041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7248918680624664273576109 2718344505234249102591041)
                      ·
                        rfl

theorem cell23_5293957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_5293957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293957 prefixEnd_5293957 := by exact prefixLift 5293957
  have htrace : WordTrace (prefixWord ++ tailWord_5293957) baseStart_5293957 baseEnd_5293957 := by
    simpa [prefixWord, tailWord_5293957, baseEnd_5293957] using wordTrace_append hprefix tailTrace_5293957
  have hstable : (prefixWord ++ tailWord_5293957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293957).length < 2 ^ (prefixWord ++ tailWord_5293957).sum := by decide
  have hdescent : baseEnd_5293957 < baseStart_5293957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293960 : List Nat := [2, 1, 3, 3, 3, 1, 1, 9]
def baseStart_5293960 : Nat := 118140960795 + 5293960 * 2 ^ 59
def prefixEnd_5293960 : Nat := 4983230072969 + 3 ^ 40 * 5293960 * 2
def baseEnd_5293960 : Nat := 100679483173193058920501

theorem tailTrace_5293960 : CollatzResearch.WordTrace tailWord_5293960 prefixEnd_5293960 100679483173193058920501 := by
  unfold tailWord_5293960
  simp only [CollatzResearch.WordTrace]
  refine ⟨96543291950447265615567667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128724389267263020820756889 96543291950447265615567667)
  ·
    refine ⟨144814937925670898423351501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96543291950447265615567667 144814937925670898423351501)
    ·
      refine ⟨54305601722126586908756813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144814937925670898423351501 54305601722126586908756813)
      ·
        refine ⟨20364600645797470090783805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54305601722126586908756813 20364600645797470090783805)
        ·
          refine ⟨7636725242174051284043927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20364600645797470090783805 7636725242174051284043927)
          ·
            refine ⟨11455087863261076926065891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7636725242174051284043927 11455087863261076926065891)
            ·
              refine ⟨17182631794891615389098837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11455087863261076926065891 17182631794891615389098837)
              ·
                refine ⟨100679483173193058920501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17182631794891615389098837 100679483173193058920501)
                ·
                  rfl

theorem cell23_5293960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 9].length) (baseStart_5293960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293960 prefixEnd_5293960 := by exact prefixLift 5293960
  have htrace : WordTrace (prefixWord ++ tailWord_5293960) baseStart_5293960 baseEnd_5293960 := by
    simpa [prefixWord, tailWord_5293960, baseEnd_5293960] using wordTrace_append hprefix tailTrace_5293960
  have hstable : (prefixWord ++ tailWord_5293960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293960).length < 2 ^ (prefixWord ++ tailWord_5293960).sum := by decide
  have hdescent : baseEnd_5293960 < baseStart_5293960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293987 : List Nat := [1, 1, 1, 4, 1, 2, 1, 6, 2, 1, 3]
def baseStart_5293987 : Nat := 118140960795 + 5293987 * 2 ^ 59
def prefixEnd_5293987 : Nat := 4983230072969 + 3 ^ 40 * 5293987 * 2
def baseEnd_5293987 : Nat := 2718359909653883985215903

theorem tailTrace_5293987 : CollatzResearch.WordTrace tailWord_5293987 prefixEnd_5293987 2718359909653883985215903 := by
  unfold tailWord_5293987
  simp only [CollatzResearch.WordTrace]
  refine ⟨193087568671796714842368215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128725045781197809894912143 193087568671796714842368215)
  ·
    refine ⟨289631353007695072263552323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193087568671796714842368215 289631353007695072263552323)
    ·
      refine ⟨434447029511542608395328485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289631353007695072263552323 434447029511542608395328485)
      ·
        refine ⟨81458818033414239074124091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 434447029511542608395328485 81458818033414239074124091)
        ·
          refine ⟨122188227050121358611186137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81458818033414239074124091 122188227050121358611186137)
          ·
            refine ⟨91641170287591018958389603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122188227050121358611186137 91641170287591018958389603)
            ·
              refine ⟨137461755431386528437584405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91641170287591018958389603 137461755431386528437584405)
              ·
                refine ⟨6443519785846243520511769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137461755431386528437584405 6443519785846243520511769)
                ·
                  refine ⟨4832639839384682640383827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6443519785846243520511769 4832639839384682640383827)
                  ·
                    refine ⟨7248959759077023960575741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4832639839384682640383827 7248959759077023960575741)
                    ·
                      refine ⟨2718359909653883985215903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7248959759077023960575741 2718359909653883985215903)
                      ·
                        rfl

theorem cell23_5293987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_5293987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293987 prefixEnd_5293987 := by exact prefixLift 5293987
  have htrace : WordTrace (prefixWord ++ tailWord_5293987) baseStart_5293987 baseEnd_5293987 := by
    simpa [prefixWord, tailWord_5293987, baseEnd_5293987] using wordTrace_append hprefix tailTrace_5293987
  have hstable : (prefixWord ++ tailWord_5293987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293987).length < 2 ^ (prefixWord ++ tailWord_5293987).sum := by decide
  have hdescent : baseEnd_5293987 < baseStart_5293987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293988 : List Nat := [2, 3, 1, 2, 1, 4, 3, 2, 1, 2, 2]
def baseStart_5293988 : Nat := 118140960795 + 5293988 * 2 ^ 59
def prefixEnd_5293988 : Nat := 4983230072969 + 3 ^ 40 * 5293988 * 2
def baseEnd_5293988 : Nat := 2718360423134538481303399

theorem tailTrace_5293988 : CollatzResearch.WordTrace tailWord_5293988 prefixEnd_5293988 2718360423134538481303399 := by
  unfold tailWord_5293988
  simp only [CollatzResearch.WordTrace]
  refine ⟨96543802572396546006577309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128725070096528728008769745 96543802572396546006577309)
  ·
    refine ⟨36203925964648704752466491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96543802572396546006577309 36203925964648704752466491)
    ·
      refine ⟨54305888946973057128699737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36203925964648704752466491 54305888946973057128699737)
      ·
        refine ⟨40729416710229792846524803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54305888946973057128699737 40729416710229792846524803)
        ·
          refine ⟨61094125065344689269787205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40729416710229792846524803 61094125065344689269787205)
          ·
            refine ⟨11455148449752129238085101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61094125065344689269787205 11455148449752129238085101)
            ·
              refine ⟨4295680668657048464281913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11455148449752129238085101 4295680668657048464281913)
              ·
                refine ⟨3221760501492786348211435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4295680668657048464281913 3221760501492786348211435)
                ·
                  refine ⟨4832640752239179522317153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221760501492786348211435 4832640752239179522317153)
                  ·
                    refine ⟨3624480564179384641737865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4832640752239179522317153 3624480564179384641737865)
                    ·
                      refine ⟨2718360423134538481303399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624480564179384641737865 2718360423134538481303399)
                      ·
                        rfl

theorem cell23_5293988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_5293988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293988 prefixEnd_5293988 := by exact prefixLift 5293988
  have htrace : WordTrace (prefixWord ++ tailWord_5293988) baseStart_5293988 baseEnd_5293988 := by
    simpa [prefixWord, tailWord_5293988, baseEnd_5293988] using wordTrace_append hprefix tailTrace_5293988
  have hstable : (prefixWord ++ tailWord_5293988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293988).length < 2 ^ (prefixWord ++ tailWord_5293988).sum := by decide
  have hdescent : baseEnd_5293988 < baseStart_5293988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5293998 : List Nat := [4, 1, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5293998 : Nat := 118140960795 + 5293998 * 2 ^ 59
def prefixEnd_5293998 : Nat := 4983230072969 + 3 ^ 40 * 5293998 * 2
def baseEnd_5293998 : Nat := 906121852647027814059451

theorem tailTrace_5293998 : CollatzResearch.WordTrace tailWord_5293998 prefixEnd_5293998 906121852647027814059451 := by
  unfold tailWord_5293998
  simp only [CollatzResearch.WordTrace]
  refine ⟨24135996234344607965127331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128725313249837909147345765 24135996234344607965127331)
  ·
    refine ⟨36203994351516911947690997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24135996234344607965127331 36203994351516911947690997)
    ·
      refine ⟨3394124470454710495096031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36203994351516911947690997 3394124470454710495096031)
      ·
        refine ⟨5091186705682065742644047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3394124470454710495096031 5091186705682065742644047)
        ·
          refine ⟨7636780058523098613966071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5091186705682065742644047 7636780058523098613966071)
          ·
            refine ⟨11455170087784647920949107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7636780058523098613966071 11455170087784647920949107)
            ·
              refine ⟨17182755131676971881423661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11455170087784647920949107 17182755131676971881423661)
              ·
                refine ⟨6443533174378864455533873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17182755131676971881423661 6443533174378864455533873)
                ·
                  refine ⟨4832649880784148341650405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6443533174378864455533873 4832649880784148341650405)
                  ·
                    refine ⟨906121852647027814059451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4832649880784148341650405 906121852647027814059451)
                    ·
                      rfl

theorem cell23_5293998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5293998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5293998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5293998 prefixEnd_5293998 := by exact prefixLift 5293998
  have htrace : WordTrace (prefixWord ++ tailWord_5293998) baseStart_5293998 baseEnd_5293998 := by
    simpa [prefixWord, tailWord_5293998, baseEnd_5293998] using wordTrace_append hprefix tailTrace_5293998
  have hstable : (prefixWord ++ tailWord_5293998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5293998).length < 2 ^ (prefixWord ++ tailWord_5293998).sum := by decide
  have hdescent : baseEnd_5293998 < baseStart_5293998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5293998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294003 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 1, 8]
def baseStart_5294003 : Nat := 118140960795 + 5294003 * 2 ^ 59
def prefixEnd_5294003 : Nat := 4983230072969 + 3 ^ 40 * 5294003 * 2
def baseEnd_5294003 : Nat := 906122708448118640871943

theorem tailTrace_5294003 : CollatzResearch.WordTrace tailWord_5294003 prefixEnd_5294003 906122708448118640871943 := by
  unfold tailWord_5294003
  simp only [CollatzResearch.WordTrace]
  refine ⟨193088152239738749574950663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128725434826492499716633775 193088152239738749574950663)
  ·
    refine ⟨289632228359608124362425995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193088152239738749574950663 289632228359608124362425995)
    ·
      refine ⟨434448342539412186543638993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289632228359608124362425995 434448342539412186543638993)
      ·
        refine ⟨325836256904559139907729245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434448342539412186543638993 325836256904559139907729245)
        ·
          refine ⟨122188596339209677465398467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325836256904559139907729245 122188596339209677465398467)
          ·
            refine ⟨183282894508814516198097701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122188596339209677465398467 183282894508814516198097701)
            ·
              refine ⟨34365542720402721787143319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183282894508814516198097701 34365542720402721787143319)
              ·
                refine ⟨51548314080604082680714979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34365542720402721787143319 51548314080604082680714979)
                ·
                  refine ⟨77322471120906124021072469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51548314080604082680714979 77322471120906124021072469)
                  ·
                    refine ⟨906122708448118640871943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77322471120906124021072469 906122708448118640871943)
                    ·
                      rfl

theorem cell23_5294003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 8].length) (baseStart_5294003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294003 prefixEnd_5294003 := by exact prefixLift 5294003
  have htrace : WordTrace (prefixWord ++ tailWord_5294003) baseStart_5294003 baseEnd_5294003 := by
    simpa [prefixWord, tailWord_5294003, baseEnd_5294003] using wordTrace_append hprefix tailTrace_5294003
  have hstable : (prefixWord ++ tailWord_5294003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294003).length < 2 ^ (prefixWord ++ tailWord_5294003).sum := by decide
  have hdescent : baseEnd_5294003 < baseStart_5294003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294014 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_5294014 : Nat := 118140960795 + 5294014 * 2 ^ 59
def prefixEnd_5294014 : Nat := 4983230072969 + 3 ^ 40 * 5294014 * 2
def baseEnd_5294014 : Nat := 2718373773631555379578279

theorem tailTrace_5294014 : CollatzResearch.WordTrace tailWord_5294014 prefixEnd_5294014 2718373773631555379578279 := by
  unfold tailWord_5294014
  simp only [CollatzResearch.WordTrace]
  refine ⟨24136069180337362306700137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128725702295132598969067397 24136069180337362306700137)
  ·
    refine ⟨18102051885253021730025103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24136069180337362306700137 18102051885253021730025103)
    ·
      refine ⟨27153077827879532595037655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18102051885253021730025103 27153077827879532595037655)
      ·
        refine ⟨40729616741819298892556483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27153077827879532595037655 40729616741819298892556483)
        ·
          refine ⟨61094425112728948338834725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40729616741819298892556483 61094425112728948338834725)
          ·
            refine ⟨11455204708636677813531511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61094425112728948338834725 11455204708636677813531511)
            ·
              refine ⟨17182807062955016720297267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11455204708636677813531511 17182807062955016720297267)
              ·
                refine ⟨25774210594432525080445901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17182807062955016720297267 25774210594432525080445901)
                ·
                  refine ⟨9665328972912196905167213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25774210594432525080445901 9665328972912196905167213)
                  ·
                    refine ⟨3624498364842073839437705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9665328972912196905167213 3624498364842073839437705)
                    ·
                      refine ⟨2718373773631555379578279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624498364842073839437705 2718373773631555379578279)
                      ·
                        rfl

theorem cell23_5294014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_5294014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294014 prefixEnd_5294014 := by exact prefixLift 5294014
  have htrace : WordTrace (prefixWord ++ tailWord_5294014) baseStart_5294014 baseEnd_5294014 := by
    simpa [prefixWord, tailWord_5294014, baseEnd_5294014] using wordTrace_append hprefix tailTrace_5294014
  have hstable : (prefixWord ++ tailWord_5294014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294014).length < 2 ^ (prefixWord ++ tailWord_5294014).sum := by decide
  have hdescent : baseEnd_5294014 < baseStart_5294014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294027 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 1, 4, 2]
def baseStart_5294027 : Nat := 118140960795 + 5294027 * 2 ^ 59
def prefixEnd_5294027 : Nat := 4983230072969 + 3 ^ 40 * 5294027 * 2
def baseEnd_5294027 : Nat := 2718380448880063828715719

theorem tailTrace_5294027 : CollatzResearch.WordTrace tailWord_5294027 prefixEnd_5294027 2718380448880063828715719 := by
  unfold tailWord_5294027
  simp only [CollatzResearch.WordTrace]
  refine ⟨193089027591651801673824335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128726018394434534449216223 193089027591651801673824335)
  ·
    refine ⟨289633541387477702510736503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193089027591651801673824335 289633541387477702510736503)
    ·
      refine ⟨434450312081216553766104755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289633541387477702510736503 434450312081216553766104755)
      ·
        refine ⟨651675468121824830649157133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434450312081216553766104755 651675468121824830649157133)
        ·
          refine ⟨244378300545684311493433925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 651675468121824830649157133 244378300545684311493433925)
          ·
            refine ⟨45820931352315808405018861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 244378300545684311493433925 45820931352315808405018861)
            ·
              refine ⟨17182849257118428151882073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45820931352315808405018861 17182849257118428151882073)
              ·
                refine ⟨12887136942838821113911555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17182849257118428151882073 12887136942838821113911555)
                ·
                  refine ⟨19330705414258231670867333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12887136942838821113911555 19330705414258231670867333)
                  ·
                    refine ⟨3624507265173418438287625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19330705414258231670867333 3624507265173418438287625)
                    ·
                      refine ⟨2718380448880063828715719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624507265173418438287625 2718380448880063828715719)
                      ·
                        rfl

theorem cell23_5294027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 4, 2].length) (baseStart_5294027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294027 prefixEnd_5294027 := by exact prefixLift 5294027
  have htrace : WordTrace (prefixWord ++ tailWord_5294027) baseStart_5294027 baseEnd_5294027 := by
    simpa [prefixWord, tailWord_5294027, baseEnd_5294027] using wordTrace_append hprefix tailTrace_5294027
  have hstable : (prefixWord ++ tailWord_5294027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294027).length < 2 ^ (prefixWord ++ tailWord_5294027).sum := by decide
  have hdescent : baseEnd_5294027 < baseStart_5294027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294030 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_5294030 : Nat := 118140960795 + 5294030 * 2 ^ 59
def prefixEnd_5294030 : Nat := 4983230072969 + 3 ^ 40 * 5294030 * 2
def baseEnd_5294030 : Nat := 2718381989322027316978205

theorem tailTrace_5294030 : CollatzResearch.WordTrace tailWord_5294030 prefixEnd_5294030 2718381989322027316978205 := by
  unfold tailWord_5294030
  simp only [CollatzResearch.WordTrace]
  refine ⟨24136142126330116648272943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128726091340427288790789029 24136142126330116648272943)
  ·
    refine ⟨36204213189495174972409415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24136142126330116648272943 36204213189495174972409415)
    ·
      refine ⟨54306319784242762458614123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36204213189495174972409415 54306319784242762458614123)
      ·
        refine ⟨81459479676364143687921185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54306319784242762458614123 81459479676364143687921185)
        ·
          refine ⟨61094609757273107765940889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81459479676364143687921185 61094609757273107765940889)
          ·
            refine ⟨45820957317954830824455667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61094609757273107765940889 45820957317954830824455667)
            ·
              refine ⟨68731435976932246236683501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45820957317954830824455667 68731435976932246236683501)
              ·
                refine ⟨25774288491349592338756313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68731435976932246236683501 25774288491349592338756313)
                ·
                  refine ⟨19330716368512194254067235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25774288491349592338756313 19330716368512194254067235)
                  ·
                    refine ⟨28996074552768291381100853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19330716368512194254067235 28996074552768291381100853)
                    ·
                      refine ⟨2718381989322027316978205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28996074552768291381100853 2718381989322027316978205)
                      ·
                        rfl

theorem cell23_5294030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_5294030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294030 prefixEnd_5294030 := by exact prefixLift 5294030
  have htrace : WordTrace (prefixWord ++ tailWord_5294030) baseStart_5294030 baseEnd_5294030 := by
    simpa [prefixWord, tailWord_5294030, baseEnd_5294030] using wordTrace_append hprefix tailTrace_5294030
  have hstable : (prefixWord ++ tailWord_5294030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294030).length < 2 ^ (prefixWord ++ tailWord_5294030).sum := by decide
  have hdescent : baseEnd_5294030 < baseStart_5294030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294033 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 11]
def baseStart_5294033 : Nat := 118140960795 + 5294033 * 2 ^ 59
def prefixEnd_5294033 : Nat := 4983230072969 + 3 ^ 40 * 5294033 * 2
def baseEnd_5294033 : Nat := 302042614418221200582299

theorem tailTrace_5294033 : CollatzResearch.WordTrace tailWord_5294033 prefixEnd_5294033 302042614418221200582299 := by
  unfold tailWord_5294033
  simp only [CollatzResearch.WordTrace]
  refine ⟨193089246429630064698542753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128726164286420043132361835 193089246429630064698542753)
  ·
    refine ⟨144816934822222548523907065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193089246429630064698542753 144816934822222548523907065)
    ·
      refine ⟨108612701116666911392930299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144816934822222548523907065 108612701116666911392930299)
      ·
        refine ⟨162919051675000367089395449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108612701116666911392930299 162919051675000367089395449)
        ·
          refine ⟨122189288756250275317046587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162919051675000367089395449 122189288756250275317046587)
          ·
            refine ⟨183283933134375412975569881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122189288756250275317046587 183283933134375412975569881)
            ·
              refine ⟨137462949850781559731677411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183283933134375412975569881 137462949850781559731677411)
              ·
                refine ⟨206194424776172339597516117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137462949850781559731677411 206194424776172339597516117)
                ·
                  refine ⟨302042614418221200582299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 206194424776172339597516117 302042614418221200582299)
                  ·
                    rfl

theorem cell23_5294033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 11].length) (baseStart_5294033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294033 prefixEnd_5294033 := by exact prefixLift 5294033
  have htrace : WordTrace (prefixWord ++ tailWord_5294033) baseStart_5294033 baseEnd_5294033 := by
    simpa [prefixWord, tailWord_5294033, baseEnd_5294033] using wordTrace_append hprefix tailTrace_5294033
  have hstable : (prefixWord ++ tailWord_5294033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294033).length < 2 ^ (prefixWord ++ tailWord_5294033).sum := by decide
  have hdescent : baseEnd_5294033 < baseStart_5294033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294038 : List Nat := [5, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_5294038 : Nat := 118140960795 + 5294038 * 2 ^ 59
def prefixEnd_5294038 : Nat := 4983230072969 + 3 ^ 40 * 5294038 * 2
def baseEnd_5294038 : Nat := 2718386097167263285678169

theorem tailTrace_5294038 : CollatzResearch.WordTrace tailWord_5294038 prefixEnd_5294038 2718386097167263285678169 := by
  unfold tailWord_5294038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12068089299663246909529673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128726285863074633701649845 12068089299663246909529673)
  ·
    refine ⟨9051066974747435182147255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12068089299663246909529673 9051066974747435182147255)
    ·
      refine ⟨13576600462121152773220883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9051066974747435182147255 13576600462121152773220883)
      ·
        refine ⟨20364900693181729159831325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13576600462121152773220883 20364900693181729159831325)
        ·
          refine ⟨7636837759943148434936747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20364900693181729159831325 7636837759943148434936747)
          ·
            refine ⟨11455256639914722652405121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7636837759943148434936747 11455256639914722652405121)
            ·
              refine ⟨8591442479936041989303841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11455256639914722652405121 8591442479936041989303841)
              ·
                refine ⟨6443581859952031491977881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8591442479936041989303841 6443581859952031491977881)
                ·
                  refine ⟨4832686394964023618983411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6443581859952031491977881 4832686394964023618983411)
                  ·
                    refine ⟨7249029592446035428475117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4832686394964023618983411 7249029592446035428475117)
                    ·
                      refine ⟨2718386097167263285678169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7249029592446035428475117 2718386097167263285678169)
                      ·
                        rfl

theorem cell23_5294038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_5294038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294038 prefixEnd_5294038 := by exact prefixLift 5294038
  have htrace : WordTrace (prefixWord ++ tailWord_5294038) baseStart_5294038 baseEnd_5294038 := by
    simpa [prefixWord, tailWord_5294038, baseEnd_5294038] using wordTrace_append hprefix tailTrace_5294038
  have hstable : (prefixWord ++ tailWord_5294038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294038).length < 2 ^ (prefixWord ++ tailWord_5294038).sum := by decide
  have hdescent : baseEnd_5294038 < baseStart_5294038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294040 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_5294040 : Nat := 118140960795 + 5294040 * 2 ^ 59
def prefixEnd_5294040 : Nat := 4983230072969 + 3 ^ 40 * 5294040 * 2
def baseEnd_5294040 : Nat := 2718387124128572277853159

theorem tailTrace_5294040 : CollatzResearch.WordTrace tailWord_5294040 prefixEnd_5294040 2718387124128572277853159 := by
  unfold tailWord_5294040
  simp only [CollatzResearch.WordTrace]
  refine ⟨96544750870302352447023787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128726334493736469929365049 96544750870302352447023787)
  ·
    refine ⟨144817126305453528670535681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96544750870302352447023787 144817126305453528670535681)
    ·
      refine ⟨108612844729090146502901761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144817126305453528670535681 108612844729090146502901761)
      ·
        refine ⟨81459633546817609877176321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108612844729090146502901761 81459633546817609877176321)
        ·
          refine ⟨61094725160113207407882241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81459633546817609877176321 61094725160113207407882241)
          ·
            refine ⟨45821043870084905555911681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61094725160113207407882241 45821043870084905555911681)
            ·
              refine ⟨34365782902563679166933761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45821043870084905555911681 34365782902563679166933761)
              ·
                refine ⟨25774337176922759375200321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34365782902563679166933761 25774337176922759375200321)
                ·
                  refine ⟨19330752882692069531400241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25774337176922759375200321 19330752882692069531400241)
                  ·
                    refine ⟨14498064662019052148550181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19330752882692069531400241 14498064662019052148550181)
                    ·
                      refine ⟨2718387124128572277853159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14498064662019052148550181 2718387124128572277853159)
                      ·
                        rfl

theorem cell23_5294040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_5294040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294040 prefixEnd_5294040 := by exact prefixLift 5294040
  have htrace : WordTrace (prefixWord ++ tailWord_5294040) baseStart_5294040 baseEnd_5294040 := by
    simpa [prefixWord, tailWord_5294040, baseEnd_5294040] using wordTrace_append hprefix tailTrace_5294040
  have hstable : (prefixWord ++ tailWord_5294040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294040).length < 2 ^ (prefixWord ++ tailWord_5294040).sum := by decide
  have hdescent : baseEnd_5294040 < baseStart_5294040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294080 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 2, 5]
def baseStart_5294080 : Nat := 118140960795 + 5294080 * 2 ^ 59
def prefixEnd_5294080 : Nat := 4983230072969 + 3 ^ 40 * 5294080 * 2
def baseEnd_5294080 : Nat := 906135887784917373784325

theorem tailTrace_5294080 : CollatzResearch.WordTrace tailWord_5294080 prefixEnd_5294080 906135887784917373784325 := by
  unfold tailWord_5294080
  simp only [CollatzResearch.WordTrace]
  refine ⟨96545480330229895862751847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128727307106973194483669129 96545480330229895862751847)
  ·
    refine ⟨144818220495344843794127771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96545480330229895862751847 144818220495344843794127771)
    ·
      refine ⟨217227330743017265691191657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144818220495344843794127771 217227330743017265691191657)
      ·
        refine ⟨162920498057262949268393743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217227330743017265691191657 162920498057262949268393743)
        ·
          refine ⟨244380747085894423902590615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162920498057262949268393743 244380747085894423902590615)
          ·
            refine ⟨366571120628841635853885923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244380747085894423902590615 366571120628841635853885923)
            ·
              refine ⟨549856680943262453780828885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366571120628841635853885923 549856680943262453780828885)
              ·
                refine ⟨12887265959607713760488177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 549856680943262453780828885 12887265959607713760488177)
                ·
                  refine ⟨9665449469705785320366133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12887265959607713760488177 9665449469705785320366133)
                  ·
                    refine ⟨906135887784917373784325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9665449469705785320366133 906135887784917373784325)
                    ·
                      rfl

theorem cell23_5294080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_5294080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294080 prefixEnd_5294080 := by exact prefixLift 5294080
  have htrace : WordTrace (prefixWord ++ tailWord_5294080) baseStart_5294080 baseEnd_5294080 := by
    simpa [prefixWord, tailWord_5294080, baseEnd_5294080] using wordTrace_append hprefix tailTrace_5294080
  have hstable : (prefixWord ++ tailWord_5294080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294080).length < 2 ^ (prefixWord ++ tailWord_5294080).sum := by decide
  have hdescent : baseEnd_5294080 < baseStart_5294080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294134 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_5294134 : Nat := 118140960795 + 5294134 * 2 ^ 59
def prefixEnd_5294134 : Nat := 4983230072969 + 3 ^ 40 * 5294134 * 2
def baseEnd_5294134 : Nat := 2718435391310094910077727

theorem tailTrace_5294134 : CollatzResearch.WordTrace tailWord_5294134 prefixEnd_5294134 2718435391310094910077727 := by
  unfold tailWord_5294134
  simp only [CollatzResearch.WordTrace]
  refine ⟨12068308137641509934248091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128728620134842772631979637 12068308137641509934248091)
  ·
    refine ⟨18102462206462264901372137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12068308137641509934248091 18102462206462264901372137)
    ·
      refine ⟨13576846654846698676029103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18102462206462264901372137 13576846654846698676029103)
      ·
        refine ⟨20365269982270048014043655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13576846654846698676029103 20365269982270048014043655)
        ·
          refine ⟨30547904973405072021065483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20365269982270048014043655 30547904973405072021065483)
          ·
            refine ⟨45821857460107608031598225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30547904973405072021065483 45821857460107608031598225)
            ·
              refine ⟨34366393095080706023698669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45821857460107608031598225 34366393095080706023698669)
              ·
                refine ⟨12887397410655264758887001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34366393095080706023698669 12887397410655264758887001)
                ·
                  refine ⟨9665548057991448569165251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12887397410655264758887001 9665548057991448569165251)
                  ·
                    refine ⟨14498322086987172853747877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9665548057991448569165251 14498322086987172853747877)
                    ·
                      refine ⟨2718435391310094910077727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14498322086987172853747877 2718435391310094910077727)
                      ·
                        rfl

theorem cell23_5294134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_5294134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294134 prefixEnd_5294134 := by exact prefixLift 5294134
  have htrace : WordTrace (prefixWord ++ tailWord_5294134) baseStart_5294134 baseEnd_5294134 := by
    simpa [prefixWord, tailWord_5294134, baseEnd_5294134] using wordTrace_append hprefix tailTrace_5294134
  have hstable : (prefixWord ++ tailWord_5294134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294134).length < 2 ^ (prefixWord ++ tailWord_5294134).sum := by decide
  have hdescent : baseEnd_5294134 < baseStart_5294134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294140 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 10]
def baseStart_5294140 : Nat := 118140960795 + 5294140 * 2 ^ 59
def prefixEnd_5294140 : Nat := 4983230072969 + 3 ^ 40 * 5294140 * 2
def baseEnd_5294140 : Nat := 302048719132669098511411

theorem tailTrace_5294140 : CollatzResearch.WordTrace tailWord_5294140 prefixEnd_5294140 302048719132669098511411 := by
  unfold tailWord_5294140
  simp only [CollatzResearch.WordTrace]
  refine ⟨96546574520121210986343937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128728766026828281315125249 96546574520121210986343937)
  ·
    refine ⟨72409930890090908239757953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96546574520121210986343937 72409930890090908239757953)
    ·
      refine ⟨54307448167568181179818465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72409930890090908239757953 54307448167568181179818465)
      ·
        refine ⟨40730586125676135884863849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54307448167568181179818465 40730586125676135884863849)
        ·
          refine ⟨30547939594257101913647887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40730586125676135884863849 30547939594257101913647887)
          ·
            refine ⟨45821909391385652870471831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30547939594257101913647887 45821909391385652870471831)
            ·
              refine ⟨68732864087078479305707747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45821909391385652870471831 68732864087078479305707747)
              ·
                refine ⟨103099296130617718958561621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68732864087078479305707747 103099296130617718958561621)
                ·
                  refine ⟨302048719132669098511411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 103099296130617718958561621 302048719132669098511411)
                  ·
                    rfl

theorem cell23_5294140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_5294140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294140 prefixEnd_5294140 := by exact prefixLift 5294140
  have htrace : WordTrace (prefixWord ++ tailWord_5294140) baseStart_5294140 baseEnd_5294140 := by
    simpa [prefixWord, tailWord_5294140, baseEnd_5294140] using wordTrace_append hprefix tailTrace_5294140
  have hstable : (prefixWord ++ tailWord_5294140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294140).length < 2 ^ (prefixWord ++ tailWord_5294140).sum := by decide
  have hdescent : baseEnd_5294140 < baseStart_5294140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294157 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 8]
def baseStart_5294157 : Nat := 118140960795 + 5294157 * 2 ^ 59
def prefixEnd_5294157 : Nat := 4983230072969 + 3 ^ 40 * 5294157 * 2
def baseEnd_5294157 : Nat := 302049689040572035565569

theorem tailTrace_5294157 : CollatzResearch.WordTrace tailWord_5294157 prefixEnd_5294157 302049689040572035565569 := by
  unfold tailWord_5294157
  simp only [CollatzResearch.WordTrace]
  refine ⟨193093769081180833876056725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128729179387453889250704483 193093769081180833876056725)
  ·
    refine ⟨9051270425680351587940159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 193093769081180833876056725 9051270425680351587940159)
    ·
      refine ⟨13576905638520527381910239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9051270425680351587940159 13576905638520527381910239)
      ·
        refine ⟨20365358457780791072865359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13576905638520527381910239 20365358457780791072865359)
        ·
          refine ⟨30548037686671186609298039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20365358457780791072865359 30548037686671186609298039)
          ·
            refine ⟨45822056530006779913947059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30548037686671186609298039 45822056530006779913947059)
            ·
              refine ⟨68733084795010169870920589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45822056530006779913947059 68733084795010169870920589)
              ·
                refine ⟨25774906798128813701595221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68733084795010169870920589 25774906798128813701595221)
                ·
                  refine ⟨302049689040572035565569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25774906798128813701595221 302049689040572035565569)
                  ·
                    rfl

theorem cell23_5294157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_5294157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294157 prefixEnd_5294157 := by exact prefixLift 5294157
  have htrace : WordTrace (prefixWord ++ tailWord_5294157) baseStart_5294157 baseEnd_5294157 := by
    simpa [prefixWord, tailWord_5294157, baseEnd_5294157] using wordTrace_append hprefix tailTrace_5294157
  have hstable : (prefixWord ++ tailWord_5294157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294157).length < 2 ^ (prefixWord ++ tailWord_5294157).sum := by decide
  have hdescent : baseEnd_5294157 < baseStart_5294157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294218 : List Nat := [3, 1, 2, 3, 1, 3, 1, 4, 1, 1, 3]
def baseStart_5294218 : Nat := 118140960795 + 5294218 * 2 ^ 59
def prefixEnd_5294218 : Nat := 4983230072969 + 3 ^ 40 * 5294218 * 2
def baseEnd_5294218 : Nat := 2718478523685072581427341

theorem tailTrace_5294218 : CollatzResearch.WordTrace tailWord_5294218 prefixEnd_5294218 2718478523685072581427341 := by
  unfold tailWord_5294218
  simp only [CollatzResearch.WordTrace]
  refine ⟨48273998483489960323506827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128730662622639894196018205 48273998483489960323506827)
  ·
    refine ⟨72410997725234940485260241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48273998483489960323506827 72410997725234940485260241)
    ·
      refine ⟨54308248293926205363945181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72410997725234940485260241 54308248293926205363945181)
      ·
        refine ⟨20365593110222327011479443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54308248293926205363945181 20365593110222327011479443)
        ·
          refine ⟨30548389665333490517219165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20365593110222327011479443 30548389665333490517219165)
          ·
            refine ⟨11455646124500058943957187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30548389665333490517219165 11455646124500058943957187)
            ·
              refine ⟨17183469186750088415935781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11455646124500058943957187 17183469186750088415935781)
              ·
                refine ⟨3221900472515641577987959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17183469186750088415935781 3221900472515641577987959)
                ·
                  refine ⟨4832850708773462366981939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221900472515641577987959 4832850708773462366981939)
                  ·
                    refine ⟨7249276063160193550472909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4832850708773462366981939 7249276063160193550472909)
                    ·
                      refine ⟨2718478523685072581427341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7249276063160193550472909 2718478523685072581427341)
                      ·
                        rfl

theorem cell23_5294218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_5294218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294218 prefixEnd_5294218 := by exact prefixLift 5294218
  have htrace : WordTrace (prefixWord ++ tailWord_5294218) baseStart_5294218 baseEnd_5294218 := by
    simpa [prefixWord, tailWord_5294218, baseEnd_5294218] using wordTrace_append hprefix tailTrace_5294218
  have hstable : (prefixWord ++ tailWord_5294218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294218).length < 2 ^ (prefixWord ++ tailWord_5294218).sum := by decide
  have hdescent : baseEnd_5294218 < baseStart_5294218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294241 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 5, 2, 2]
def baseStart_5294241 : Nat := 118140960795 + 5294241 * 2 ^ 59
def prefixEnd_5294241 : Nat := 4983230072969 + 3 ^ 40 * 5294241 * 2
def baseEnd_5294241 : Nat := 2718490333740125991439735

theorem tailTrace_5294241 : CollatzResearch.WordTrace tailWord_5294241 prefixEnd_5294241 2718490333740125991439735 := by
  unfold tailWord_5294241
  simp only [CollatzResearch.WordTrace]
  refine ⟨193096832812876516222114577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128731221875251010814743051 193096832812876516222114577)
  ·
    refine ⟨144822624609657387166585933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193096832812876516222114577 144822624609657387166585933)
    ·
      refine ⟨54308484228621520187469725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144822624609657387166585933 54308484228621520187469725)
      ·
        refine ⟨20365681585733070070301147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54308484228621520187469725 20365681585733070070301147)
        ·
          refine ⟨30548522378599605105451721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20365681585733070070301147 30548522378599605105451721)
          ·
            refine ⟨22911391783949703829088791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30548522378599605105451721 22911391783949703829088791)
            ·
              refine ⟨34367087675924555743633187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22911391783949703829088791 34367087675924555743633187)
              ·
                refine ⟨51550631513886833615449781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34367087675924555743633187 51550631513886833615449781)
                ·
                  refine ⟨4832871704426890651448417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51550631513886833615449781 4832871704426890651448417)
                  ·
                    refine ⟨3624653778320167988586313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4832871704426890651448417 3624653778320167988586313)
                    ·
                      refine ⟨2718490333740125991439735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624653778320167988586313 2718490333740125991439735)
                      ·
                        rfl

theorem cell23_5294241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_5294241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294241 prefixEnd_5294241 := by exact prefixLift 5294241
  have htrace : WordTrace (prefixWord ++ tailWord_5294241) baseStart_5294241 baseEnd_5294241 := by
    simpa [prefixWord, tailWord_5294241, baseEnd_5294241] using wordTrace_append hprefix tailTrace_5294241
  have hstable : (prefixWord ++ tailWord_5294241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294241).length < 2 ^ (prefixWord ++ tailWord_5294241).sum := by decide
  have hdescent : baseEnd_5294241 < baseStart_5294241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294268 : List Nat := [2, 2, 2, 3, 3, 2, 1, 2, 2, 4]
def baseStart_5294268 : Nat := 118140960795 + 5294268 * 2 ^ 59
def prefixEnd_5294268 : Nat := 4983230072969 + 3 ^ 40 * 5294268 * 2
def baseEnd_5294268 : Nat := 906168065905932461934037

theorem tailTrace_5294268 : CollatzResearch.WordTrace tailWord_5294268 prefixEnd_5294268 906168065905932461934037 := by
  unfold tailWord_5294268
  simp only [CollatzResearch.WordTrace]
  refine ⟨96548908791889349916673729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128731878389185799888898305 96548908791889349916673729)
  ·
    refine ⟨72411681593917012437505297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96548908791889349916673729 72411681593917012437505297)
    ·
      refine ⟨54308761195437759328128973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72411681593917012437505297 54308761195437759328128973)
      ·
        refine ⟨20365785448289159748048365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54308761195437759328128973 20365785448289159748048365)
        ·
          refine ⟨7637169543108434905518137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20365785448289159748048365 7637169543108434905518137)
          ·
            refine ⟨5727877157331326179138603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7637169543108434905518137 5727877157331326179138603)
            ·
              refine ⟨8591815735996989268707905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5727877157331326179138603 8591815735996989268707905)
              ·
                refine ⟨6443861801997741951530929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8591815735996989268707905 6443861801997741951530929)
                ·
                  refine ⟨4832896351498306463648197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6443861801997741951530929 4832896351498306463648197)
                  ·
                    refine ⟨906168065905932461934037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4832896351498306463648197 906168065905932461934037)
                    ·
                      rfl

theorem cell23_5294268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_5294268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294268 prefixEnd_5294268 := by exact prefixLift 5294268
  have htrace : WordTrace (prefixWord ++ tailWord_5294268) baseStart_5294268 baseEnd_5294268 := by
    simpa [prefixWord, tailWord_5294268, baseEnd_5294268] using wordTrace_append hprefix tailTrace_5294268
  have hstable : (prefixWord ++ tailWord_5294268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294268).length < 2 ^ (prefixWord ++ tailWord_5294268).sum := by decide
  have hdescent : baseEnd_5294268 < baseStart_5294268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294297 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 2, 3, 4]
def baseStart_5294297 : Nat := 118140960795 + 5294297 * 2 ^ 59
def prefixEnd_5294297 : Nat := 4983230072969 + 3 ^ 40 * 5294297 * 2
def baseEnd_5294297 : Nat := 2718519088656777772339477

theorem tailTrace_5294297 : CollatzResearch.WordTrace tailWord_5294297 prefixEnd_5294297 2718519088656777772339477 := by
  unfold tailWord_5294297
  simp only [CollatzResearch.WordTrace]
  refine ⟨193098875300673637786153145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128732583533782425190768763 193098875300673637786153145)
  ·
    refine ⟨144824156475505228339614859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193098875300673637786153145 144824156475505228339614859)
    ·
      refine ⟨217236234713257842509422289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144824156475505228339614859 217236234713257842509422289)
      ·
        refine ⟨162927176034943381882066717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217236234713257842509422289 162927176034943381882066717)
        ·
          refine ⟨61097691013103768205775019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162927176034943381882066717 61097691013103768205775019)
          ·
            refine ⟨91646536519655652308662529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61097691013103768205775019 91646536519655652308662529)
            ·
              refine ⟨68734902389741739231496897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91646536519655652308662529 68734902389741739231496897)
              ·
                refine ⟨51551176792306304423622673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68734902389741739231496897 51551176792306304423622673)
                ·
                  refine ⟨38663382594229728317717005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51551176792306304423622673 38663382594229728317717005)
                  ·
                    refine ⟨14498768472836148119143877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38663382594229728317717005 14498768472836148119143877)
                    ·
                      refine ⟨2718519088656777772339477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14498768472836148119143877 2718519088656777772339477)
                      ·
                        rfl

theorem cell23_5294297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_5294297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294297 prefixEnd_5294297 := by exact prefixLift 5294297
  have htrace : WordTrace (prefixWord ++ tailWord_5294297) baseStart_5294297 baseEnd_5294297 := by
    simpa [prefixWord, tailWord_5294297, baseEnd_5294297] using wordTrace_append hprefix tailTrace_5294297
  have hstable : (prefixWord ++ tailWord_5294297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294297).length < 2 ^ (prefixWord ++ tailWord_5294297).sum := by decide
  have hdescent : baseEnd_5294297 < baseStart_5294297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294334 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_5294334 : Nat := 118140960795 + 5294334 * 2 ^ 59
def prefixEnd_5294334 : Nat := 4983230072969 + 3 ^ 40 * 5294334 * 2
def baseEnd_5294334 : Nat := 2718538087440994127576807

theorem tailTrace_5294334 : CollatzResearch.WordTrace tailWord_5294334 prefixEnd_5294334 2718538087440994127576807 := by
  unfold tailWord_5294334
  simp only [CollatzResearch.WordTrace]
  refine ⟨24137528100192449138156257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128733483201026395403500037 24137528100192449138156257)
  ·
    refine ⟨18103146075144336853617193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24137528100192449138156257 18103146075144336853617193)
    ·
      refine ⟨13577359556358252640212895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18103146075144336853617193 13577359556358252640212895)
      ·
        refine ⟨20366039334537378960319343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13577359556358252640212895 20366039334537378960319343)
        ·
          refine ⟨30549059001806068440479015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20366039334537378960319343 30549059001806068440479015)
          ·
            refine ⟨45823588502709102660718523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30549059001806068440479015 45823588502709102660718523)
            ·
              refine ⟨68735382754063653991077785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45823588502709102660718523 68735382754063653991077785)
              ·
                refine ⟨51551537065547740493308339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68735382754063653991077785 51551537065547740493308339)
                ·
                  refine ⟨77327305598321610739962509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51551537065547740493308339 77327305598321610739962509)
                  ·
                    refine ⟨28997739599370604027485941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77327305598321610739962509 28997739599370604027485941)
                    ·
                      refine ⟨2718538087440994127576807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28997739599370604027485941 2718538087440994127576807)
                      ·
                        rfl

theorem cell23_5294334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_5294334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294334 prefixEnd_5294334 := by exact prefixLift 5294334
  have htrace : WordTrace (prefixWord ++ tailWord_5294334) baseStart_5294334 baseEnd_5294334 := by
    simpa [prefixWord, tailWord_5294334, baseEnd_5294334] using wordTrace_append hprefix tailTrace_5294334
  have hstable : (prefixWord ++ tailWord_5294334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294334).length < 2 ^ (prefixWord ++ tailWord_5294334).sum := by decide
  have hdescent : baseEnd_5294334 < baseStart_5294334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294348 : List Nat := [2, 2, 1, 2, 2, 2, 3, 3, 2, 2, 2]
def baseStart_5294348 : Nat := 118140960795 + 5294348 * 2 ^ 59
def prefixEnd_5294348 : Nat := 4983230072969 + 3 ^ 40 * 5294348 * 2
def baseEnd_5294348 : Nat := 2718545276170157072801743

theorem tailTrace_5294348 : CollatzResearch.WordTrace tailWord_5294348 prefixEnd_5294348 2718545276170157072801743 := by
  unfold tailWord_5294348
  simp only [CollatzResearch.WordTrace]
  refine ⟨96550367711744436748129849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128733823615659248997506465 96550367711744436748129849)
  ·
    refine ⟨72412775783808327561097387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96550367711744436748129849 72412775783808327561097387)
    ·
      refine ⟨108619163675712491341646081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72412775783808327561097387 108619163675712491341646081)
      ·
        refine ⟨81464372756784368506234561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108619163675712491341646081 81464372756784368506234561)
        ·
          refine ⟨61098279567588276379675921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81464372756784368506234561 61098279567588276379675921)
          ·
            refine ⟨45823709675691207284756941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61098279567588276379675921 45823709675691207284756941)
            ·
              refine ⟨17183891128384202731783853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45823709675691207284756941 17183891128384202731783853)
              ·
                refine ⟨6443959173144076024418945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17183891128384202731783853 6443959173144076024418945)
                ·
                  refine ⟨4832969379858057018314209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6443959173144076024418945 4832969379858057018314209)
                  ·
                    refine ⟨3624727034893542763735657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4832969379858057018314209 3624727034893542763735657)
                    ·
                      refine ⟨2718545276170157072801743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624727034893542763735657 2718545276170157072801743)
                      ·
                        rfl

theorem cell23_5294348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_5294348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294348 prefixEnd_5294348 := by exact prefixLift 5294348
  have htrace : WordTrace (prefixWord ++ tailWord_5294348) baseStart_5294348 baseEnd_5294348 := by
    simpa [prefixWord, tailWord_5294348, baseEnd_5294348] using wordTrace_append hprefix tailTrace_5294348
  have hstable : (prefixWord ++ tailWord_5294348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294348).length < 2 ^ (prefixWord ++ tailWord_5294348).sum := by decide
  have hdescent : baseEnd_5294348 < baseStart_5294348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294364 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_5294364 : Nat := 118140960795 + 5294364 * 2 ^ 59
def prefixEnd_5294364 : Nat := 4983230072969 + 3 ^ 40 * 5294364 * 2
def baseEnd_5294364 : Nat := 2718553491860629010201669

theorem tailTrace_5294364 : CollatzResearch.WordTrace tailWord_5294364 prefixEnd_5294364 2718553491860629010201669 := by
  unfold tailWord_5294364
  simp only [CollatzResearch.WordTrace]
  refine ⟨96550659495715454114421073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128734212660953938819228097 96550659495715454114421073)
  ·
    refine ⟨72412994621786590585815805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96550659495715454114421073 72412994621786590585815805)
    ·
      refine ⟨27154872983169971469680927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72412994621786590585815805 27154872983169971469680927)
      ·
        refine ⟨40732309474754957204521391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27154872983169971469680927 40732309474754957204521391)
        ·
          refine ⟨61098464212132435806782087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40732309474754957204521391 61098464212132435806782087)
          ·
            refine ⟨91647696318198653710173131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61098464212132435806782087 91647696318198653710173131)
            ·
              refine ⟨137471544477297980565259697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91647696318198653710173131 137471544477297980565259697)
              ·
                refine ⟨103103658357973485423944773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137471544477297980565259697 103103658357973485423944773)
                ·
                  refine ⟨19331935942120028516989645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103103658357973485423944773 19331935942120028516989645)
                  ·
                    refine ⟨7249475978295010693871117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19331935942120028516989645 7249475978295010693871117)
                    ·
                      refine ⟨2718553491860629010201669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7249475978295010693871117 2718553491860629010201669)
                      ·
                        rfl

theorem cell23_5294364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_5294364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294364 prefixEnd_5294364 := by exact prefixLift 5294364
  have htrace : WordTrace (prefixWord ++ tailWord_5294364) baseStart_5294364 baseEnd_5294364 := by
    simpa [prefixWord, tailWord_5294364, baseEnd_5294364] using wordTrace_append hprefix tailTrace_5294364
  have hstable : (prefixWord ++ tailWord_5294364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294364).length < 2 ^ (prefixWord ++ tailWord_5294364).sum := by decide
  have hdescent : baseEnd_5294364 < baseStart_5294364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294388 : List Nat := [2, 5, 1, 1, 1, 3, 1, 4, 5]
def baseStart_5294388 : Nat := 118140960795 + 5294388 * 2 ^ 59
def prefixEnd_5294388 : Nat := 4983230072969 + 3 ^ 40 * 5294388 * 2
def baseEnd_5294388 : Nat := 302062868377370768477951

theorem tailTrace_5294388 : CollatzResearch.WordTrace tailWord_5294388 prefixEnd_5294388 302062868377370768477951 := by
  unfold tailWord_5294388
  simp only [CollatzResearch.WordTrace]
  refine ⟨96551097171671980163857909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128734796228895973551810545 96551097171671980163857909)
  ·
    refine ⟨9051665359844248140361679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96551097171671980163857909 9051665359844248140361679)
    ·
      refine ⟨13577498039766372210542519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9051665359844248140361679 13577498039766372210542519)
      ·
        refine ⟨20366247059649558315813779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13577498039766372210542519 20366247059649558315813779)
        ·
          refine ⟨30549370589474337473720669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20366247059649558315813779 30549370589474337473720669)
          ·
            refine ⟨11456013971052876552645251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30549370589474337473720669 11456013971052876552645251)
            ·
              refine ⟨17184020956579314828967877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11456013971052876552645251 17184020956579314828967877)
              ·
                refine ⟨3222003929358621530431477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17184020956579314828967877 3222003929358621530431477)
                ·
                  refine ⟨302062868377370768477951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3222003929358621530431477 302062868377370768477951)
                  ·
                    rfl

theorem cell23_5294388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_5294388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294388 prefixEnd_5294388 := by exact prefixLift 5294388
  have htrace : WordTrace (prefixWord ++ tailWord_5294388) baseStart_5294388 baseEnd_5294388 := by
    simpa [prefixWord, tailWord_5294388, baseEnd_5294388] using wordTrace_append hprefix tailTrace_5294388
  have hstable : (prefixWord ++ tailWord_5294388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294388).length < 2 ^ (prefixWord ++ tailWord_5294388).sum := by decide
  have hdescent : baseEnd_5294388 < baseStart_5294388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294394 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_5294394 : Nat := 118140960795 + 5294394 * 2 ^ 59
def prefixEnd_5294394 : Nat := 4983230072969 + 3 ^ 40 * 5294394 * 2
def baseEnd_5294394 : Nat := 2718568896280263892826531

theorem tailTrace_5294394 : CollatzResearch.WordTrace tailWord_5294394 prefixEnd_5294394 2718568896280263892826531 := by
  unfold tailWord_5294394
  simp only [CollatzResearch.WordTrace]
  refine ⟨48275603295330555838108559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128734942120881482234956157 48275603295330555838108559)
  ·
    refine ⟨72413404942995833757162839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48275603295330555838108559 72413404942995833757162839)
    ·
      refine ⟨108620107414493750635744259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72413404942995833757162839 108620107414493750635744259)
      ·
        refine ⟨162930161121740625953616389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108620107414493750635744259 162930161121740625953616389)
        ·
          refine ⟨30549405210326367366303073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162930161121740625953616389 30549405210326367366303073)
          ·
            refine ⟨22912053907744775524727305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30549405210326367366303073 22912053907744775524727305)
            ·
              refine ⟨17184040430808581643545479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22912053907744775524727305 17184040430808581643545479)
              ·
                refine ⟨25776060646212872465318219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17184040430808581643545479 25776060646212872465318219)
                ·
                  refine ⟨38664090969319308697977329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25776060646212872465318219 38664090969319308697977329)
                  ·
                    refine ⟨28998068226989481523482997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38664090969319308697977329 28998068226989481523482997)
                    ·
                      refine ⟨2718568896280263892826531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28998068226989481523482997 2718568896280263892826531)
                      ·
                        rfl

theorem cell23_5294394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_5294394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294394 prefixEnd_5294394 := by exact prefixLift 5294394
  have htrace : WordTrace (prefixWord ++ tailWord_5294394) baseStart_5294394 baseEnd_5294394 := by
    simpa [prefixWord, tailWord_5294394, baseEnd_5294394] using wordTrace_append hprefix tailTrace_5294394
  have hstable : (prefixWord ++ tailWord_5294394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294394).length < 2 ^ (prefixWord ++ tailWord_5294394).sum := by decide
  have hdescent : baseEnd_5294394 < baseStart_5294394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294421 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_5294421 : Nat := 118140960795 + 5294421 * 2 ^ 59
def prefixEnd_5294421 : Nat := 4983230072969 + 3 ^ 40 * 5294421 * 2
def baseEnd_5294421 : Nat := 2718582760257935287188907

theorem tailTrace_5294421 : CollatzResearch.WordTrace tailWord_5294421 prefixEnd_5294421 2718582760257935287188907 := by
  unfold tailWord_5294421
  simp only [CollatzResearch.WordTrace]
  refine ⟨193103397952224406963667117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128735598634816271309111411 193103397952224406963667117)
  ·
    refine ⟨72413774232084152611375169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193103397952224406963667117 72413774232084152611375169)
    ·
      refine ⟨54310330674063114458531377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72413774232084152611375169 54310330674063114458531377)
      ·
        refine ⟨40732748005547335843898533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54310330674063114458531377 40732748005547335843898533)
        ·
          refine ⟨7637390251040125470730975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40732748005547335843898533 7637390251040125470730975)
          ·
            refine ⟨11456085376560188206096463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7637390251040125470730975 11456085376560188206096463)
            ·
              refine ⟨17184128064840282309144695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11456085376560188206096463 17184128064840282309144695)
              ·
                refine ⟨25776192097260423463717043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17184128064840282309144695 25776192097260423463717043)
                ·
                  refine ⟨38664288145890635195575565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25776192097260423463717043 38664288145890635195575565)
                  ·
                    refine ⟨14499108054708988198340837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38664288145890635195575565 14499108054708988198340837)
                    ·
                      refine ⟨2718582760257935287188907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14499108054708988198340837 2718582760257935287188907)
                      ·
                        rfl

theorem cell23_5294421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_5294421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294421 prefixEnd_5294421 := by exact prefixLift 5294421
  have htrace : WordTrace (prefixWord ++ tailWord_5294421) baseStart_5294421 baseEnd_5294421 := by
    simpa [prefixWord, tailWord_5294421, baseEnd_5294421] using wordTrace_append hprefix tailTrace_5294421
  have hstable : (prefixWord ++ tailWord_5294421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294421).length < 2 ^ (prefixWord ++ tailWord_5294421).sum := by decide
  have hdescent : baseEnd_5294421 < baseStart_5294421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294448 : List Nat := [2, 1, 1, 1, 4, 3, 2, 4, 1, 4]
def baseStart_5294448 : Nat := 118140960795 + 5294448 * 2 ^ 59
def prefixEnd_5294448 : Nat := 4983230072969 + 3 ^ 40 * 5294448 * 2
def baseEnd_5294448 : Nat := 906198874745202227183761

theorem tailTrace_5294448 : CollatzResearch.WordTrace tailWord_5294448 prefixEnd_5294448 906198874745202227183761 := by
  unfold tailWord_5294448
  simp only [CollatzResearch.WordTrace]
  refine ⟨96552191361563295287449999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128736255148751060383266665 96552191361563295287449999)
  ·
    refine ⟨144828287042344942931174999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96552191361563295287449999 144828287042344942931174999)
    ·
      refine ⟨217242430563517414396762499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144828287042344942931174999 217242430563517414396762499)
      ·
        refine ⟨325863645845276121595143749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217242430563517414396762499 325863645845276121595143749)
        ·
          refine ⟨61099433595989272799089453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 325863645845276121595143749 61099433595989272799089453)
          ·
            refine ⟨22912287598495977299658545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61099433595989272799089453 22912287598495977299658545)
            ·
              refine ⟨17184215698871982974743909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22912287598495977299658545 17184215698871982974743909)
              ·
                refine ⟨3222040443538496807764483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17184215698871982974743909 3222040443538496807764483)
                ·
                  refine ⟨4833060665307745211646725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3222040443538496807764483 4833060665307745211646725)
                  ·
                    refine ⟨906198874745202227183761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4833060665307745211646725 906198874745202227183761)
                    ·
                      rfl

theorem cell23_5294448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 1, 4].length) (baseStart_5294448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294448 prefixEnd_5294448 := by exact prefixLift 5294448
  have htrace : WordTrace (prefixWord ++ tailWord_5294448) baseStart_5294448 baseEnd_5294448 := by
    simpa [prefixWord, tailWord_5294448, baseEnd_5294448] using wordTrace_append hprefix tailTrace_5294448
  have hstable : (prefixWord ++ tailWord_5294448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294448).length < 2 ^ (prefixWord ++ tailWord_5294448).sum := by decide
  have hdescent : baseEnd_5294448 < baseStart_5294448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294528 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 5, 2, 2]
def baseStart_5294528 : Nat := 118140960795 + 5294528 * 2 ^ 59
def prefixEnd_5294528 : Nat := 4983230072969 + 3 ^ 40 * 5294528 * 2
def baseEnd_5294528 : Nat := 2718637702687966368550915

theorem tailTrace_5294528 : CollatzResearch.WordTrace tailWord_5294528 prefixEnd_5294528 2718637702687966368550915 := by
  unfold tailWord_5294528
  simp only [CollatzResearch.WordTrace]
  refine ⟨96553650281418382118906119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128738200375224509491874825 96553650281418382118906119)
  ·
    refine ⟨144830475422127573178359179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96553650281418382118906119 144830475422127573178359179)
    ·
      refine ⟨217245713133191359767538769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144830475422127573178359179 217245713133191359767538769)
      ·
        refine ⟨162934284849893519825654077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217245713133191359767538769 162934284849893519825654077)
        ·
          refine ⟨61100356818710069934620279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162934284849893519825654077 61100356818710069934620279)
          ·
            refine ⟨91650535228065104901930419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61100356818710069934620279 91650535228065104901930419)
            ·
              refine ⟨137475802842097657352895629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91650535228065104901930419 137475802842097657352895629)
              ·
                refine ⟨51553426065786621507335861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137475802842097657352895629 51553426065786621507335861)
                ·
                  refine ⟨4833133693667495766312737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51553426065786621507335861 4833133693667495766312737)
                  ·
                    refine ⟨3624850270250621824734553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4833133693667495766312737 3624850270250621824734553)
                    ·
                      refine ⟨2718637702687966368550915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624850270250621824734553 2718637702687966368550915)
                      ·
                        rfl

theorem cell23_5294528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 5, 2, 2].length) (baseStart_5294528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294528 prefixEnd_5294528 := by exact prefixLift 5294528
  have htrace : WordTrace (prefixWord ++ tailWord_5294528) baseStart_5294528 baseEnd_5294528 := by
    simpa [prefixWord, tailWord_5294528, baseEnd_5294528] using wordTrace_append hprefix tailTrace_5294528
  have hstable : (prefixWord ++ tailWord_5294528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294528).length < 2 ^ (prefixWord ++ tailWord_5294528).sum := by decide
  have hdescent : baseEnd_5294528 < baseStart_5294528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294532 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_5294532 : Nat := 118140960795 + 5294532 * 2 ^ 59
def prefixEnd_5294532 : Nat := 4983230072969 + 3 ^ 40 * 5294532 * 2
def baseEnd_5294532 : Nat := 2718639756610584352900897

theorem tailTrace_5294532 : CollatzResearch.WordTrace tailWord_5294532 prefixEnd_5294532 2718639756610584352900897 := by
  unfold tailWord_5294532
  simp only [CollatzResearch.WordTrace]
  refine ⟨96553723227411136460478925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128738297636548181947305233 96553723227411136460478925)
  ·
    refine ⟨36207646210279176172679597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96553723227411136460478925 36207646210279176172679597)
    ·
      refine ⟨13577867328854691064754849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36207646210279176172679597 13577867328854691064754849)
      ·
        refine ⟨10183400496641018298566137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13577867328854691064754849 10183400496641018298566137)
        ·
          refine ⟨7637550372480763723924603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10183400496641018298566137 7637550372480763723924603)
          ·
            refine ⟨11456325558721145585886905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7637550372480763723924603 11456325558721145585886905)
            ·
              refine ⟨8592244169040859189415179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11456325558721145585886905 8592244169040859189415179)
              ·
                refine ⟨12888366253561288784122769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8592244169040859189415179 12888366253561288784122769)
                ·
                  refine ⟨9666274690170966588092077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12888366253561288784122769 9666274690170966588092077)
                  ·
                    refine ⟨3624853008814112470534529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9666274690170966588092077 3624853008814112470534529)
                    ·
                      refine ⟨2718639756610584352900897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624853008814112470534529 2718639756610584352900897)
                      ·
                        rfl

theorem cell23_5294532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_5294532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294532 prefixEnd_5294532 := by exact prefixLift 5294532
  have htrace : WordTrace (prefixWord ++ tailWord_5294532) baseStart_5294532 baseEnd_5294532 := by
    simpa [prefixWord, tailWord_5294532, baseEnd_5294532] using wordTrace_append hprefix tailTrace_5294532
  have hstable : (prefixWord ++ tailWord_5294532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294532).length < 2 ^ (prefixWord ++ tailWord_5294532).sum := by decide
  have hdescent : baseEnd_5294532 < baseStart_5294532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294548 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_5294548 : Nat := 118140960795 + 5294548 * 2 ^ 59
def prefixEnd_5294548 : Nat := 4983230072969 + 3 ^ 40 * 5294548 * 2
def baseEnd_5294548 : Nat := 2718647972301056290300823

theorem tailTrace_5294548 : CollatzResearch.WordTrace tailWord_5294548 prefixEnd_5294548 2718647972301056290300823 := by
  unfold tailWord_5294548
  simp only [CollatzResearch.WordTrace]
  refine ⟨96554015011382153826770149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128738686681842871769026865 96554015011382153826770149)
  ·
    refine ⟨18103877814634153842519403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96554015011382153826770149 18103877814634153842519403)
    ·
      refine ⟨27155816721951230763779105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18103877814634153842519403 27155816721951230763779105)
      ·
        refine ⟨20366862541463423072834329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27155816721951230763779105 20366862541463423072834329)
        ·
          refine ⟨15275146906097567304625747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20366862541463423072834329 15275146906097567304625747)
          ·
            refine ⟨22912720359146350956938621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15275146906097567304625747 22912720359146350956938621)
            ·
              refine ⟨8592270134679881608851983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22912720359146350956938621 8592270134679881608851983)
              ·
                refine ⟨12888405202019822413277975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8592270134679881608851983 12888405202019822413277975)
                ·
                  refine ⟨19332607803029733619916963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12888405202019822413277975 19332607803029733619916963)
                  ·
                    refine ⟨28998911704544600429875445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19332607803029733619916963 28998911704544600429875445)
                    ·
                      refine ⟨2718647972301056290300823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28998911704544600429875445 2718647972301056290300823)
                      ·
                        rfl

theorem cell23_5294548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_5294548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294548 prefixEnd_5294548 := by exact prefixLift 5294548
  have htrace : WordTrace (prefixWord ++ tailWord_5294548) baseStart_5294548 baseEnd_5294548 := by
    simpa [prefixWord, tailWord_5294548, baseEnd_5294548] using wordTrace_append hprefix tailTrace_5294548
  have hstable : (prefixWord ++ tailWord_5294548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294548).length < 2 ^ (prefixWord ++ tailWord_5294548).sum := by decide
  have hdescent : baseEnd_5294548 < baseStart_5294548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294561 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_5294561 : Nat := 118140960795 + 5294561 * 2 ^ 59
def prefixEnd_5294561 : Nat := 4983230072969 + 3 ^ 40 * 5294561 * 2
def baseEnd_5294561 : Nat := 2718654647549564739438263

theorem tailTrace_5294561 : CollatzResearch.WordTrace tailWord_5294561 prefixEnd_5294561 2718654647549564739438263 := by
  unfold tailWord_5294561
  simp only [CollatzResearch.WordTrace]
  refine ⟨193108504171717210873763537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128739002781144807249175691 193108504171717210873763537)
  ·
    refine ⟨144831378128787908155322653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193108504171717210873763537 144831378128787908155322653)
    ·
      refine ⟨54311766798295465558245995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144831378128787908155322653 54311766798295465558245995)
      ·
        refine ⟨81467650197443198337368993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54311766798295465558245995 81467650197443198337368993)
        ·
          refine ⟨61100737648082398753026745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81467650197443198337368993 61100737648082398753026745)
          ·
            refine ⟨45825553236061799064770059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61100737648082398753026745 45825553236061799064770059)
            ·
              refine ⟨68738329854092698597155089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45825553236061799064770059 68738329854092698597155089)
              ·
                refine ⟨51553747390569523947866317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68738329854092698597155089 51553747390569523947866317)
                ·
                  refine ⟨19332655271463571480449869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51553747390569523947866317 19332655271463571480449869)
                  ·
                    refine ⟨7249745726798839305168701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19332655271463571480449869 7249745726798839305168701)
                    ·
                      refine ⟨2718654647549564739438263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7249745726798839305168701 2718654647549564739438263)
                      ·
                        rfl

theorem cell23_5294561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_5294561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294561 prefixEnd_5294561 := by exact prefixLift 5294561
  have htrace : WordTrace (prefixWord ++ tailWord_5294561) baseStart_5294561 baseEnd_5294561 := by
    simpa [prefixWord, tailWord_5294561, baseEnd_5294561] using wordTrace_append hprefix tailTrace_5294561
  have hstable : (prefixWord ++ tailWord_5294561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294561).length < 2 ^ (prefixWord ++ tailWord_5294561).sum := by decide
  have hdescent : baseEnd_5294561 < baseStart_5294561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294599 : List Nat := [1, 1, 4, 3, 4, 1, 2, 1, 1, 2, 3]
def baseStart_5294599 : Nat := 118140960795 + 5294599 * 2 ^ 59
def prefixEnd_5294599 : Nat := 4983230072969 + 3 ^ 40 * 5294599 * 2
def baseEnd_5294599 : Nat := 2718674159814435590763089

theorem tailTrace_5294599 : CollatzResearch.WordTrace tailWord_5294599 prefixEnd_5294599 2718674159814435590763089 := by
  unfold tailWord_5294599
  simp only [CollatzResearch.WordTrace]
  refine ⟨193109890145579543363646851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128739926763719695575764567 193109890145579543363646851)
  ·
    refine ⟨289664835218369315045470277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193109890145579543363646851 289664835218369315045470277)
    ·
      refine ⟨54312156603444246571025677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289664835218369315045470277 54312156603444246571025677)
      ·
        refine ⟨20367058726291592464134629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54312156603444246571025677 20367058726291592464134629)
        ·
          refine ⟨3818823511179673587025243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20367058726291592464134629 3818823511179673587025243)
          ·
            refine ⟨5728235266769510380537865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818823511179673587025243 5728235266769510380537865)
            ·
              refine ⟨4296176450077132785403399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5728235266769510380537865 4296176450077132785403399)
              ·
                refine ⟨6444264675115699178105099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4296176450077132785403399 6444264675115699178105099)
                ·
                  refine ⟨9666397012673548767157649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6444264675115699178105099 9666397012673548767157649)
                  ·
                    refine ⟨7249797759505161575368237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9666397012673548767157649 7249797759505161575368237)
                    ·
                      refine ⟨2718674159814435590763089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7249797759505161575368237 2718674159814435590763089)
                      ·
                        rfl

theorem cell23_5294599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_5294599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294599 prefixEnd_5294599 := by exact prefixLift 5294599
  have htrace : WordTrace (prefixWord ++ tailWord_5294599) baseStart_5294599 baseEnd_5294599 := by
    simpa [prefixWord, tailWord_5294599, baseEnd_5294599] using wordTrace_append hprefix tailTrace_5294599
  have hstable : (prefixWord ++ tailWord_5294599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294599).length < 2 ^ (prefixWord ++ tailWord_5294599).sum := by decide
  have hdescent : baseEnd_5294599 < baseStart_5294599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294612 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_5294612 : Nat := 118140960795 + 5294612 * 2 ^ 59
def prefixEnd_5294612 : Nat := 4983230072969 + 3 ^ 40 * 5294612 * 2
def baseEnd_5294612 : Nat := 2718680835062944039900529

theorem tailTrace_5294612 : CollatzResearch.WordTrace tailWord_5294612 prefixEnd_5294612 2718680835062944039900529 := by
  unfold tailWord_5294612
  simp only [CollatzResearch.WordTrace]
  refine ⟨96555182147266223291935045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128740242863021631055913393 96555182147266223291935045)
  ·
    refine ⟨18104096652612416867237821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96555182147266223291935045 18104096652612416867237821)
    ·
      refine ⟨6789036244729656325214183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18104096652612416867237821 6789036244729656325214183)
      ·
        refine ⟨10183554367094484487821275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6789036244729656325214183 10183554367094484487821275)
        ·
          refine ⟨15275331550641726731731913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10183554367094484487821275 15275331550641726731731913)
          ·
            refine ⟨11456498662981295048798935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15275331550641726731731913 11456498662981295048798935)
            ·
              refine ⟨17184747994471942573198403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11456498662981295048798935 17184747994471942573198403)
              ·
                refine ⟨25777121991707913859797605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17184747994471942573198403 25777121991707913859797605)
                ·
                  refine ⟨4833210373445233848712051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25777121991707913859797605 4833210373445233848712051)
                  ·
                    refine ⟨7249815560167850773068077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4833210373445233848712051 7249815560167850773068077)
                    ·
                      refine ⟨2718680835062944039900529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7249815560167850773068077 2718680835062944039900529)
                      ·
                        rfl

theorem cell23_5294612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_5294612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294612 prefixEnd_5294612 := by exact prefixLift 5294612
  have htrace : WordTrace (prefixWord ++ tailWord_5294612) baseStart_5294612 baseEnd_5294612 := by
    simpa [prefixWord, tailWord_5294612, baseEnd_5294612] using wordTrace_append hprefix tailTrace_5294612
  have hstable : (prefixWord ++ tailWord_5294612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294612).length < 2 ^ (prefixWord ++ tailWord_5294612).sum := by decide
  have hdescent : baseEnd_5294612 < baseStart_5294612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294618 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2]
def baseStart_5294618 : Nat := 118140960795 + 5294618 * 2 ^ 59
def prefixEnd_5294618 : Nat := 4983230072969 + 3 ^ 40 * 5294618 * 2
def baseEnd_5294618 : Nat := 2718683915946871016425501

theorem tailTrace_5294618 : CollatzResearch.WordTrace tailWord_5294618 prefixEnd_5294618 2718683915946871016425501 := by
  unfold tailWord_5294618
  simp only [CollatzResearch.WordTrace]
  refine ⟨48277645783127677402147127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128740388755007139739059005 48277645783127677402147127)
  ·
    refine ⟨72416468674691516103220691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48277645783127677402147127 72416468674691516103220691)
    ·
      refine ⟨108624703012037274154831037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72416468674691516103220691 108624703012037274154831037)
      ·
        refine ⟨40734263629513977808061639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108624703012037274154831037 40734263629513977808061639)
        ·
          refine ⟨61101395444270966712092459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40734263629513977808061639 61101395444270966712092459)
          ·
            refine ⟨91652093166406450068138689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61101395444270966712092459 91652093166406450068138689)
            ·
              refine ⟨68739069874804837551104017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91652093166406450068138689 68739069874804837551104017)
              ·
                refine ⟨51554302406103628163328013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68739069874804837551104017 51554302406103628163328013)
                ·
                  refine ⟨19332863402288860561248005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51554302406103628163328013 19332863402288860561248005)
                  ·
                    refine ⟨3624911887929161355234001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19332863402288860561248005 3624911887929161355234001)
                    ·
                      refine ⟨2718683915946871016425501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624911887929161355234001 2718683915946871016425501)
                      ·
                        rfl

theorem cell23_5294618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_5294618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294618 prefixEnd_5294618 := by exact prefixLift 5294618
  have htrace : WordTrace (prefixWord ++ tailWord_5294618) baseStart_5294618 baseEnd_5294618 := by
    simpa [prefixWord, tailWord_5294618, baseEnd_5294618] using wordTrace_append hprefix tailTrace_5294618
  have hstable : (prefixWord ++ tailWord_5294618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294618).length < 2 ^ (prefixWord ++ tailWord_5294618).sum := by decide
  have hdescent : baseEnd_5294618 < baseStart_5294618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294635 : List Nat := [1, 1, 1, 1, 2, 1, 3, 7, 2, 2, 2]
def baseStart_5294635 : Nat := 118140960795 + 5294635 * 2 ^ 59
def prefixEnd_5294635 : Nat := 4983230072969 + 3 ^ 40 * 5294635 * 2
def baseEnd_5294635 : Nat := 2718692645117997449912923

theorem tailTrace_5294635 : CollatzResearch.WordTrace tailWord_5294635 prefixEnd_5294635 2718692645117997449912923 := by
  unfold tailWord_5294635
  simp only [CollatzResearch.WordTrace]
  refine ⟨193111203173449121511957359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128740802115632747674638239 193111203173449121511957359)
  ·
    refine ⟨289666804760173682267936039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193111203173449121511957359 289666804760173682267936039)
    ·
      refine ⟨434500207140260523401904059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289666804760173682267936039 434500207140260523401904059)
      ·
        refine ⟨651750310710390785102856089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434500207140260523401904059 651750310710390785102856089)
        ·
          refine ⟨488812733032793088827142067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 651750310710390785102856089 488812733032793088827142067)
          ·
            refine ⟨733219099549189633240713101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488812733032793088827142067 733219099549189633240713101)
            ·
              refine ⟨274957162330946112465267413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 733219099549189633240713101 274957162330946112465267413)
              ·
                refine ⟨6444308492131549510904705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 274957162330946112465267413 6444308492131549510904705)
                ·
                  refine ⟨4833231369098662133178529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6444308492131549510904705 4833231369098662133178529)
                  ·
                    refine ⟨3624923526823996599883897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4833231369098662133178529 3624923526823996599883897)
                    ·
                      refine ⟨2718692645117997449912923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3624923526823996599883897 2718692645117997449912923)
                      ·
                        rfl

theorem cell23_5294635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 2, 2].length) (baseStart_5294635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294635 prefixEnd_5294635 := by exact prefixLift 5294635
  have htrace : WordTrace (prefixWord ++ tailWord_5294635) baseStart_5294635 baseEnd_5294635 := by
    simpa [prefixWord, tailWord_5294635, baseEnd_5294635] using wordTrace_append hprefix tailTrace_5294635
  have hstable : (prefixWord ++ tailWord_5294635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294635).length < 2 ^ (prefixWord ++ tailWord_5294635).sum := by decide
  have hdescent : baseEnd_5294635 < baseStart_5294635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294641 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 7]
def baseStart_5294641 : Nat := 118140960795 + 5294641 * 2 ^ 59
def prefixEnd_5294641 : Nat := 4983230072969 + 3 ^ 40 * 5294641 * 2
def baseEnd_5294641 : Nat := 302077302889102714048655

theorem tailTrace_5294641 : CollatzResearch.WordTrace tailWord_5294641 prefixEnd_5294641 302077302889102714048655 := by
  unfold tailWord_5294641
  simp only [CollatzResearch.WordTrace]
  refine ⟨193111422011427384536675777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128740948007618256357783851 193111422011427384536675777)
  ·
    refine ⟨144833566508570538402506833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193111422011427384536675777 144833566508570538402506833)
    ·
      refine ⟨108625174881427903801880125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144833566508570538402506833 108625174881427903801880125)
      ·
        refine ⟨40734440580535463925705047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108625174881427903801880125 40734440580535463925705047)
        ·
          refine ⟨61101660870803195888557571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40734440580535463925705047 61101660870803195888557571)
          ·
            refine ⟨91652491306204793832836357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61101660870803195888557571 91652491306204793832836357)
            ·
              refine ⟨17184842119913398843656817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91652491306204793832836357 17184842119913398843656817)
              ·
                refine ⟨12888631589935049132742613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17184842119913398843656817 12888631589935049132742613)
                ·
                  refine ⟨302077302889102714048655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12888631589935049132742613 302077302889102714048655)
                  ·
                    rfl

theorem cell23_5294641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 7].length) (baseStart_5294641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294641 prefixEnd_5294641 := by exact prefixLift 5294641
  have htrace : WordTrace (prefixWord ++ tailWord_5294641) baseStart_5294641 baseEnd_5294641 := by
    simpa [prefixWord, tailWord_5294641, baseEnd_5294641] using wordTrace_append hprefix tailTrace_5294641
  have hstable : (prefixWord ++ tailWord_5294641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294641).length < 2 ^ (prefixWord ++ tailWord_5294641).sum := by decide
  have hdescent : baseEnd_5294641 < baseStart_5294641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294671 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 4, 5]
def baseStart_5294671 : Nat := 118140960795 + 5294671 * 2 ^ 59
def prefixEnd_5294671 : Nat := 4983230072969 + 3 ^ 40 * 5294671 * 2
def baseEnd_5294671 : Nat := 906237043473853103020919

theorem tailTrace_5294671 : CollatzResearch.WordTrace tailWord_5294671 prefixEnd_5294671 906237043473853103020919 := by
  unfold tailWord_5294671
  simp only [CollatzResearch.WordTrace]
  refine ⟨193112516201318699660267867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128741677467545799773511911 193112516201318699660267867)
  ·
    refine ⟨289668774301978049490401801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193112516201318699660267867 289668774301978049490401801)
    ·
      refine ⟨217251580726483537117801351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289668774301978049490401801 217251580726483537117801351)
      ·
        refine ⟨325877371089725305676702027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217251580726483537117801351 325877371089725305676702027)
        ·
          refine ⟨488816056634587958515053041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325877371089725305676702027 488816056634587958515053041)
          ·
            refine ⟨366612042475940968886289781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488816056634587958515053041 366612042475940968886289781)
            ·
              refine ⟨34369878982119465833089667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 366612042475940968886289781 34369878982119465833089667)
              ·
                refine ⟨51554818473179198749634501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34369878982119465833089667 51554818473179198749634501)
                ·
                  refine ⟨9666528463721099765556469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51554818473179198749634501 9666528463721099765556469)
                  ·
                    refine ⟨906237043473853103020919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9666528463721099765556469 906237043473853103020919)
                    ·
                      rfl

theorem cell23_5294671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_5294671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294671 prefixEnd_5294671 := by exact prefixLift 5294671
  have htrace : WordTrace (prefixWord ++ tailWord_5294671) baseStart_5294671 baseEnd_5294671 := by
    simpa [prefixWord, tailWord_5294671, baseEnd_5294671] using wordTrace_append hprefix tailTrace_5294671
  have hstable : (prefixWord ++ tailWord_5294671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294671).length < 2 ^ (prefixWord ++ tailWord_5294671).sum := by decide
  have hdescent : baseEnd_5294671 < baseStart_5294671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294735 : List Nat := [1, 1, 2, 1, 1, 1, 1, 10, 1, 4]
def baseStart_5294735 : Nat := 118140960795 + 5294735 * 2 ^ 59
def prefixEnd_5294735 : Nat := 4983230072969 + 3 ^ 40 * 5294735 * 2
def baseEnd_5294735 : Nat := 906247997727815686220821

theorem tailTrace_5294735 : CollatzResearch.WordTrace tailWord_5294735 prefixEnd_5294735 906247997727815686220821 := by
  unfold tailWord_5294735
  simp only [CollatzResearch.WordTrace]
  refine ⟨193114850473086838590597659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128743233648724559060398439 193114850473086838590597659)
  ·
    refine ⟨289672275709630257885896489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193114850473086838590597659 289672275709630257885896489)
    ·
      refine ⟨217254206782222693414422367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289672275709630257885896489 217254206782222693414422367)
      ·
        refine ⟨325881310173334040121633551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217254206782222693414422367 325881310173334040121633551)
        ·
          refine ⟨488821965260001060182450327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325881310173334040121633551 488821965260001060182450327)
          ·
            refine ⟨733232947890001590273675491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488821965260001060182450327 733232947890001590273675491)
            ·
              refine ⟨1099849421835002385410513237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733232947890001590273675491 1099849421835002385410513237)
              ·
                refine ⟨3222215103032233551007363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1099849421835002385410513237 3222215103032233551007363)
                ·
                  refine ⟨4833322654548350326511045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3222215103032233551007363 4833322654548350326511045)
                  ·
                    refine ⟨906247997727815686220821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4833322654548350326511045 906247997727815686220821)
                    ·
                      rfl

theorem cell23_5294735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 1, 4].length) (baseStart_5294735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294735 prefixEnd_5294735 := by exact prefixLift 5294735
  have htrace : WordTrace (prefixWord ++ tailWord_5294735) baseStart_5294735 baseEnd_5294735 := by
    simpa [prefixWord, tailWord_5294735, baseEnd_5294735] using wordTrace_append hprefix tailTrace_5294735
  have hstable : (prefixWord ++ tailWord_5294735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294735).length < 2 ^ (prefixWord ++ tailWord_5294735).sum := by decide
  have hdescent : baseEnd_5294735 < baseStart_5294735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294759 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_5294759 : Nat := 118140960795 + 5294759 * 2 ^ 59
def prefixEnd_5294759 : Nat := 4983230072969 + 3 ^ 40 * 5294759 * 2
def baseEnd_5294759 : Nat := 2718756316719154964762353

theorem tailTrace_5294759 : CollatzResearch.WordTrace tailWord_5294759 prefixEnd_5294759 2718756316719154964762353 := by
  unfold tailWord_5294759
  simp only [CollatzResearch.WordTrace]
  refine ⟨193115725824999890689471331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128743817216666593792980887 193115725824999890689471331)
  ·
    refine ⟨289673588737499836034206997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193115725824999890689471331 289673588737499836034206997)
    ·
      refine ⟨13578449472070304814103453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 289673588737499836034206997 13578449472070304814103453)
      ·
        refine ⟨5091918552026364305288795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13578449472070304814103453 5091918552026364305288795)
        ·
          refine ⟨7637877828039546457933193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5091918552026364305288795 7637877828039546457933193)
          ·
            refine ⟨5728408371029659843449895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7637877828039546457933193 5728408371029659843449895)
            ·
              refine ⟨8592612556544489765174843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5728408371029659843449895 8592612556544489765174843)
              ·
                refine ⟨12888918834816734647762265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8592612556544489765174843 12888918834816734647762265)
                ·
                  refine ⟨9666689126112550985821699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12888918834816734647762265 9666689126112550985821699)
                  ·
                    refine ⟨14500033689168826478732549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9666689126112550985821699 14500033689168826478732549)
                    ·
                      refine ⟨2718756316719154964762353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14500033689168826478732549 2718756316719154964762353)
                      ·
                        rfl

theorem cell23_5294759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_5294759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294759 prefixEnd_5294759 := by exact prefixLift 5294759
  have htrace : WordTrace (prefixWord ++ tailWord_5294759) baseStart_5294759 baseEnd_5294759 := by
    simpa [prefixWord, tailWord_5294759, baseEnd_5294759] using wordTrace_append hprefix tailTrace_5294759
  have hstable : (prefixWord ++ tailWord_5294759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294759).length < 2 ^ (prefixWord ++ tailWord_5294759).sum := by decide
  have hdescent : baseEnd_5294759 < baseStart_5294759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294792 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_5294792 : Nat := 118140960795 + 5294792 * 2 ^ 59
def prefixEnd_5294792 : Nat := 4983230072969 + 3 ^ 40 * 5294792 * 2
def baseEnd_5294792 : Nat := 2718773261580753335649701

theorem tailTrace_5294792 : CollatzResearch.WordTrace tailWord_5294792 prefixEnd_5294792 2718773261580753335649701 := by
  unfold tailWord_5294792
  simp only [CollatzResearch.WordTrace]
  refine ⟨96558464716940168662711315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128744619622586891550281753 96558464716940168662711315)
  ·
    refine ⟨144837697075410252994066973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96558464716940168662711315 144837697075410252994066973)
    ·
      refine ⟨54314136403278844872775115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144837697075410252994066973 54314136403278844872775115)
      ·
        refine ⟨81471204604918267309162673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54314136403278844872775115 81471204604918267309162673)
        ·
          refine ⟨61103403453688700481872005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81471204604918267309162673 61103403453688700481872005)
          ·
            refine ⟨11456888147566631340351001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61103403453688700481872005 11456888147566631340351001)
            ·
              refine ⟨8592666110674973505263251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11456888147566631340351001 8592666110674973505263251)
              ·
                refine ⟨12888999166012460257894877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8592666110674973505263251 12888999166012460257894877)
                ·
                  refine ⟨4833374687254672596710579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12888999166012460257894877 4833374687254672596710579)
                  ·
                    refine ⟨7250062030882008895065869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4833374687254672596710579 7250062030882008895065869)
                    ·
                      refine ⟨2718773261580753335649701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7250062030882008895065869 2718773261580753335649701)
                      ·
                        rfl

theorem cell23_5294792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_5294792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294792 prefixEnd_5294792 := by exact prefixLift 5294792
  have htrace : WordTrace (prefixWord ++ tailWord_5294792) baseStart_5294792 baseEnd_5294792 := by
    simpa [prefixWord, tailWord_5294792, baseEnd_5294792] using wordTrace_append hprefix tailTrace_5294792
  have hstable : (prefixWord ++ tailWord_5294792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294792).length < 2 ^ (prefixWord ++ tailWord_5294792).sum := by decide
  have hdescent : baseEnd_5294792 < baseStart_5294792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294812 : List Nat := [2, 2, 5, 1, 1, 1, 1, 4, 1, 5]
def baseStart_5294812 : Nat := 118140960795 + 5294812 * 2 ^ 59
def prefixEnd_5294812 : Nat := 4983230072969 + 3 ^ 40 * 5294812 * 2
def baseEnd_5294812 : Nat := 906261177064614419133203

theorem tailTrace_5294812 : CollatzResearch.WordTrace tailWord_5294812 prefixEnd_5294812 906261177064614419133203 := by
  unfold tailWord_5294812
  simp only [CollatzResearch.WordTrace]
  refine ⟨96558829446903940370575345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128745105929205253827433793 96558829446903940370575345)
  ·
    refine ⟨72419122085177955277931509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96558829446903940370575345 72419122085177955277931509)
    ·
      refine ⟨6789292695485433307306079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72419122085177955277931509 6789292695485433307306079)
      ·
        refine ⟨10183939043228149960959119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6789292695485433307306079 10183939043228149960959119)
        ·
          refine ⟨15275908564842224941438679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10183939043228149960959119 15275908564842224941438679)
          ·
            refine ⟨22913862847263337412158019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15275908564842224941438679 22913862847263337412158019)
            ·
              refine ⟨34370794270895006118237029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22913862847263337412158019 34370794270895006118237029)
              ·
                refine ⟨6444523925792813647169443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34370794270895006118237029 6444523925792813647169443)
                ·
                  refine ⟨9666785888689220470754165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6444523925792813647169443 9666785888689220470754165)
                  ·
                    refine ⟨906261177064614419133203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9666785888689220470754165 906261177064614419133203)
                    ·
                      rfl

theorem cell23_5294812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_5294812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294812 prefixEnd_5294812 := by exact prefixLift 5294812
  have htrace : WordTrace (prefixWord ++ tailWord_5294812) baseStart_5294812 baseEnd_5294812 := by
    simpa [prefixWord, tailWord_5294812, baseEnd_5294812] using wordTrace_append hprefix tailTrace_5294812
  have hstable : (prefixWord ++ tailWord_5294812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294812).length < 2 ^ (prefixWord ++ tailWord_5294812).sum := by decide
  have hdescent : baseEnd_5294812 < baseStart_5294812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294815 : List Nat := [1, 1, 2, 3, 2, 3, 1, 4, 1, 1, 4]
def baseStart_5294815 : Nat := 118140960795 + 5294815 * 2 ^ 59
def prefixEnd_5294815 : Nat := 4983230072969 + 3 ^ 40 * 5294815 * 2
def baseEnd_5294815 : Nat := 2718785071635806745662095

theorem tailTrace_5294815 : CollatzResearch.WordTrace tailWord_5294815 prefixEnd_5294815 2718785071635806745662095 := by
  unfold tailWord_5294815
  simp only [CollatzResearch.WordTrace]
  refine ⟨193117768312797012253509899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128745178875198008169006599 193117768312797012253509899)
  ·
    refine ⟨289676652469195518380264849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193117768312797012253509899 289676652469195518380264849)
    ·
      refine ⟨217257489351896638785198637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289676652469195518380264849 217257489351896638785198637)
      ·
        refine ⟨81471558506961239544449489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217257489351896638785198637 81471558506961239544449489)
        ·
          refine ⟨61103668880220929658337117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81471558506961239544449489 61103668880220929658337117)
          ·
            refine ⟨22913875830082848621876419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61103668880220929658337117 22913875830082848621876419)
            ·
              refine ⟨34370813745124272932814629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22913875830082848621876419 34370813745124272932814629)
              ·
                refine ⟨6444527577210801174902743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34370813745124272932814629 6444527577210801174902743)
                ·
                  refine ⟨9666791365816201762354115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6444527577210801174902743 9666791365816201762354115)
                  ·
                    refine ⟨14500187048724302643531173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9666791365816201762354115 14500187048724302643531173)
                    ·
                      refine ⟨2718785071635806745662095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14500187048724302643531173 2718785071635806745662095)
                      ·
                        rfl

theorem cell23_5294815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_5294815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294815 prefixEnd_5294815 := by exact prefixLift 5294815
  have htrace : WordTrace (prefixWord ++ tailWord_5294815) baseStart_5294815 baseEnd_5294815 := by
    simpa [prefixWord, tailWord_5294815, baseEnd_5294815] using wordTrace_append hprefix tailTrace_5294815
  have hstable : (prefixWord ++ tailWord_5294815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294815).length < 2 ^ (prefixWord ++ tailWord_5294815).sum := by decide
  have hdescent : baseEnd_5294815 < baseStart_5294815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294828 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_5294828 : Nat := 118140960795 + 5294828 * 2 ^ 59
def prefixEnd_5294828 : Nat := 4983230072969 + 3 ^ 40 * 5294828 * 2
def baseEnd_5294828 : Nat := 2718791746884315194799535

theorem tailTrace_5294828 : CollatzResearch.WordTrace tailWord_5294828 prefixEnd_5294828 2718791746884315194799535 := by
  unfold tailWord_5294828
  simp only [CollatzResearch.WordTrace]
  refine ⟨96559121230874957736866569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128745494974499943649155425 96559121230874957736866569)
  ·
    refine ⟨72419340923156218302649927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96559121230874957736866569 72419340923156218302649927)
    ·
      refine ⟨108629011384734327453974891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72419340923156218302649927 108629011384734327453974891)
      ·
        refine ⟨162943517077101491180962337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108629011384734327453974891 162943517077101491180962337)
        ·
          refine ⟨122207637807826118385721753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162943517077101491180962337 122207637807826118385721753)
          ·
            refine ⟨91655728355869588789291315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122207637807826118385721753 91655728355869588789291315)
            ·
              refine ⟨137483592533804383183936973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91655728355869588789291315 137483592533804383183936973)
              ·
                refine ⟨51556347200176643693976365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137483592533804383183936973 51556347200176643693976365)
                ·
                  refine ⟨19333630200066241385241137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51556347200176643693976365 19333630200066241385241137)
                  ·
                    refine ⟨14500222650049681038930853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19333630200066241385241137 14500222650049681038930853)
                    ·
                      refine ⟨2718791746884315194799535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14500222650049681038930853 2718791746884315194799535)
                      ·
                        rfl

theorem cell23_5294828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_5294828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294828 prefixEnd_5294828 := by exact prefixLift 5294828
  have htrace : WordTrace (prefixWord ++ tailWord_5294828) baseStart_5294828 baseEnd_5294828 := by
    simpa [prefixWord, tailWord_5294828, baseEnd_5294828] using wordTrace_append hprefix tailTrace_5294828
  have hstable : (prefixWord ++ tailWord_5294828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294828).length < 2 ^ (prefixWord ++ tailWord_5294828).sum := by decide
  have hdescent : baseEnd_5294828 < baseStart_5294828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294848 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 3]
def baseStart_5294848 : Nat := 118140960795 + 5294848 * 2 ^ 59
def prefixEnd_5294848 : Nat := 4983230072969 + 3 ^ 40 * 5294848 * 2
def baseEnd_5294848 : Nat := 2718802016497405116549443

theorem tailTrace_5294848 : CollatzResearch.WordTrace tailWord_5294848 prefixEnd_5294848 2718802016497405116549443 := by
  unfold tailWord_5294848
  simp only [CollatzResearch.WordTrace]
  refine ⟨96559485960838729444730599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128745981281118305926307465 96559485960838729444730599)
  ·
    refine ⟨144839228941258094167095899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96559485960838729444730599 144839228941258094167095899)
    ·
      refine ⟨217258843411887141250643849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144839228941258094167095899 217258843411887141250643849)
      ·
        refine ⟨162944132558915355937982887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217258843411887141250643849 162944132558915355937982887)
        ·
          refine ⟨244416198838373033906974331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162944132558915355937982887 244416198838373033906974331)
          ·
            refine ⟨366624298257559550860461497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244416198838373033906974331 366624298257559550860461497)
            ·
              refine ⟨274968223693169663145346123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366624298257559550860461497 274968223693169663145346123)
              ·
                refine ⟨412452335539754494718019185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274968223693169663145346123 412452335539754494718019185)
                ·
                  refine ⟨309339251654815871038514389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412452335539754494718019185 309339251654815871038514389)
                  ·
                    refine ⟨7250138710659746977465181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 309339251654815871038514389 7250138710659746977465181)
                    ·
                      refine ⟨2718802016497405116549443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7250138710659746977465181 2718802016497405116549443)
                      ·
                        rfl

theorem cell23_5294848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_5294848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294848 prefixEnd_5294848 := by exact prefixLift 5294848
  have htrace : WordTrace (prefixWord ++ tailWord_5294848) baseStart_5294848 baseEnd_5294848 := by
    simpa [prefixWord, tailWord_5294848, baseEnd_5294848] using wordTrace_append hprefix tailTrace_5294848
  have hstable : (prefixWord ++ tailWord_5294848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294848).length < 2 ^ (prefixWord ++ tailWord_5294848).sum := by decide
  have hdescent : baseEnd_5294848 < baseStart_5294848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294855 : List Nat := [1, 1, 4, 4, 1, 2, 2, 8]
def baseStart_5294855 : Nat := 118140960795 + 5294855 * 2 ^ 59
def prefixEnd_5294855 : Nat := 4983230072969 + 3 ^ 40 * 5294855 * 2
def baseEnd_5294855 : Nat := 100696504105999503302293

theorem tailTrace_5294855 : CollatzResearch.WordTrace tailWord_5294855 prefixEnd_5294855 100696504105999503302293 := by
  unfold tailWord_5294855
  simp only [CollatzResearch.WordTrace]
  refine ⟨193119227232652099084966019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128746151488434732723310679 193119227232652099084966019)
  ·
    refine ⟨289678840848978148627449029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193119227232652099084966019 289678840848978148627449029)
    ·
      refine ⟨54314782659183402867646693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289678840848978148627449029 54314782659183402867646693)
      ·
        refine ⟨10184021748596888037683755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54314782659183402867646693 10184021748596888037683755)
        ·
          refine ⟨15276032622895332056525633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10184021748596888037683755 15276032622895332056525633)
          ·
            refine ⟨11457024467171499042394225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15276032622895332056525633 11457024467171499042394225)
            ·
              refine ⟨8592768350378624281795669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11457024467171499042394225 8592768350378624281795669)
              ·
                refine ⟨100696504105999503302293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8592768350378624281795669 100696504105999503302293)
                ·
                  rfl

theorem cell23_5294855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 8].length) (baseStart_5294855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294855 prefixEnd_5294855 := by exact prefixLift 5294855
  have htrace : WordTrace (prefixWord ++ tailWord_5294855) baseStart_5294855 baseEnd_5294855 := by
    simpa [prefixWord, tailWord_5294855, baseEnd_5294855] using wordTrace_append hprefix tailTrace_5294855
  have hstable : (prefixWord ++ tailWord_5294855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294855).length < 2 ^ (prefixWord ++ tailWord_5294855).sum := by decide
  have hdescent : baseEnd_5294855 < baseStart_5294855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294858 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_5294858 : Nat := 118140960795 + 5294858 * 2 ^ 59
def prefixEnd_5294858 : Nat := 4983230072969 + 3 ^ 40 * 5294858 * 2
def baseEnd_5294858 : Nat := 2718807151303950077424397

theorem tailTrace_5294858 : CollatzResearch.WordTrace tailWord_5294858 prefixEnd_5294858 2718807151303950077424397 := by
  unfold tailWord_5294858
  simp only [CollatzResearch.WordTrace]
  refine ⟨48279834162910307649331307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128746224434427487064883485 48279834162910307649331307)
  ·
    refine ⟨72419751244365461473996961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48279834162910307649331307 72419751244365461473996961)
    ·
      refine ⟨54314813433274096105497721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72419751244365461473996961 54314813433274096105497721)
      ·
        refine ⟨40736110074955572079123291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54314813433274096105497721 40736110074955572079123291)
        ·
          refine ⟨61104165112433358118684937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40736110074955572079123291 61104165112433358118684937)
          ·
            refine ⟨45828123834325018589013703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61104165112433358118684937 45828123834325018589013703)
            ·
              refine ⟨68742185751487527883520555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45828123834325018589013703 68742185751487527883520555)
              ·
                refine ⟨103113278627231291825280833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68742185751487527883520555 103113278627231291825280833)
                ·
                  refine ⟨77334958970423468868960625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103113278627231291825280833 77334958970423468868960625)
                  ·
                    refine ⟨58001219227817601651720469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77334958970423468868960625 58001219227817601651720469)
                    ·
                      refine ⟨2718807151303950077424397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58001219227817601651720469 2718807151303950077424397)
                      ·
                        rfl

theorem cell23_5294858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_5294858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294858 prefixEnd_5294858 := by exact prefixLift 5294858
  have htrace : WordTrace (prefixWord ++ tailWord_5294858) baseStart_5294858 baseEnd_5294858 := by
    simpa [prefixWord, tailWord_5294858, baseEnd_5294858] using wordTrace_append hprefix tailTrace_5294858
  have hstable : (prefixWord ++ tailWord_5294858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294858).length < 2 ^ (prefixWord ++ tailWord_5294858).sum := by decide
  have hdescent : baseEnd_5294858 < baseStart_5294858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294866 : List Nat := [3, 2, 4, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_5294866 : Nat := 118140960795 + 5294866 * 2 ^ 59
def prefixEnd_5294866 : Nat := 4983230072969 + 3 ^ 40 * 5294866 * 2
def baseEnd_5294866 : Nat := 2718811259149186046124361

theorem tailTrace_5294866 : CollatzResearch.WordTrace tailWord_5294866 prefixEnd_5294866 2718811259149186046124361 := by
  unfold tailWord_5294866
  simp only [CollatzResearch.WordTrace]
  refine ⟨48279907108903061990904113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128746418957074831975744301 48279907108903061990904113)
  ·
    refine ⟨36209930331677296493178085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48279907108903061990904113 36209930331677296493178085)
    ·
      refine ⟨6789361937189493092470891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36209930331677296493178085 6789361937189493092470891)
      ·
        refine ⟨10184042905784239638706337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6789361937189493092470891 10184042905784239638706337)
        ·
          refine ⟨7638032179338179729029753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10184042905784239638706337 7638032179338179729029753)
          ·
            refine ⟨5728524134503634796772315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7638032179338179729029753 5728524134503634796772315)
            ·
              refine ⟨8592786201755452195158473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5728524134503634796772315 8592786201755452195158473)
              ·
                refine ⟨6444589651316589146368855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8592786201755452195158473 6444589651316589146368855)
                ·
                  refine ⟨9666884476974883719553283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6444589651316589146368855 9666884476974883719553283)
                  ·
                    refine ⟨14500326715462325579329925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9666884476974883719553283 14500326715462325579329925)
                    ·
                      refine ⟨2718811259149186046124361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14500326715462325579329925 2718811259149186046124361)
                      ·
                        rfl

theorem cell23_5294866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_5294866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294866 prefixEnd_5294866 := by exact prefixLift 5294866
  have htrace : WordTrace (prefixWord ++ tailWord_5294866) baseStart_5294866 baseEnd_5294866 := by
    simpa [prefixWord, tailWord_5294866, baseEnd_5294866] using wordTrace_append hprefix tailTrace_5294866
  have hstable : (prefixWord ++ tailWord_5294866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294866).length < 2 ^ (prefixWord ++ tailWord_5294866).sum := by decide
  have hdescent : baseEnd_5294866 < baseStart_5294866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294882 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_5294882 : Nat := 118140960795 + 5294882 * 2 ^ 59
def prefixEnd_5294882 : Nat := 4983230072969 + 3 ^ 40 * 5294882 * 2
def baseEnd_5294882 : Nat := 2718819474839657983524287

theorem tailTrace_5294882 : CollatzResearch.WordTrace tailWord_5294882 prefixEnd_5294882 2718819474839657983524287 := by
  unfold tailWord_5294882
  simp only [CollatzResearch.WordTrace]
  refine ⟨48280053000888570674049725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128746808002369521797465933 48280053000888570674049725)
  ·
    refine ⟨18105019875333214002768647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48280053000888570674049725 18105019875333214002768647)
    ·
      refine ⟨27157529812999821004152971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18105019875333214002768647 27157529812999821004152971)
      ·
        refine ⟨40736294719499731506229457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27157529812999821004152971 40736294719499731506229457)
        ·
          refine ⟨30552221039624798629672093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40736294719499731506229457 30552221039624798629672093)
          ·
            refine ⟨11457082889859299486127035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30552221039624798629672093 11457082889859299486127035)
            ·
              refine ⟨17185624334788949229190553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11457082889859299486127035 17185624334788949229190553)
              ·
                refine ⟨12889218251091711921892915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17185624334788949229190553 12889218251091711921892915)
                ·
                  refine ⟨19333827376637567882839373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12889218251091711921892915 19333827376637567882839373)
                  ·
                    refine ⟨7250185266239087956064765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19333827376637567882839373 7250185266239087956064765)
                    ·
                      refine ⟨2718819474839657983524287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7250185266239087956064765 2718819474839657983524287)
                      ·
                        rfl

theorem cell23_5294882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_5294882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294882 prefixEnd_5294882 := by exact prefixLift 5294882
  have htrace : WordTrace (prefixWord ++ tailWord_5294882) baseStart_5294882 baseEnd_5294882 := by
    simpa [prefixWord, tailWord_5294882, baseEnd_5294882] using wordTrace_append hprefix tailTrace_5294882
  have hstable : (prefixWord ++ tailWord_5294882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294882).length < 2 ^ (prefixWord ++ tailWord_5294882).sum := by decide
  have hdescent : baseEnd_5294882 < baseStart_5294882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294899 : List Nat := [1, 1, 1, 2, 6, 2, 2, 2, 2, 1, 3]
def baseStart_5294899 : Nat := 118140960795 + 5294899 * 2 ^ 59
def prefixEnd_5294899 : Nat := 4983230072969 + 3 ^ 40 * 5294899 * 2
def baseEnd_5294899 : Nat := 2718828204010784417011709

theorem tailTrace_5294899 : CollatzResearch.WordTrace tailWord_5294899 prefixEnd_5294899 2718828204010784417011709 := by
  unfold tailWord_5294899
  simp only [CollatzResearch.WordTrace]
  refine ⟨193120832044492694599567751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128747221362995129733045167 193120832044492694599567751)
  ·
    refine ⟨289681248066739041899351627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193120832044492694599567751 289681248066739041899351627)
    ·
      refine ⟨434521872100108562849027441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289681248066739041899351627 434521872100108562849027441)
      ·
        refine ⟨325891404075081422136770581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434521872100108562849027441 325891404075081422136770581)
        ·
          refine ⟨15276159566019441662661121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 325891404075081422136770581 15276159566019441662661121)
          ·
            refine ⟨11457119674514581246995841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15276159566019441662661121 11457119674514581246995841)
            ·
              refine ⟨8592839755885935935246881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11457119674514581246995841 8592839755885935935246881)
              ·
                refine ⟨6444629816914451951435161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8592839755885935935246881 6444629816914451951435161)
                ·
                  refine ⟨4833472362685838963576371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6444629816914451951435161 4833472362685838963576371)
                  ·
                    refine ⟨7250208544028758445364557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4833472362685838963576371 7250208544028758445364557)
                    ·
                      refine ⟨2718828204010784417011709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7250208544028758445364557 2718828204010784417011709)
                      ·
                        rfl

theorem cell23_5294899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 1, 3].length) (baseStart_5294899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294899 prefixEnd_5294899 := by exact prefixLift 5294899
  have htrace : WordTrace (prefixWord ++ tailWord_5294899) baseStart_5294899 baseEnd_5294899 := by
    simpa [prefixWord, tailWord_5294899, baseEnd_5294899] using wordTrace_append hprefix tailTrace_5294899
  have hstable : (prefixWord ++ tailWord_5294899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294899).length < 2 ^ (prefixWord ++ tailWord_5294899).sum := by decide
  have hdescent : baseEnd_5294899 < baseStart_5294899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294916 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_5294916 : Nat := 118140960795 + 5294916 * 2 ^ 59
def prefixEnd_5294916 : Nat := 4983230072969 + 3 ^ 40 * 5294916 * 2
def baseEnd_5294916 : Nat := 2718836933181910850499131

theorem tailTrace_5294916 : CollatzResearch.WordTrace tailWord_5294916 prefixEnd_5294916 2718836933181910850499131 := by
  unfold tailWord_5294916
  simp only [CollatzResearch.WordTrace]
  refine ⟨96560726042715553251468301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128747634723620737668624401 96560726042715553251468301)
  ·
    refine ⟨36210272266018332469300613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96560726042715553251468301 36210272266018332469300613)
    ·
      refine ⟨6789426049878437337993865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36210272266018332469300613 6789426049878437337993865)
      ·
        refine ⟨5092069537408828003495399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6789426049878437337993865 5092069537408828003495399)
        ·
          refine ⟨7638104306113242005243099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5092069537408828003495399 7638104306113242005243099)
          ·
            refine ⟨11457156459169863007864649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7638104306113242005243099 11457156459169863007864649)
            ·
              refine ⟨8592867344377397255898487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11457156459169863007864649 8592867344377397255898487)
              ·
                refine ⟨12889301016566095883847731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8592867344377397255898487 12889301016566095883847731)
                ·
                  refine ⟨19333951524849143825771597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12889301016566095883847731 19333951524849143825771597)
                  ·
                    refine ⟨7250231821818428934664349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19333951524849143825771597 7250231821818428934664349)
                    ·
                      refine ⟨2718836933181910850499131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7250231821818428934664349 2718836933181910850499131)
                      ·
                        rfl

theorem cell23_5294916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_5294916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294916 prefixEnd_5294916 := by exact prefixLift 5294916
  have htrace : WordTrace (prefixWord ++ tailWord_5294916) baseStart_5294916 baseEnd_5294916 := by
    simpa [prefixWord, tailWord_5294916, baseEnd_5294916] using wordTrace_append hprefix tailTrace_5294916
  have hstable : (prefixWord ++ tailWord_5294916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294916).length < 2 ^ (prefixWord ++ tailWord_5294916).sum := by decide
  have hdescent : baseEnd_5294916 < baseStart_5294916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294928 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 9]
def baseStart_5294928 : Nat := 118140960795 + 5294928 * 2 ^ 59
def prefixEnd_5294928 : Nat := 4983230072969 + 3 ^ 40 * 5294928 * 2
def baseEnd_5294928 : Nat := 302093677216640533727675

theorem tailTrace_5294928 : CollatzResearch.WordTrace tailWord_5294928 prefixEnd_5294928 302093677216640533727675 := by
  unfold tailWord_5294928
  simp only [CollatzResearch.WordTrace]
  refine ⟨96560944880693816276186719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128747926507591755034915625 96560944880693816276186719)
  ·
    refine ⟨144841417321040724414280079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96560944880693816276186719 144841417321040724414280079)
    ·
      refine ⟨217262125981561086621420119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144841417321040724414280079 217262125981561086621420119)
      ·
        refine ⟨325893188972341629932130179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217262125981561086621420119 325893188972341629932130179)
        ·
          refine ⟨488839783458512444898195269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325893188972341629932130179 488839783458512444898195269)
          ·
            refine ⟨91657459398471083418411613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 488839783458512444898195269 91657459398471083418411613)
            ·
              refine ⟨34371547274426656281904355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91657459398471083418411613 34371547274426656281904355)
              ·
                refine ⟨51557320911639984422856533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34371547274426656281904355 51557320911639984422856533)
                ·
                  refine ⟨302093677216640533727675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51557320911639984422856533 302093677216640533727675)
                  ·
                    rfl

theorem cell23_5294928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 9].length) (baseStart_5294928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294928 prefixEnd_5294928 := by exact prefixLift 5294928
  have htrace : WordTrace (prefixWord ++ tailWord_5294928) baseStart_5294928 baseEnd_5294928 := by
    simpa [prefixWord, tailWord_5294928, baseEnd_5294928] using wordTrace_append hprefix tailTrace_5294928
  have hstable : (prefixWord ++ tailWord_5294928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294928).length < 2 ^ (prefixWord ++ tailWord_5294928).sum := by decide
  have hdescent : baseEnd_5294928 < baseStart_5294928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294955 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 3]
def baseStart_5294955 : Nat := 118140960795 + 5294955 * 2 ^ 59
def prefixEnd_5294955 : Nat := 4983230072969 + 3 ^ 40 * 5294955 * 2
def baseEnd_5294955 : Nat := 2718856958927436197911451

theorem tailTrace_5294955 : CollatzResearch.WordTrace tailWord_5294955 prefixEnd_5294955 2718856958927436197911451 := by
  unfold tailWord_5294955
  simp only [CollatzResearch.WordTrace]
  refine ⟨193122874532289816163606319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128748583021526544109070879 193122874532289816163606319)
  ·
    refine ⟨289684311798434724245409479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193122874532289816163606319 289684311798434724245409479)
    ·
      refine ⟨434526467697652086368114219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289684311798434724245409479 434526467697652086368114219)
      ·
        refine ⟨651789701546478129552171329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434526467697652086368114219 651789701546478129552171329)
        ·
          refine ⟨488842276159858597164128497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 651789701546478129552171329 488842276159858597164128497)
          ·
            refine ⟨366631707119893947873096373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488842276159858597164128497 366631707119893947873096373)
            ·
              refine ⟨34371722542490057613102785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 366631707119893947873096373 34371722542490057613102785)
              ·
                refine ⟨25778791906867543209827089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34371722542490057613102785 25778791906867543209827089)
                ·
                  refine ⟨19334093930150657407370317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25778791906867543209827089 19334093930150657407370317)
                  ·
                    refine ⟨7250285223806496527763869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19334093930150657407370317 7250285223806496527763869)
                    ·
                      refine ⟨2718856958927436197911451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7250285223806496527763869 2718856958927436197911451)
                      ·
                        rfl

theorem cell23_5294955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 3].length) (baseStart_5294955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294955 prefixEnd_5294955 := by exact prefixLift 5294955
  have htrace : WordTrace (prefixWord ++ tailWord_5294955) baseStart_5294955 baseEnd_5294955 := by
    simpa [prefixWord, tailWord_5294955, baseEnd_5294955] using wordTrace_append hprefix tailTrace_5294955
  have hstable : (prefixWord ++ tailWord_5294955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294955).length < 2 ^ (prefixWord ++ tailWord_5294955).sum := by decide
  have hdescent : baseEnd_5294955 < baseStart_5294955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5294962 : List Nat := [3, 2, 1, 2, 1, 1, 4, 4, 5]
def baseStart_5294962 : Nat := 118140960795 + 5294962 * 2 ^ 59
def prefixEnd_5294962 : Nat := 4983230072969 + 3 ^ 40 * 5294962 * 2
def baseEnd_5294962 : Nat := 302095617032446407835991

theorem tailTrace_5294962 : CollatzResearch.WordTrace tailWord_5294962 prefixEnd_5294962 302095617032446407835991 := by
  unfold tailWord_5294962
  simp only [CollatzResearch.WordTrace]
  refine ⟨48280782460816114089777785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128748753228842970906074093 48280782460816114089777785)
  ·
    refine ⟨36210586845612085567333339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48280782460816114089777785 36210586845612085567333339)
    ·
      refine ⟨54315880268418128351000009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36210586845612085567333339 54315880268418128351000009)
      ·
        refine ⟨40736910201313596263250007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54315880268418128351000009 40736910201313596263250007)
        ·
          refine ⟨61105365301970394394875011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40736910201313596263250007 61105365301970394394875011)
          ·
            refine ⟨91658047952955591592312517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61105365301970394394875011 91658047952955591592312517)
            ·
              refine ⟨17185883991179173423558597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91658047952955591592312517 17185883991179173423558597)
              ·
                refine ⟨3222353248346095016917237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17185883991179173423558597 3222353248346095016917237)
                ·
                  refine ⟨302095617032446407835991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3222353248346095016917237 302095617032446407835991)
                  ·
                    rfl

theorem cell23_5294962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_5294962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5294962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5294962 prefixEnd_5294962 := by exact prefixLift 5294962
  have htrace : WordTrace (prefixWord ++ tailWord_5294962) baseStart_5294962 baseEnd_5294962 := by
    simpa [prefixWord, tailWord_5294962, baseEnd_5294962] using wordTrace_append hprefix tailTrace_5294962
  have hstable : (prefixWord ++ tailWord_5294962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5294962).length < 2 ^ (prefixWord ++ tailWord_5294962).sum := by decide
  have hdescent : baseEnd_5294962 < baseStart_5294962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5294962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295012 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_5295012 : Nat := 118140960795 + 5295012 * 2 ^ 59
def prefixEnd_5295012 : Nat := 4983230072969 + 3 ^ 40 * 5295012 * 2
def baseEnd_5295012 : Nat := 2718886227324742474898689

theorem tailTrace_5295012 : CollatzResearch.WordTrace tailWord_5295012 prefixEnd_5295012 2718886227324742474898689 := by
  unfold tailWord_5295012
  simp only [CollatzResearch.WordTrace]
  refine ⟨96562476746541657449215645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128749968995388876598954193 96562476746541657449215645)
  ·
    refine ⟨36210928779953121543455867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96562476746541657449215645 36210928779953121543455867)
    ·
      refine ⟨54316393169929682315183801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36210928779953121543455867 54316393169929682315183801)
      ·
        refine ⟨40737294877447261736387851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54316393169929682315183801 40737294877447261736387851)
        ·
          refine ⟨61105942316170892604581777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40737294877447261736387851 61105942316170892604581777)
          ·
            refine ⟨45829456737128169453436333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61105942316170892604581777 45829456737128169453436333)
            ·
              refine ⟨17186046276423063545038625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45829456737128169453436333 17186046276423063545038625)
              ·
                refine ⟨12889534707317297658778969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17186046276423063545038625 12889534707317297658778969)
                ·
                  refine ⟨9667151030487973244084227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12889534707317297658778969 9667151030487973244084227)
                  ·
                    refine ⟨14500726545731959866126341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9667151030487973244084227 14500726545731959866126341)
                    ·
                      refine ⟨2718886227324742474898689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14500726545731959866126341 2718886227324742474898689)
                      ·
                        rfl

theorem cell23_5295012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_5295012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295012 prefixEnd_5295012 := by exact prefixLift 5295012
  have htrace : WordTrace (prefixWord ++ tailWord_5295012) baseStart_5295012 baseEnd_5295012 := by
    simpa [prefixWord, tailWord_5295012, baseEnd_5295012] using wordTrace_append hprefix tailTrace_5295012
  have hstable : (prefixWord ++ tailWord_5295012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295012).length < 2 ^ (prefixWord ++ tailWord_5295012).sum := by decide
  have hdescent : baseEnd_5295012 < baseStart_5295012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295069 : List Nat := [1, 4, 3, 1, 2, 2, 2, 2, 6]
def baseStart_5295069 : Nat := 118140960795 + 5295069 * 2 ^ 59
def prefixEnd_5295069 : Nat := 4983230072969 + 3 ^ 40 * 5295069 * 2
def baseEnd_5295069 : Nat := 302101721746894305765103

theorem tailTrace_5295069 : CollatzResearch.WordTrace tailWord_5295069 prefixEnd_5295069 302101721746894305765103 := by
  unfold tailWord_5295069
  simp only [CollatzResearch.WordTrace]
  refine ⟨193127032453876813633256261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128751354969251209088837507 193127032453876813633256261)
  ·
    refine ⟨36211318585101902556235549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193127032453876813633256261 36211318585101902556235549)
    ·
      refine ⟨13579244469413213458588331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36211318585101902556235549 13579244469413213458588331)
      ·
        refine ⟨20368866704119820187882497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13579244469413213458588331 20368866704119820187882497)
        ·
          refine ⟨15276650028089865140911873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20368866704119820187882497 15276650028089865140911873)
          ·
            refine ⟨11457487521067398855683905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15276650028089865140911873 11457487521067398855683905)
            ·
              refine ⟨8593115640800549141762929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11457487521067398855683905 8593115640800549141762929)
              ·
                refine ⟨6444836730600411856322197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8593115640800549141762929 6444836730600411856322197)
                ·
                  refine ⟨302101721746894305765103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6444836730600411856322197 302101721746894305765103)
                  ·
                    rfl

theorem cell23_5295069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_5295069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295069 prefixEnd_5295069 := by exact prefixLift 5295069
  have htrace : WordTrace (prefixWord ++ tailWord_5295069) baseStart_5295069 baseEnd_5295069 := by
    simpa [prefixWord, tailWord_5295069, baseEnd_5295069] using wordTrace_append hprefix tailTrace_5295069
  have hstable : (prefixWord ++ tailWord_5295069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295069).length < 2 ^ (prefixWord ++ tailWord_5295069).sum := by decide
  have hdescent : baseEnd_5295069 < baseStart_5295069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295072 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 5, 5, 2]
def baseStart_5295072 : Nat := 118140960795 + 5295072 * 2 ^ 59
def prefixEnd_5295072 : Nat := 4983230072969 + 3 ^ 40 * 5295072 * 2
def baseEnd_5295072 : Nat := 2718917036164012240148413

theorem tailTrace_5295072 : CollatzResearch.WordTrace tailWord_5295072 prefixEnd_5295072 2718917036164012240148413 := by
  unfold tailWord_5295072
  simp only [CollatzResearch.WordTrace]
  refine ⟨96563570936432972572807735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128751427915243963430410313 96563570936432972572807735)
  ·
    refine ⟨144845356404649458859211603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96563570936432972572807735 144845356404649458859211603)
    ·
      refine ⟨217268034606974188288817405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144845356404649458859211603 217268034606974188288817405)
      ·
        refine ⟨81475512977615320608306527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217268034606974188288817405 81475512977615320608306527)
        ·
          refine ⟨122213269466422980912459791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81475512977615320608306527 122213269466422980912459791)
          ·
            refine ⟨183319904199634471368689687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122213269466422980912459791 183319904199634471368689687)
            ·
              refine ⟨274979856299451707053034531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183319904199634471368689687 274979856299451707053034531)
              ·
                refine ⟨412469784449177560579551797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274979856299451707053034531 412469784449177560579551797)
                ·
                  refine ⟨38669042292110396304332981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 412469784449177560579551797 38669042292110396304332981)
                  ·
                    refine ⟨3625222714885349653531217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38669042292110396304332981 3625222714885349653531217)
                    ·
                      refine ⟨2718917036164012240148413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3625222714885349653531217 2718917036164012240148413)
                      ·
                        rfl

theorem cell23_5295072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_5295072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295072 prefixEnd_5295072 := by exact prefixLift 5295072
  have htrace : WordTrace (prefixWord ++ tailWord_5295072) baseStart_5295072 baseEnd_5295072 := by
    simpa [prefixWord, tailWord_5295072, baseEnd_5295072] using wordTrace_append hprefix tailTrace_5295072
  have hstable : (prefixWord ++ tailWord_5295072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295072).length < 2 ^ (prefixWord ++ tailWord_5295072).sum := by decide
  have hdescent : baseEnd_5295072 < baseStart_5295072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295082 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 3, 5]
def baseStart_5295082 : Nat := 118140960795 + 5295082 * 2 ^ 59
def prefixEnd_5295082 : Nat := 4983230072969 + 3 ^ 40 * 5295082 * 2
def baseEnd_5295082 : Nat := 906307390323519067007789

theorem tailTrace_5295082 : CollatzResearch.WordTrace tailWord_5295082 prefixEnd_5295082 906307390323519067007789 := by
  unfold tailWord_5295082
  simp only [CollatzResearch.WordTrace]
  refine ⟨48281876650707429213369875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128751671068553144568986333 48281876650707429213369875)
  ·
    refine ⟨72422814976061143820054813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48281876650707429213369875 72422814976061143820054813)
    ·
      refine ⟨27158555616022928932520555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72422814976061143820054813 27158555616022928932520555)
      ·
        refine ⟨40737833424034393398780833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27158555616022928932520555 40737833424034393398780833)
        ·
          refine ⟨30553375068025795049085625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40737833424034393398780833 30553375068025795049085625)
          ·
            refine ⟨22915031301019346286814219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30553375068025795049085625 22915031301019346286814219)
            ·
              refine ⟨34372546951529019430221329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22915031301019346286814219 34372546951529019430221329)
              ·
                refine ⟨25779410213646764572665997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34372546951529019430221329 25779410213646764572665997)
                ·
                  refine ⟨9667278830117536714749749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25779410213646764572665997 9667278830117536714749749)
                  ·
                    refine ⟨906307390323519067007789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9667278830117536714749749 906307390323519067007789)
                    ·
                      rfl

theorem cell23_5295082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_5295082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295082 prefixEnd_5295082 := by exact prefixLift 5295082
  have htrace : WordTrace (prefixWord ++ tailWord_5295082) baseStart_5295082 baseEnd_5295082 := by
    simpa [prefixWord, tailWord_5295082, baseEnd_5295082] using wordTrace_append hprefix tailTrace_5295082
  have hstable : (prefixWord ++ tailWord_5295082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295082).length < 2 ^ (prefixWord ++ tailWord_5295082).sum := by decide
  have hdescent : baseEnd_5295082 < baseStart_5295082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295112 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 1, 6]
def baseStart_5295112 : Nat := 118140960795 + 5295112 * 2 ^ 59
def prefixEnd_5295112 : Nat := 4983230072969 + 3 ^ 40 * 5295112 * 2
def baseEnd_5295112 : Nat := 906312525130064027882743

theorem tailTrace_5295112 : CollatzResearch.WordTrace tailWord_5295112 prefixEnd_5295112 906312525130064027882743 := by
  unfold tailWord_5295112
  simp only [CollatzResearch.WordTrace]
  refine ⟨96564300396360515988535795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128752400528480687984714393 96564300396360515988535795)
  ·
    refine ⟨144846450594540773982803693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96564300396360515988535795 144846450594540773982803693)
    ·
      refine ⟨54317418972952790243551385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144846450594540773982803693 54317418972952790243551385)
      ·
        refine ⟨40738064229714592682663539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54317418972952790243551385 40738064229714592682663539)
        ·
          refine ⟨61107096344571889023995309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40738064229714592682663539 61107096344571889023995309)
          ·
            refine ⟨22915161129214458383998241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61107096344571889023995309 22915161129214458383998241)
            ·
              refine ⟨17186370846910843787998681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22915161129214458383998241 17186370846910843787998681)
              ·
                refine ⟨12889778135183132840999011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17186370846910843787998681 12889778135183132840999011)
                ·
                  refine ⟨19334667202774699261498517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12889778135183132840999011 19334667202774699261498517)
                  ·
                    refine ⟨906312525130064027882743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19334667202774699261498517 906312525130064027882743)
                    ·
                      rfl

theorem cell23_5295112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_5295112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295112 prefixEnd_5295112 := by exact prefixLift 5295112
  have htrace : WordTrace (prefixWord ++ tailWord_5295112) baseStart_5295112 baseEnd_5295112 := by
    simpa [prefixWord, tailWord_5295112, baseEnd_5295112] using wordTrace_append hprefix tailTrace_5295112
  have hstable : (prefixWord ++ tailWord_5295112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295112).length < 2 ^ (prefixWord ++ tailWord_5295112).sum := by decide
  have hdescent : baseEnd_5295112 < baseStart_5295112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295116 : List Nat := [2, 2, 1, 2, 3, 4, 2, 1, 1, 5]
def baseStart_5295116 : Nat := 118140960795 + 5295116 * 2 ^ 59
def prefixEnd_5295116 : Nat := 4983230072969 + 3 ^ 40 * 5295116 * 2
def baseEnd_5295116 : Nat := 906313209770936689332737

theorem tailTrace_5295116 : CollatzResearch.WordTrace tailWord_5295116 prefixEnd_5295116 906313209770936689332737 := by
  unfold tailWord_5295116
  simp only [CollatzResearch.WordTrace]
  refine ⟨96564373342353270330108601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128752497789804360440144801 96564373342353270330108601)
  ·
    refine ⟨72423280006764952747581451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96564373342353270330108601 72423280006764952747581451)
    ·
      refine ⟨108634920010147429121372177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72423280006764952747581451 108634920010147429121372177)
      ·
        refine ⟨81476190007610571841029133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108634920010147429121372177 81476190007610571841029133)
        ·
          refine ⟨30553571252853964440385925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81476190007610571841029133 30553571252853964440385925)
          ·
            refine ⟨5728794609910118332572361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30553571252853964440385925 5728794609910118332572361)
            ·
              refine ⟨4296595957432588749429271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5728794609910118332572361 4296595957432588749429271)
              ·
                refine ⟨6444893936148883124143907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4296595957432588749429271 6444893936148883124143907)
                ·
                  refine ⟨9667340904223324686215861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6444893936148883124143907 9667340904223324686215861)
                  ·
                    refine ⟨906313209770936689332737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9667340904223324686215861 906313209770936689332737)
                    ·
                      rfl

theorem cell23_5295116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_5295116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295116 prefixEnd_5295116 := by exact prefixLift 5295116
  have htrace : WordTrace (prefixWord ++ tailWord_5295116) baseStart_5295116 baseEnd_5295116 := by
    simpa [prefixWord, tailWord_5295116, baseEnd_5295116] using wordTrace_append hprefix tailTrace_5295116
  have hstable : (prefixWord ++ tailWord_5295116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295116).length < 2 ^ (prefixWord ++ tailWord_5295116).sum := by decide
  have hdescent : baseEnd_5295116 < baseStart_5295116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295129 : List Nat := [1, 2, 1, 2, 1, 1, 7, 2, 2, 4]
def baseStart_5295129 : Nat := 118140960795 + 5295129 * 2 ^ 59
def prefixEnd_5295129 : Nat := 4983230072969 + 3 ^ 40 * 5295129 * 2
def baseEnd_5295129 : Nat := 906315434853772839045217

theorem tailTrace_5295129 : CollatzResearch.WordTrace tailWord_5295129 prefixEnd_5295129 906315434853772839045217 := by
  unfold tailWord_5295129
  simp only [CollatzResearch.WordTrace]
  refine ⟨193129220833659443880440441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128752813889106295920293627 193129220833659443880440441)
  ·
    refine ⟨144846915625244582910330331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193129220833659443880440441 144846915625244582910330331)
    ·
      refine ⟨217270373437866874365495497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144846915625244582910330331 217270373437866874365495497)
      ·
        refine ⟨162952780078400155774121623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217270373437866874365495497 162952780078400155774121623)
        ·
          refine ⟨244429170117600233661182435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162952780078400155774121623 244429170117600233661182435)
          ·
            refine ⟨366643755176400350491773653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244429170117600233661182435 366643755176400350491773653)
            ·
              refine ⟨8593213011946883214650945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 366643755176400350491773653 8593213011946883214650945)
              ·
                refine ⟨6444909758960162410988209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8593213011946883214650945 6444909758960162410988209)
                ·
                  refine ⟨4833682319220121808241157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6444909758960162410988209 4833682319220121808241157)
                  ·
                    refine ⟨906315434853772839045217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4833682319220121808241157 906315434853772839045217)
                    ·
                      rfl

theorem cell23_5295129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 4].length) (baseStart_5295129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295129 prefixEnd_5295129 := by exact prefixLift 5295129
  have htrace : WordTrace (prefixWord ++ tailWord_5295129) baseStart_5295129 baseEnd_5295129 := by
    simpa [prefixWord, tailWord_5295129, baseEnd_5295129] using wordTrace_append hprefix tailTrace_5295129
  have hstable : (prefixWord ++ tailWord_5295129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295129).length < 2 ^ (prefixWord ++ tailWord_5295129).sum := by decide
  have hdescent : baseEnd_5295129 < baseStart_5295129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295146 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 1, 6]
def baseStart_5295146 : Nat := 118140960795 + 5295146 * 2 ^ 59
def prefixEnd_5295146 : Nat := 4983230072969 + 3 ^ 40 * 5295146 * 2
def baseEnd_5295146 : Nat := 906318344577481650207691

theorem tailTrace_5295146 : CollatzResearch.WordTrace tailWord_5295146 prefixEnd_5295146 906318344577481650207691 := by
  unfold tailWord_5295146
  simp only [CollatzResearch.WordTrace]
  refine ⟨48282460218649463945952323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128753227249731903855872861 48282460218649463945952323)
  ·
    refine ⟨72423690327974195918928485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48282460218649463945952323 72423690327974195918928485)
    ·
      refine ⟨13579441936495161734799091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72423690327974195918928485 13579441936495161734799091)
      ·
        refine ⟨20369162904742742602198637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13579441936495161734799091 20369162904742742602198637)
        ·
          refine ⟨7638436089278528475824489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20369162904742742602198637 7638436089278528475824489)
          ·
            refine ⟨5728827066958896356868367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7638436089278528475824489 5728827066958896356868367)
            ·
              refine ⟨8593240600438344535302551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5728827066958896356868367 8593240600438344535302551)
              ·
                refine ⟨12889860900657516802953827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8593240600438344535302551 12889860900657516802953827)
                ·
                  refine ⟨19334791350986275204430741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12889860900657516802953827 19334791350986275204430741)
                  ·
                    refine ⟨906318344577481650207691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19334791350986275204430741 906318344577481650207691)
                    ·
                      rfl

theorem cell23_5295146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_5295146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295146 prefixEnd_5295146 := by exact prefixLift 5295146
  have htrace : WordTrace (prefixWord ++ tailWord_5295146) baseStart_5295146 baseEnd_5295146 := by
    simpa [prefixWord, tailWord_5295146, baseEnd_5295146] using wordTrace_append hprefix tailTrace_5295146
  have hstable : (prefixWord ++ tailWord_5295146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295146).length < 2 ^ (prefixWord ++ tailWord_5295146).sum := by decide
  have hdescent : baseEnd_5295146 < baseStart_5295146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295182 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_5295182 : Nat := 118140960795 + 5295182 * 2 ^ 59
def prefixEnd_5295182 : Nat := 4983230072969 + 3 ^ 40 * 5295182 * 2
def baseEnd_5295182 : Nat := 2718973519036006809772907

theorem tailTrace_5295182 : CollatzResearch.WordTrace tailWord_5295182 prefixEnd_5295182 2718973519036006809772907 := by
  unfold tailWord_5295182
  simp only [CollatzResearch.WordTrace]
  refine ⟨24141394237808429241514975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128754102601644955954746533 24141394237808429241514975)
  ·
    refine ⟨36212091356712643862272463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24141394237808429241514975 36212091356712643862272463)
    ·
      refine ⟨54318137035068965793408695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36212091356712643862272463 54318137035068965793408695)
      ·
        refine ⟨81477205552603448690113043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54318137035068965793408695 81477205552603448690113043)
        ·
          refine ⟨122215808328905173035169565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81477205552603448690113043 122215808328905173035169565)
          ·
            refine ⟨45830928123339439888188587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122215808328905173035169565 45830928123339439888188587)
            ·
              refine ⟨68746392185009159832282881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45830928123339439888188587 68746392185009159832282881)
              ·
                refine ⟨51559794138756869874212161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68746392185009159832282881 51559794138756869874212161)
                ·
                  refine ⟨38669845604067652405659121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51559794138756869874212161 38669845604067652405659121)
                  ·
                    refine ⟨29002384203050739304244341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38669845604067652405659121 29002384203050739304244341)
                    ·
                      refine ⟨2718973519036006809772907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29002384203050739304244341 2718973519036006809772907)
                      ·
                        rfl

theorem cell23_5295182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_5295182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295182 prefixEnd_5295182 := by exact prefixLift 5295182
  have htrace : WordTrace (prefixWord ++ tailWord_5295182) baseStart_5295182 baseEnd_5295182 := by
    simpa [prefixWord, tailWord_5295182, baseEnd_5295182] using wordTrace_append hprefix tailTrace_5295182
  have hstable : (prefixWord ++ tailWord_5295182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295182).length < 2 ^ (prefixWord ++ tailWord_5295182).sum := by decide
  have hdescent : baseEnd_5295182 < baseStart_5295182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295186 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_5295186 : Nat := 118140960795 + 5295186 * 2 ^ 59
def prefixEnd_5295186 : Nat := 4983230072969 + 3 ^ 40 * 5295186 * 2
def baseEnd_5295186 : Nat := 2718975572958624794122889

theorem tailTrace_5295186 : CollatzResearch.WordTrace tailWord_5295186 prefixEnd_5295186 2718975572958624794122889 := by
  unfold tailWord_5295186
  simp only [CollatzResearch.WordTrace]
  refine ⟨48282824948613235653816353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128754199862968628410176941 48282824948613235653816353)
  ·
    refine ⟨36212118711459926740362265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48282824948613235653816353 36212118711459926740362265)
    ·
      refine ⟨27159089033594945055271699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36212118711459926740362265 27159089033594945055271699)
      ·
        refine ⟨40738633550392417582907549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27159089033594945055271699 40738633550392417582907549)
        ·
          refine ⟨15276987581397156593590331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40738633550392417582907549 15276987581397156593590331)
          ·
            refine ⟨22915481372095734890385497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15276987581397156593590331 22915481372095734890385497)
            ·
              refine ⟨17186611029071801167789123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22915481372095734890385497 17186611029071801167789123)
              ·
                refine ⟨25779916543607701751683685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17186611029071801167789123 25779916543607701751683685)
                ·
                  refine ⟨4833734351926444078440691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25779916543607701751683685 4833734351926444078440691)
                  ·
                    refine ⟨7250601527889666117661037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4833734351926444078440691 7250601527889666117661037)
                    ·
                      refine ⟨2718975572958624794122889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7250601527889666117661037 2718975572958624794122889)
                      ·
                        rfl

theorem cell23_5295186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_5295186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295186 prefixEnd_5295186 := by exact prefixLift 5295186
  have htrace : WordTrace (prefixWord ++ tailWord_5295186) baseStart_5295186 baseEnd_5295186 := by
    simpa [prefixWord, tailWord_5295186, baseEnd_5295186] using wordTrace_append hprefix tailTrace_5295186
  have hstable : (prefixWord ++ tailWord_5295186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295186).length < 2 ^ (prefixWord ++ tailWord_5295186).sum := by decide
  have hdescent : baseEnd_5295186 < baseStart_5295186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295192 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_5295192 : Nat := 118140960795 + 5295192 * 2 ^ 59
def prefixEnd_5295192 : Nat := 4983230072969 + 3 ^ 40 * 5295192 * 2
def baseEnd_5295192 : Nat := 2718978653842551770647861

theorem tailTrace_5295192 : CollatzResearch.WordTrace tailWord_5295192 prefixEnd_5295192 2718978653842551770647861 := by
  unfold tailWord_5295192
  simp only [CollatzResearch.WordTrace]
  refine ⟨96565759316215602819991915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128754345754954137093322553 96565759316215602819991915)
  ·
    refine ⟨144848638974323404229987873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96565759316215602819991915 144848638974323404229987873)
    ·
      refine ⟨108636479230742553172490905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144848638974323404229987873 108636479230742553172490905)
      ·
        refine ⟨81477359423056914879368179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108636479230742553172490905 81477359423056914879368179)
        ·
          refine ⟨122216039134585372319052269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81477359423056914879368179 122216039134585372319052269)
          ·
            refine ⟨45831014675469514619644601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122216039134585372319052269 45831014675469514619644601)
            ·
              refine ⟨34373261006602135964733451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45831014675469514619644601 34373261006602135964733451)
              ·
                refine ⟨51559891509903203947100177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34373261006602135964733451 51559891509903203947100177)
                ·
                  refine ⟨38669918632427402960325133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51559891509903203947100177 38669918632427402960325133)
                  ·
                    refine ⟨14501219487160276110121925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38669918632427402960325133 14501219487160276110121925)
                    ·
                      refine ⟨2718978653842551770647861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14501219487160276110121925 2718978653842551770647861)
                      ·
                        rfl

theorem cell23_5295192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_5295192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295192 prefixEnd_5295192 := by exact prefixLift 5295192
  have htrace : WordTrace (prefixWord ++ tailWord_5295192) baseStart_5295192 baseEnd_5295192 := by
    simpa [prefixWord, tailWord_5295192, baseEnd_5295192] using wordTrace_append hprefix tailTrace_5295192
  have hstable : (prefixWord ++ tailWord_5295192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295192).length < 2 ^ (prefixWord ++ tailWord_5295192).sum := by decide
  have hdescent : baseEnd_5295192 < baseStart_5295192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295196 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_5295196 : Nat := 118140960795 + 5295196 * 2 ^ 59
def prefixEnd_5295196 : Nat := 4983230072969 + 3 ^ 40 * 5295196 * 2
def baseEnd_5295196 : Nat := 2718980707765169754997843

theorem tailTrace_5295196 : CollatzResearch.WordTrace tailWord_5295196 prefixEnd_5295196 2718980707765169754997843 := by
  unfold tailWord_5295196
  simp only [CollatzResearch.WordTrace]
  refine ⟨96565832262208357161564721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128754443016277809548752961 96565832262208357161564721)
  ·
    refine ⟨72424374196656267871173541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96565832262208357161564721 72424374196656267871173541)
    ·
      refine ⟨13579570161873050225845039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72424374196656267871173541 13579570161873050225845039)
      ·
        refine ⟨20369355242809575338767559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13579570161873050225845039 20369355242809575338767559)
        ·
          refine ⟨30554032864214363008151339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20369355242809575338767559 30554032864214363008151339)
          ·
            refine ⟨45831049296321544512227009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30554032864214363008151339 45831049296321544512227009)
            ·
              refine ⟨34373286972241158384170257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45831049296321544512227009 34373286972241158384170257)
              ·
                refine ⟨25779965229180868788127693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34373286972241158384170257 25779965229180868788127693)
                ·
                  refine ⟨9667486960942825795547885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25779965229180868788127693 9667486960942825795547885)
                  ·
                    refine ⟨3625307610353559673330457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9667486960942825795547885 3625307610353559673330457)
                    ·
                      refine ⟨2718980707765169754997843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3625307610353559673330457 2718980707765169754997843)
                      ·
                        rfl

theorem cell23_5295196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_5295196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295196 prefixEnd_5295196 := by exact prefixLift 5295196
  have htrace : WordTrace (prefixWord ++ tailWord_5295196) baseStart_5295196 baseEnd_5295196 := by
    simpa [prefixWord, tailWord_5295196, baseEnd_5295196] using wordTrace_append hprefix tailTrace_5295196
  have hstable : (prefixWord ++ tailWord_5295196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295196).length < 2 ^ (prefixWord ++ tailWord_5295196).sum := by decide
  have hdescent : baseEnd_5295196 < baseStart_5295196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295197 : List Nat := [1, 4, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_5295197 : Nat := 118140960795 + 5295197 * 2 ^ 59
def prefixEnd_5295197 : Nat := 4983230072969 + 3 ^ 40 * 5295197 * 2
def baseEnd_5295197 : Nat := 906327073748608083695113

theorem tailTrace_5295197 : CollatzResearch.WordTrace tailWord_5295197 prefixEnd_5295197 906327073748608083695113 := by
  unfold tailWord_5295197
  simp only [CollatzResearch.WordTrace]
  refine ⟨193131700997413091493915845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128754467331608727662610563 193131700997413091493915845)
  ·
    refine ⟨36212193937014954655109221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193131700997413091493915845 36212193937014954655109221)
    ·
      refine ⟨6789786363190303997832979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36212193937014954655109221 6789786363190303997832979)
      ·
        refine ⟨10184679544785455996749469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6789786363190303997832979 10184679544785455996749469)
        ·
          refine ⟨3819254829294545998781051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10184679544785455996749469 3819254829294545998781051)
          ·
            refine ⟨5728882243941818998171577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3819254829294545998781051 5728882243941818998171577)
            ·
              refine ⟨4296661682956364248628683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5728882243941818998171577 4296661682956364248628683)
              ·
                refine ⟨6444992524434546372943025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4296661682956364248628683 6444992524434546372943025)
                ·
                  refine ⟨4833744393325909779707269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6444992524434546372943025 4833744393325909779707269)
                  ·
                    refine ⟨906327073748608083695113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4833744393325909779707269 906327073748608083695113)
                    ·
                      rfl

theorem cell23_5295197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_5295197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295197 prefixEnd_5295197 := by exact prefixLift 5295197
  have htrace : WordTrace (prefixWord ++ tailWord_5295197) baseStart_5295197 baseEnd_5295197 := by
    simpa [prefixWord, tailWord_5295197, baseEnd_5295197] using wordTrace_append hprefix tailTrace_5295197
  have hstable : (prefixWord ++ tailWord_5295197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295197).length < 2 ^ (prefixWord ++ tailWord_5295197).sum := by decide
  have hdescent : baseEnd_5295197 < baseStart_5295197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295212 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_5295212 : Nat := 118140960795 + 5295212 * 2 ^ 59
def prefixEnd_5295212 : Nat := 4983230072969 + 3 ^ 40 * 5295212 * 2
def baseEnd_5295212 : Nat := 2718988923455641692397769

theorem tailTrace_5295212 : CollatzResearch.WordTrace tailWord_5295212 prefixEnd_5295212 2718988923455641692397769 := by
  unfold tailWord_5295212
  simp only [CollatzResearch.WordTrace]
  refine ⟨96566124046179374527855945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128754832061572499370474593 96566124046179374527855945)
  ·
    refine ⟨72424593034634530895891959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96566124046179374527855945 72424593034634530895891959)
    ·
      refine ⟨108636889551951796343837939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72424593034634530895891959 108636889551951796343837939)
      ·
        refine ⟨162955334327927694515756909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108636889551951796343837939 162955334327927694515756909)
        ·
          refine ⟨61108250372972885443408841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162955334327927694515756909 61108250372972885443408841)
          ·
            refine ⟨45831187779729664082556631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61108250372972885443408841 45831187779729664082556631)
            ·
              refine ⟨68746781669594496123834947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45831187779729664082556631 68746781669594496123834947)
              ·
                refine ⟨103120172504391744185752421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68746781669594496123834947 103120172504391744185752421)
                ·
                  refine ⟨19335032344573452034828579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103120172504391744185752421 19335032344573452034828579)
                  ·
                    refine ⟨29002548516860178052242869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19335032344573452034828579 29002548516860178052242869)
                    ·
                      refine ⟨2718988923455641692397769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29002548516860178052242869 2718988923455641692397769)
                      ·
                        rfl

theorem cell23_5295212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_5295212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295212 prefixEnd_5295212 := by exact prefixLift 5295212
  have htrace : WordTrace (prefixWord ++ tailWord_5295212) baseStart_5295212 baseEnd_5295212 := by
    simpa [prefixWord, tailWord_5295212, baseEnd_5295212] using wordTrace_append hprefix tailTrace_5295212
  have hstable : (prefixWord ++ tailWord_5295212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295212).length < 2 ^ (prefixWord ++ tailWord_5295212).sum := by decide
  have hdescent : baseEnd_5295212 < baseStart_5295212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295213 : List Nat := [1, 5, 1, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_5295213 : Nat := 118140960795 + 5295213 * 2 ^ 59
def prefixEnd_5295213 : Nat := 4983230072969 + 3 ^ 40 * 5295213 * 2
def baseEnd_5295213 : Nat := 2718989436936296188485265

theorem tailTrace_5295213 : CollatzResearch.WordTrace tailWord_5295213 prefixEnd_5295213 2718989436936296188485265 := by
  unfold tailWord_5295213
  simp only [CollatzResearch.WordTrace]
  refine ⟨193132284565355126226498293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128754856376903417484332195 193132284565355126226498293)
  ·
    refine ⟨18106151678002043083734215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193132284565355126226498293 18106151678002043083734215)
    ·
      refine ⟨27159227517003064625601323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18106151678002043083734215 27159227517003064625601323)
      ·
        refine ⟨40738841275504596938401985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27159227517003064625601323 40738841275504596938401985)
        ·
          refine ⟨30554130956628447703801489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40738841275504596938401985 30554130956628447703801489)
          ·
            refine ⟨22915598217471335777851117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30554130956628447703801489 22915598217471335777851117)
            ·
              refine ⟨8593349331551750916694169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22915598217471335777851117 8593349331551750916694169)
              ·
                refine ⟨6445011998663813187520627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8593349331551750916694169 6445011998663813187520627)
                ·
                  refine ⟨9667517997995719781280941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6445011998663813187520627 9667517997995719781280941)
                  ·
                    refine ⟨3625319249248394917980353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9667517997995719781280941 3625319249248394917980353)
                    ·
                      refine ⟨2718989436936296188485265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3625319249248394917980353 2718989436936296188485265)
                      ·
                        rfl

theorem cell23_5295213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_5295213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295213 prefixEnd_5295213 := by exact prefixLift 5295213
  have htrace : WordTrace (prefixWord ++ tailWord_5295213) baseStart_5295213 baseEnd_5295213 := by
    simpa [prefixWord, tailWord_5295213, baseEnd_5295213] using wordTrace_append hprefix tailTrace_5295213
  have hstable : (prefixWord ++ tailWord_5295213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295213).length < 2 ^ (prefixWord ++ tailWord_5295213).sum := by decide
  have hdescent : baseEnd_5295213 < baseStart_5295213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295266 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 7]
def baseStart_5295266 : Nat := 118140960795 + 5295266 * 2 ^ 59
def prefixEnd_5295266 : Nat := 4983230072969 + 3 ^ 40 * 5295266 * 2
def baseEnd_5295266 : Nat := 302112961267887164569169

theorem tailTrace_5295266 : CollatzResearch.WordTrace tailWord_5295266 prefixEnd_5295266 302112961267887164569169 := by
  unfold tailWord_5295266
  simp only [CollatzResearch.WordTrace]
  refine ⟨48283554408540779069544413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128756145089442077518785101 48283554408540779069544413)
  ·
    refine ⟨18106332903202792151079155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48283554408540779069544413 18106332903202792151079155)
    ·
      refine ⟨27159499354804188226618733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18106332903202792151079155 27159499354804188226618733)
      ·
        refine ⟨10184812258051570584982025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27159499354804188226618733 10184812258051570584982025)
        ·
          refine ⟨7638609193538677938736519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10184812258051570584982025 7638609193538677938736519)
          ·
            refine ⟨11457913790308016908104779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7638609193538677938736519 11457913790308016908104779)
            ·
              refine ⟨17186870685462025362157169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11457913790308016908104779 17186870685462025362157169)
              ·
                refine ⟨12890153014096519021617877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17186870685462025362157169 12890153014096519021617877)
                ·
                  refine ⟨302112961267887164569169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12890153014096519021617877 302112961267887164569169)
                  ·
                    rfl

theorem cell23_5295266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_5295266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295266 prefixEnd_5295266 := by exact prefixLift 5295266
  have htrace : WordTrace (prefixWord ++ tailWord_5295266) baseStart_5295266 baseEnd_5295266 := by
    simpa [prefixWord, tailWord_5295266, baseEnd_5295266] using wordTrace_append hprefix tailTrace_5295266
  have hstable : (prefixWord ++ tailWord_5295266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295266).length < 2 ^ (prefixWord ++ tailWord_5295266).sum := by decide
  have hdescent : baseEnd_5295266 < baseStart_5295266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295279 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 2, 5]
def baseStart_5295279 : Nat := 118140960795 + 5295279 * 2 ^ 59
def prefixEnd_5295279 : Nat := 4983230072969 + 3 ^ 40 * 5295279 * 2
def baseEnd_5295279 : Nat := 906341108886497643419987

theorem tailTrace_5295279 : CollatzResearch.WordTrace tailWord_5295279 prefixEnd_5295279 906341108886497643419987 := by
  unfold tailWord_5295279
  simp only [CollatzResearch.WordTrace]
  refine ⟨193134691783116019498400891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128756461188744012998933927 193134691783116019498400891)
  ·
    refine ⟨289702037674674029247601337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193134691783116019498400891 289702037674674029247601337)
    ·
      refine ⟨217276528256005521935701003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289702037674674029247601337 217276528256005521935701003)
      ·
        refine ⟨325914792384008282903551505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217276528256005521935701003 325914792384008282903551505)
        ·
          refine ⟨244436094288006212177663629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325914792384008282903551505 244436094288006212177663629)
          ·
            refine ⟨91663535358002329566623861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244436094288006212177663629 91663535358002329566623861)
            ·
              refine ⟨8593456439812718396870987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91663535358002329566623861 8593456439812718396870987)
              ·
                refine ⟨12890184659719077595306481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8593456439812718396870987 12890184659719077595306481)
                ·
                  refine ⟨9667638494789308196479861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12890184659719077595306481 9667638494789308196479861)
                  ·
                    refine ⟨906341108886497643419987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9667638494789308196479861 906341108886497643419987)
                    ·
                      rfl

theorem cell23_5295279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 5].length) (baseStart_5295279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295279 prefixEnd_5295279 := by exact prefixLift 5295279
  have htrace : WordTrace (prefixWord ++ tailWord_5295279) baseStart_5295279 baseEnd_5295279 := by
    simpa [prefixWord, tailWord_5295279, baseEnd_5295279] using wordTrace_append hprefix tailTrace_5295279
  have hstable : (prefixWord ++ tailWord_5295279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295279).length < 2 ^ (prefixWord ++ tailWord_5295279).sum := by decide
  have hdescent : baseEnd_5295279 < baseStart_5295279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295319 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 3]
def baseStart_5295319 : Nat := 118140960795 + 5295319 * 2 ^ 59
def prefixEnd_5295319 : Nat := 4983230072969 + 3 ^ 40 * 5295319 * 2
def baseEnd_5295319 : Nat := 2719043865885672773759777

theorem tailTrace_5295319 : CollatzResearch.WordTrace tailWord_5295319 prefixEnd_5295319 2719043865885672773759777 := by
  unfold tailWord_5295319
  simp only [CollatzResearch.WordTrace]
  refine ⟨193136150702971106329857011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128757433801980737553238007 193136150702971106329857011)
  ·
    refine ⟨289704226054456659494785517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193136150702971106329857011 289704226054456659494785517)
    ·
      refine ⟨108639084770421247310544569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289704226054456659494785517 108639084770421247310544569)
      ·
        refine ⟨81479313577815935482908427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108639084770421247310544569 81479313577815935482908427)
        ·
          refine ⟨122218970366723903224362641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81479313577815935482908427 122218970366723903224362641)
          ·
            refine ⟨91664227775042927418271981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122218970366723903224362641 91664227775042927418271981)
            ·
              refine ⟨34374085415641097781851993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91664227775042927418271981 34374085415641097781851993)
              ·
                refine ⟨25780564061730823336388995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34374085415641097781851993 25780564061730823336388995)
                ·
                  refine ⟨38670846092596235004583493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25780564061730823336388995 38670846092596235004583493)
                  ·
                    refine ⟨7250783642361794063359405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38670846092596235004583493 7250783642361794063359405)
                    ·
                      refine ⟨2719043865885672773759777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7250783642361794063359405 2719043865885672773759777)
                      ·
                        rfl

theorem cell23_5295319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_5295319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295319 prefixEnd_5295319 := by exact prefixLift 5295319
  have htrace : WordTrace (prefixWord ++ tailWord_5295319) baseStart_5295319 baseEnd_5295319 := by
    simpa [prefixWord, tailWord_5295319, baseEnd_5295319] using wordTrace_append hprefix tailTrace_5295319
  have hstable : (prefixWord ++ tailWord_5295319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295319).length < 2 ^ (prefixWord ++ tailWord_5295319).sum := by decide
  have hdescent : baseEnd_5295319 < baseStart_5295319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295336 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_5295336 : Nat := 118140960795 + 5295336 * 2 ^ 59
def prefixEnd_5295336 : Nat := 4983230072969 + 3 ^ 40 * 5295336 * 2
def baseEnd_5295336 : Nat := 2719052595056799207247199

theorem tailTrace_5295336 : CollatzResearch.WordTrace tailWord_5295336 prefixEnd_5295336 2719052595056799207247199 := by
  unfold tailWord_5295336
  simp only [CollatzResearch.WordTrace]
  refine ⟨96568385371954759116612931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128757847162606345488817241 96568385371954759116612931)
  ·
    refine ⟨144852578057932138674919397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96568385371954759116612931 144852578057932138674919397)
    ·
      refine ⟨27159858385862276001547387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144852578057932138674919397 27159858385862276001547387)
      ·
        refine ⟨40739787578793414002321081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27159858385862276001547387 40739787578793414002321081)
        ·
          refine ⟨30554840684095060501740811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40739787578793414002321081 30554840684095060501740811)
          ·
            refine ⟨45832261026142590752611217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30554840684095060501740811 45832261026142590752611217)
            ·
              refine ⟨34374195769606943064458413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45832261026142590752611217 34374195769606943064458413)
              ·
                refine ⟨12890323413602603649171905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34374195769606943064458413 12890323413602603649171905)
                ·
                  refine ⟨9667742560201952736878929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12890323413602603649171905 9667742560201952736878929)
                  ·
                    refine ⟨7250806920151464552659197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9667742560201952736878929 7250806920151464552659197)
                    ·
                      refine ⟨2719052595056799207247199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7250806920151464552659197 2719052595056799207247199)
                      ·
                        rfl

theorem cell23_5295336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_5295336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295336 prefixEnd_5295336 := by exact prefixLift 5295336
  have htrace : WordTrace (prefixWord ++ tailWord_5295336) baseStart_5295336 baseEnd_5295336 := by
    simpa [prefixWord, tailWord_5295336, baseEnd_5295336] using wordTrace_append hprefix tailTrace_5295336
  have hstable : (prefixWord ++ tailWord_5295336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295336).length < 2 ^ (prefixWord ++ tailWord_5295336).sum := by decide
  have hdescent : baseEnd_5295336 < baseStart_5295336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295369 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 3, 5]
def baseStart_5295369 : Nat := 118140960795 + 5295369 * 2 ^ 59
def prefixEnd_5295369 : Nat := 4983230072969 + 3 ^ 40 * 5295369 * 2
def baseEnd_5295369 : Nat := 906356513306132526044849

theorem tailTrace_5295369 : CollatzResearch.WordTrace tailWord_5295369 prefixEnd_5295369 906356513306132526044849 := by
  unfold tailWord_5295369
  simp only [CollatzResearch.WordTrace]
  refine ⟨193137974352789964869177161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128758649568526643246118107 193137974352789964869177161)
  ·
    refine ⟨144853480764592473651882871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193137974352789964869177161 144853480764592473651882871)
    ·
      refine ⟨217280221146888710477824307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144853480764592473651882871 217280221146888710477824307)
      ·
        refine ⟨325920331720333065716736461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217280221146888710477824307 325920331720333065716736461)
        ·
          refine ⟨122220124395124899643776173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325920331720333065716736461 122220124395124899643776173)
          ·
            refine ⟨45832546648171837366416065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122220124395124899643776173 45832546648171837366416065)
            ·
              refine ⟨34374409986128878024812049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45832546648171837366416065 34374409986128878024812049)
              ·
                refine ⟨25780807489596658518609037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34374409986128878024812049 25780807489596658518609037)
                ·
                  refine ⟨9667802808598746944478389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25780807489596658518609037 9667802808598746944478389)
                  ·
                    refine ⟨906356513306132526044849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9667802808598746944478389 906356513306132526044849)
                    ·
                      rfl

theorem cell23_5295369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_5295369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295369 prefixEnd_5295369 := by exact prefixLift 5295369
  have htrace : WordTrace (prefixWord ++ tailWord_5295369) baseStart_5295369 baseEnd_5295369 := by
    simpa [prefixWord, tailWord_5295369, baseEnd_5295369] using wordTrace_append hprefix tailTrace_5295369
  have hstable : (prefixWord ++ tailWord_5295369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295369).length < 2 ^ (prefixWord ++ tailWord_5295369).sum := by decide
  have hdescent : baseEnd_5295369 < baseStart_5295369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295386 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 3, 5]
def baseStart_5295386 : Nat := 118140960795 + 5295386 * 2 ^ 59
def prefixEnd_5295386 : Nat := 4983230072969 + 3 ^ 40 * 5295386 * 2
def baseEnd_5295386 : Nat := 906359423029841337207323

theorem tailTrace_5295386 : CollatzResearch.WordTrace tailWord_5295386 prefixEnd_5295386 906359423029841337207323 := by
  unfold tailWord_5295386
  simp only [CollatzResearch.WordTrace]
  refine ⟨48284648598432094193136503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128759062929152251181697341 48284648598432094193136503)
  ·
    refine ⟨72426972897648141289704755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48284648598432094193136503 72426972897648141289704755)
    ·
      refine ⟨108640459346472211934557133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72426972897648141289704755 108640459346472211934557133)
      ·
        refine ⟨40740172254927079475458925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108640459346472211934557133 40740172254927079475458925)
        ·
          refine ⟨15277564595597654803297097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40740172254927079475458925 15277564595597654803297097)
          ·
            refine ⟨11458173446698241102472823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15277564595597654803297097 11458173446698241102472823)
            ·
              refine ⟨17187260170047361653709235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11458173446698241102472823 17187260170047361653709235)
              ·
                refine ⟨25780890255071042480563853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17187260170047361653709235 25780890255071042480563853)
                ·
                  refine ⟨9667833845651640930211445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25780890255071042480563853 9667833845651640930211445)
                  ·
                    refine ⟨906359423029841337207323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9667833845651640930211445 906359423029841337207323)
                    ·
                      rfl

theorem cell23_5295386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_5295386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295386 prefixEnd_5295386 := by exact prefixLift 5295386
  have htrace : WordTrace (prefixWord ++ tailWord_5295386) baseStart_5295386 baseEnd_5295386 := by
    simpa [prefixWord, tailWord_5295386, baseEnd_5295386] using wordTrace_append hprefix tailTrace_5295386
  have hstable : (prefixWord ++ tailWord_5295386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295386).length < 2 ^ (prefixWord ++ tailWord_5295386).sum := by decide
  have hdescent : baseEnd_5295386 < baseStart_5295386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295417 : List Nat := [1, 2, 1, 6, 2, 1, 1, 4, 1, 1, 3]
def baseStart_5295417 : Nat := 118140960795 + 5295417 * 2 ^ 59
def prefixEnd_5295417 : Nat := 4983230072969 + 3 ^ 40 * 5295417 * 2
def baseEnd_5295417 : Nat := 2719094186989813390334327

theorem tailTrace_5295417 : CollatzResearch.WordTrace tailWord_5295417 prefixEnd_5295417 2719094186989813390334327 := by
  unfold tailWord_5295417
  simp only [CollatzResearch.WordTrace]
  refine ⟨193139725056616069066924505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128759816704410712711283003 193139725056616069066924505)
  ·
    refine ⟨144854793792462051800193379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193139725056616069066924505 144854793792462051800193379)
    ·
      refine ⟨217282190688693077700290069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144854793792462051800193379 217282190688693077700290069)
      ·
        refine ⟨10185102688532488017201097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 217282190688693077700290069 10185102688532488017201097)
        ·
          refine ⟨7638827016399366012900823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10185102688532488017201097 7638827016399366012900823)
          ·
            refine ⟨11458240524599049019351235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7638827016399366012900823 11458240524599049019351235)
            ·
              refine ⟨17187360786898573529026853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11458240524599049019351235 17187360786898573529026853)
              ·
                refine ⟨3222630147543482536692535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17187360786898573529026853 3222630147543482536692535)
                ·
                  refine ⟨4833945221315223805038803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3222630147543482536692535 4833945221315223805038803)
                  ·
                    refine ⟨7250917831972835707558205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4833945221315223805038803 7250917831972835707558205)
                    ·
                      refine ⟨2719094186989813390334327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7250917831972835707558205 2719094186989813390334327)
                      ·
                        rfl

theorem cell23_5295417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_5295417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295417 prefixEnd_5295417 := by exact prefixLift 5295417
  have htrace : WordTrace (prefixWord ++ tailWord_5295417) baseStart_5295417 baseEnd_5295417 := by
    simpa [prefixWord, tailWord_5295417, baseEnd_5295417] using wordTrace_append hprefix tailTrace_5295417
  have hstable : (prefixWord ++ tailWord_5295417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295417).length < 2 ^ (prefixWord ++ tailWord_5295417).sum := by decide
  have hdescent : baseEnd_5295417 < baseStart_5295417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295436 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_5295436 : Nat := 118140960795 + 5295436 * 2 ^ 59
def prefixEnd_5295436 : Nat := 4983230072969 + 3 ^ 40 * 5295436 * 2
def baseEnd_5295436 : Nat := 2719103943122248815996739

theorem tailTrace_5295436 : CollatzResearch.WordTrace tailWord_5295436 prefixEnd_5295436 2719103943122248815996739 := by
  unfold tailWord_5295436
  simp only [CollatzResearch.WordTrace]
  refine ⟨96570209021773617655933081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128760278695698156874577441 96570209021773617655933081)
  ·
    refine ⟨72427656766330213241949811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96570209021773617655933081 72427656766330213241949811)
    ·
      refine ⟨108641485149495319862924717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72427656766330213241949811 108641485149495319862924717)
      ·
        refine ⟨40740556931060744948596769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108641485149495319862924717 40740556931060744948596769)
        ·
          refine ⟨30555417698295558711447577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40740556931060744948596769 30555417698295558711447577)
          ·
            refine ⟨22916563273721669033585683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30555417698295558711447577 22916563273721669033585683)
            ·
              refine ⟨34374844910582503550378525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22916563273721669033585683 34374844910582503550378525)
              ·
                refine ⟨12890566841468438831391947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34374844910582503550378525 12890566841468438831391947)
                ·
                  refine ⟨19335850262202658247087921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12890566841468438831391947 19335850262202658247087921)
                  ·
                    refine ⟨14501887696651993685315941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19335850262202658247087921 14501887696651993685315941)
                    ·
                      refine ⟨2719103943122248815996739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14501887696651993685315941 2719103943122248815996739)
                      ·
                        rfl

theorem cell23_5295436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_5295436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295436 prefixEnd_5295436 := by exact prefixLift 5295436
  have htrace : WordTrace (prefixWord ++ tailWord_5295436) baseStart_5295436 baseEnd_5295436 := by
    simpa [prefixWord, tailWord_5295436, baseEnd_5295436] using wordTrace_append hprefix tailTrace_5295436
  have hstable : (prefixWord ++ tailWord_5295436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295436).length < 2 ^ (prefixWord ++ tailWord_5295436).sum := by decide
  have hdescent : baseEnd_5295436 < baseStart_5295436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295460 : List Nat := [2, 3, 1, 1, 3, 2, 4, 1, 1, 2, 3]
def baseStart_5295460 : Nat := 118140960795 + 5295460 * 2 ^ 59
def prefixEnd_5295460 : Nat := 4983230072969 + 3 ^ 40 * 5295460 * 2
def baseEnd_5295460 : Nat := 2719116266657956722096629

theorem tailTrace_5295460 : CollatzResearch.WordTrace tailWord_5295460 prefixEnd_5295460 2719116266657956722096629 := by
  unfold tailWord_5295460
  simp only [CollatzResearch.WordTrace]
  refine ⟨96570646697730143705369917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128760862263640191607159889 96570646697730143705369917)
  ·
    refine ⟨36213992511648803889513719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96570646697730143705369917 36213992511648803889513719)
    ·
      refine ⟨54320988767473205834270579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36213992511648803889513719 54320988767473205834270579)
      ·
        refine ⟨81481483151209808751405869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54320988767473205834270579 81481483151209808751405869)
        ·
          refine ⟨30555556181703678281777201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81481483151209808751405869 30555556181703678281777201)
          ·
            refine ⟨22916667136277758711332901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30555556181703678281777201 22916667136277758711332901)
            ·
              refine ⟨4296875088052079758374919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22916667136277758711332901 4296875088052079758374919)
              ·
                refine ⟨6445312632078119637562379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4296875088052079758374919 6445312632078119637562379)
                ·
                  refine ⟨9667968948117179456343569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6445312632078119637562379 9667968948117179456343569)
                  ·
                    refine ⟨7250976711087884592257677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9667968948117179456343569 7250976711087884592257677)
                    ·
                      refine ⟨2719116266657956722096629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7250976711087884592257677 2719116266657956722096629)
                      ·
                        rfl

theorem cell23_5295460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_5295460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295460 prefixEnd_5295460 := by exact prefixLift 5295460
  have htrace : WordTrace (prefixWord ++ tailWord_5295460) baseStart_5295460 baseEnd_5295460 := by
    simpa [prefixWord, tailWord_5295460, baseEnd_5295460] using wordTrace_append hprefix tailTrace_5295460
  have hstable : (prefixWord ++ tailWord_5295460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295460).length < 2 ^ (prefixWord ++ tailWord_5295460).sum := by decide
  have hdescent : baseEnd_5295460 < baseStart_5295460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295500 : List Nat := [2, 2, 1, 2, 1, 3, 4, 2, 1, 3, 2]
def baseStart_5295500 : Nat := 118140960795 + 5295500 * 2 ^ 59
def prefixEnd_5295500 : Nat := 4983230072969 + 3 ^ 40 * 5295500 * 2
def baseEnd_5295500 : Nat := 2719136805884136565596445

theorem tailTrace_5295500 : CollatzResearch.WordTrace tailWord_5295500 prefixEnd_5295500 2719136805884136565596445 := by
  unfold tailWord_5295500
  simp only [CollatzResearch.WordTrace]
  refine ⟨96571376157657687121097977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128761834876876916161463969 96571376157657687121097977)
  ·
    refine ⟨72428532118243265340823483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96571376157657687121097977 72428532118243265340823483)
    ·
      refine ⟨108642798177364898011235225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72428532118243265340823483 108642798177364898011235225)
      ·
        refine ⟨81482098633023673508426419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108642798177364898011235225 81482098633023673508426419)
        ·
          refine ⟨122223147949535510262639629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81482098633023673508426419 122223147949535510262639629)
          ·
            refine ⟨45833680481075816348489861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122223147949535510262639629 45833680481075816348489861)
            ·
              refine ⟨8593815090201715565341849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45833680481075816348489861 8593815090201715565341849)
              ·
                refine ⟨6445361317651286674006387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8593815090201715565341849 6445361317651286674006387)
                ·
                  refine ⟨9668041976476930011009581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6445361317651286674006387 9668041976476930011009581)
                  ·
                    refine ⟨3625515741178848754128593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9668041976476930011009581 3625515741178848754128593)
                    ·
                      refine ⟨2719136805884136565596445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3625515741178848754128593 2719136805884136565596445)
                      ·
                        rfl

theorem cell23_5295500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_5295500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295500 prefixEnd_5295500 := by exact prefixLift 5295500
  have htrace : WordTrace (prefixWord ++ tailWord_5295500) baseStart_5295500 baseEnd_5295500 := by
    simpa [prefixWord, tailWord_5295500, baseEnd_5295500] using wordTrace_append hprefix tailTrace_5295500
  have hstable : (prefixWord ++ tailWord_5295500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295500).length < 2 ^ (prefixWord ++ tailWord_5295500).sum := by decide
  have hdescent : baseEnd_5295500 < baseStart_5295500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295566 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_5295566 : Nat := 118140960795 + 5295566 * 2 ^ 59
def prefixEnd_5295566 : Nat := 4983230072969 + 3 ^ 40 * 5295566 * 2
def baseEnd_5295566 : Nat := 906390231869111102457047

theorem tailTrace_5295566 : CollatzResearch.WordTrace tailWord_5295566 prefixEnd_5295566 906390231869111102457047 := by
  unfold tailWord_5295566
  simp only [CollatzResearch.WordTrace]
  refine ⟨24143144941634533439262319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128763439688717511676065701 24143144941634533439262319)
  ·
    refine ⟨36214717412451800158893479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24143144941634533439262319 36214717412451800158893479)
    ·
      refine ⟨54322076118677700238340219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36214717412451800158893479 54322076118677700238340219)
      ·
        refine ⟨81483114178016550357510329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54322076118677700238340219 81483114178016550357510329)
        ·
          refine ⟨61112335633512412768132747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81483114178016550357510329 61112335633512412768132747)
          ·
            refine ⟨91668503450268619152199121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61112335633512412768132747 91668503450268619152199121)
            ·
              refine ⟨68751377587701464364149341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91668503450268619152199121 68751377587701464364149341)
              ·
                refine ⟨25781766595388049136556003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68751377587701464364149341 25781766595388049136556003)
                ·
                  refine ⟨38672649893082073704834005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25781766595388049136556003 38672649893082073704834005)
                  ·
                    refine ⟨906390231869111102457047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38672649893082073704834005 906390231869111102457047)
                    ·
                      rfl

theorem cell23_5295566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_5295566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295566 prefixEnd_5295566 := by exact prefixLift 5295566
  have htrace : WordTrace (prefixWord ++ tailWord_5295566) baseStart_5295566 baseEnd_5295566 := by
    simpa [prefixWord, tailWord_5295566, baseEnd_5295566] using wordTrace_append hprefix tailTrace_5295566
  have hstable : (prefixWord ++ tailWord_5295566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295566).length < 2 ^ (prefixWord ++ tailWord_5295566).sum := by decide
  have hdescent : baseEnd_5295566 < baseStart_5295566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295576 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_5295576 : Nat := 118140960795 + 5295576 * 2 ^ 59
def prefixEnd_5295576 : Nat := 4983230072969 + 3 ^ 40 * 5295576 * 2
def baseEnd_5295576 : Nat := 2719175830413878268246095

theorem tailTrace_5295576 : CollatzResearch.WordTrace tailWord_5295576 prefixEnd_5295576 2719175830413878268246095 := by
  unfold tailWord_5295576
  simp only [CollatzResearch.WordTrace]
  refine ⟨96572762131520019610981291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128763682842026692814641721 96572762131520019610981291)
  ·
    refine ⟨144859143197280029416471937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96572762131520019610981291 144859143197280029416471937)
    ·
      refine ⟨108644357397960022062353953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144859143197280029416471937 108644357397960022062353953)
      ·
        refine ⟨81483268048470016546765465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108644357397960022062353953 81483268048470016546765465)
        ·
          refine ⟨61112451036352512410074099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81483268048470016546765465 61112451036352512410074099)
          ·
            refine ⟨91668676554528768615111149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61112451036352512410074099 91668676554528768615111149)
            ·
              refine ⟨34375753707948288230666681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91668676554528768615111149 34375753707948288230666681)
              ·
                refine ⟨25781815280961216173000011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34375753707948288230666681 25781815280961216173000011)
                ·
                  refine ⟨38672722921441824259500017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25781815280961216173000011 38672722921441824259500017)
                  ·
                    refine ⟨29004542191081368194625013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38672722921441824259500017 29004542191081368194625013)
                    ·
                      refine ⟨2719175830413878268246095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29004542191081368194625013 2719175830413878268246095)
                      ·
                        rfl

theorem cell23_5295576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_5295576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295576 prefixEnd_5295576 := by exact prefixLift 5295576
  have htrace : WordTrace (prefixWord ++ tailWord_5295576) baseStart_5295576 baseEnd_5295576 := by
    simpa [prefixWord, tailWord_5295576, baseEnd_5295576] using wordTrace_append hprefix tailTrace_5295576
  have hstable : (prefixWord ++ tailWord_5295576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295576).length < 2 ^ (prefixWord ++ tailWord_5295576).sum := by decide
  have hdescent : baseEnd_5295576 < baseStart_5295576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295587 : List Nat := [1, 1, 1, 6, 2, 3, 2, 2, 5]
def baseStart_5295587 : Nat := 118140960795 + 5295587 * 2 ^ 59
def prefixEnd_5295587 : Nat := 4983230072969 + 3 ^ 40 * 5295587 * 2
def baseEnd_5295587 : Nat := 302131275411230858356505

theorem tailTrace_5295587 : CollatzResearch.WordTrace tailWord_5295587 prefixEnd_5295587 302131275411230858356505 := by
  unfold tailWord_5295587
  simp only [CollatzResearch.WordTrace]
  refine ⟨193145925466000188100613015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128763950310666792067075343 193145925466000188100613015)
  ·
    refine ⟨289718888199000282150919523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193145925466000188100613015 289718888199000282150919523)
    ·
      refine ⟨434578332298500423226379285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289718888199000282150919523 434578332298500423226379285)
      ·
        refine ⟨20370859326492207338736529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 434578332298500423226379285 20370859326492207338736529)
        ·
          refine ⟨15278144494869155504052397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20370859326492207338736529 15278144494869155504052397)
          ·
            refine ⟨5729304185575933314019649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15278144494869155504052397 5729304185575933314019649)
            ·
              refine ⟨4296978139181949985514737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5729304185575933314019649 4296978139181949985514737)
              ·
                refine ⟨3222733604386462489136053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4296978139181949985514737 3222733604386462489136053)
                ·
                  refine ⟨302131275411230858356505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3222733604386462489136053 302131275411230858356505)
                  ·
                    rfl

theorem cell23_5295587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 5].length) (baseStart_5295587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295587 prefixEnd_5295587 := by exact prefixLift 5295587
  have htrace : WordTrace (prefixWord ++ tailWord_5295587) baseStart_5295587 baseEnd_5295587 := by
    simpa [prefixWord, tailWord_5295587, baseEnd_5295587] using wordTrace_append hprefix tailTrace_5295587
  have hstable : (prefixWord ++ tailWord_5295587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295587).length < 2 ^ (prefixWord ++ tailWord_5295587).sum := by decide
  have hdescent : baseEnd_5295587 < baseStart_5295587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295613 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_5295613 : Nat := 118140960795 + 5295613 * 2 ^ 59
def prefixEnd_5295613 : Nat := 4983230072969 + 3 ^ 40 * 5295613 * 2
def baseEnd_5295613 : Nat := 906398276399364874494475

theorem tailTrace_5295613 : CollatzResearch.WordTrace tailWord_5295613 prefixEnd_5295613 906398276399364874494475 := by
  unfold tailWord_5295613
  simp only [CollatzResearch.WordTrace]
  refine ⟨193146873763905994541059493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128764582509270663027372995 193146873763905994541059493)
  ·
    refine ⟨36215038830732373976448655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193146873763905994541059493 36215038830732373976448655)
    ·
      refine ⟨54322558246098560964672983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36215038830732373976448655 54322558246098560964672983)
      ·
        refine ⟨81483837369147841447009475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54322558246098560964672983 81483837369147841447009475)
        ·
          refine ⟨122225756053721762170514213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81483837369147841447009475 122225756053721762170514213)
          ·
            refine ⟨22917329260072830406971415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122225756053721762170514213 22917329260072830406971415)
            ·
              refine ⟨34375993890109245610457123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22917329260072830406971415 34375993890109245610457123)
              ·
                refine ⟨51563990835163868415685685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34375993890109245610457123 51563990835163868415685685)
                ·
                  refine ⟨4834124140796612663970533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51563990835163868415685685 4834124140796612663970533)
                  ·
                    refine ⟨906398276399364874494475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4834124140796612663970533 906398276399364874494475)
                    ·
                      rfl

theorem cell23_5295613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_5295613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295613 prefixEnd_5295613 := by exact prefixLift 5295613
  have htrace : WordTrace (prefixWord ++ tailWord_5295613) baseStart_5295613 baseEnd_5295613 := by
    simpa [prefixWord, tailWord_5295613, baseEnd_5295613] using wordTrace_append hprefix tailTrace_5295613
  have hstable : (prefixWord ++ tailWord_5295613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295613).length < 2 ^ (prefixWord ++ tailWord_5295613).sum := by decide
  have hdescent : baseEnd_5295613 < baseStart_5295613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295617 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 2, 5]
def baseStart_5295617 : Nat := 118140960795 + 5295617 * 2 ^ 59
def prefixEnd_5295617 : Nat := 4983230072969 + 3 ^ 40 * 5295617 * 2
def baseEnd_5295617 : Nat := 906398961040237535944469

theorem tailTrace_5295617 : CollatzResearch.WordTrace tailWord_5295617 prefixEnd_5295617 906398961040237535944469 := by
  unfold tailWord_5295617
  simp only [CollatzResearch.WordTrace]
  refine ⟨193147019655891503224205105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128764679770594335482803403 193147019655891503224205105)
  ·
    refine ⟨144860264741918627418153829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193147019655891503224205105 144860264741918627418153829)
    ·
      refine ⟨27161299639109742640903843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144860264741918627418153829 27161299639109742640903843)
      ·
        refine ⟨40741949458664613961355765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27161299639109742640903843 40741949458664613961355765)
        ·
          refine ⟨3819557761749807558877103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40741949458664613961355765 3819557761749807558877103)
          ·
            refine ⟨5729336642624711338315655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3819557761749807558877103 5729336642624711338315655)
            ·
              refine ⟨8594004963937067007473483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5729336642624711338315655 8594004963937067007473483)
              ·
                refine ⟨12891007445905600511210225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8594004963937067007473483 12891007445905600511210225)
                ·
                  refine ⟨9668255584429200383407669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12891007445905600511210225 9668255584429200383407669)
                  ·
                    refine ⟨906398961040237535944469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9668255584429200383407669 906398961040237535944469)
                    ·
                      rfl

theorem cell23_5295617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_5295617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295617 prefixEnd_5295617 := by exact prefixLift 5295617
  have htrace : WordTrace (prefixWord ++ tailWord_5295617) baseStart_5295617 baseEnd_5295617 := by
    simpa [prefixWord, tailWord_5295617, baseEnd_5295617] using wordTrace_append hprefix tailTrace_5295617
  have hstable : (prefixWord ++ tailWord_5295617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295617).length < 2 ^ (prefixWord ++ tailWord_5295617).sum := by decide
  have hdescent : baseEnd_5295617 < baseStart_5295617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295620 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_5295620 : Nat := 118140960795 + 5295620 * 2 ^ 59
def prefixEnd_5295620 : Nat := 4983230072969 + 3 ^ 40 * 5295620 * 2
def baseEnd_5295620 : Nat := 2719198423562676096095893

theorem tailTrace_5295620 : CollatzResearch.WordTrace tailWord_5295620 prefixEnd_5295620 2719198423562676096095893 := by
  unfold tailWord_5295620
  simp only [CollatzResearch.WordTrace]
  refine ⟨96573564537440317368282157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128764752716587089824376209 96573564537440317368282157)
  ·
    refine ⟨36215086701540119013105809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96573564537440317368282157 36215086701540119013105809)
    ·
      refine ⟨27161315026155089259829357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36215086701540119013105809 27161315026155089259829357)
      ·
        refine ⟨10185493134808158472436009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27161315026155089259829357 10185493134808158472436009)
        ·
          refine ⟨7639119851106118854327007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10185493134808158472436009 7639119851106118854327007)
          ·
            refine ⟨11458679776659178281490511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7639119851106118854327007 11458679776659178281490511)
            ·
              refine ⟨17188019664988767422235767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11458679776659178281490511 17188019664988767422235767)
              ·
                refine ⟨25782029497483151133353651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17188019664988767422235767 25782029497483151133353651)
                ·
                  refine ⟨38673044246224726700030477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25782029497483151133353651 38673044246224726700030477)
                  ·
                    refine ⟨14502391592334272512511429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38673044246224726700030477 14502391592334272512511429)
                    ·
                      refine ⟨2719198423562676096095893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14502391592334272512511429 2719198423562676096095893)
                      ·
                        rfl

theorem cell23_5295620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_5295620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295620 prefixEnd_5295620 := by exact prefixLift 5295620
  have htrace : WordTrace (prefixWord ++ tailWord_5295620) baseStart_5295620 baseEnd_5295620 := by
    simpa [prefixWord, tailWord_5295620, baseEnd_5295620] using wordTrace_append hprefix tailTrace_5295620
  have hstable : (prefixWord ++ tailWord_5295620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295620).length < 2 ^ (prefixWord ++ tailWord_5295620).sum := by decide
  have hdescent : baseEnd_5295620 < baseStart_5295620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295680 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 2, 3, 2]
def baseStart_5295680 : Nat := 118140960795 + 5295680 * 2 ^ 59
def prefixEnd_5295680 : Nat := 4983230072969 + 3 ^ 40 * 5295680 * 2
def baseEnd_5295680 : Nat := 2719229232401945861345617

theorem tailTrace_5295680 : CollatzResearch.WordTrace tailWord_5295680 prefixEnd_5295680 2719229232401945861345617 := by
  unfold tailWord_5295680
  simp only [CollatzResearch.WordTrace]
  refine ⟨96574658727331632491874247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128766211636442176655832329 96574658727331632491874247)
  ·
    refine ⟨144861988090997448737811371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96574658727331632491874247 144861988090997448737811371)
    ·
      refine ⟨217292982136496173106717057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144861988090997448737811371 217292982136496173106717057)
      ·
        refine ⟨162969736602372129830037793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217292982136496173106717057 162969736602372129830037793)
        ·
          refine ⟨122227302451779097372528345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162969736602372129830037793 122227302451779097372528345)
          ·
            refine ⟨91670476838834323029396259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122227302451779097372528345 91670476838834323029396259)
            ·
              refine ⟨137505715258251484544094389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91670476838834323029396259 137505715258251484544094389)
              ·
                refine ⟨12891160805461076676008849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137505715258251484544094389 12891160805461076676008849)
                ·
                  refine ⟨9668370604095807507006637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12891160805461076676008849 9668370604095807507006637)
                  ·
                    refine ⟨3625638976535927815127489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9668370604095807507006637 3625638976535927815127489)
                    ·
                      refine ⟨2719229232401945861345617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3625638976535927815127489 2719229232401945861345617)
                      ·
                        rfl

theorem cell23_5295680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2, 3, 2].length) (baseStart_5295680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295680 prefixEnd_5295680 := by exact prefixLift 5295680
  have htrace : WordTrace (prefixWord ++ tailWord_5295680) baseStart_5295680 baseEnd_5295680 := by
    simpa [prefixWord, tailWord_5295680, baseEnd_5295680] using wordTrace_append hprefix tailTrace_5295680
  have hstable : (prefixWord ++ tailWord_5295680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295680).length < 2 ^ (prefixWord ++ tailWord_5295680).sum := by decide
  have hdescent : baseEnd_5295680 < baseStart_5295680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295713 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_5295713 : Nat := 118140960795 + 5295713 * 2 ^ 59
def prefixEnd_5295713 : Nat := 4983230072969 + 3 ^ 40 * 5295713 * 2
def baseEnd_5295713 : Nat := 2719246177263544232232965

theorem tailTrace_5295713 : CollatzResearch.WordTrace tailWord_5295713 prefixEnd_5295713 2719246177263544232232965 := by
  unfold tailWord_5295713
  simp only [CollatzResearch.WordTrace]
  refine ⟨193150521063543711619699793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128767014042362474413133195 193150521063543711619699793)
  ·
    refine ⟨144862890797657783714774845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193150521063543711619699793 144862890797657783714774845)
    ·
      refine ⟨54323584049121668893040567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144862890797657783714774845 54323584049121668893040567)
      ·
        refine ⟨81485376073682503339560851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54323584049121668893040567 81485376073682503339560851)
        ·
          refine ⟨122228064110523755009341277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81485376073682503339560851 122228064110523755009341277)
          ·
            refine ⟨45835524041446408128502979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122228064110523755009341277 45835524041446408128502979)
            ·
              refine ⟨68753286062169612192754469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45835524041446408128502979 68753286062169612192754469)
              ·
                refine ⟨12891241136656802286141463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68753286062169612192754469 12891241136656802286141463)
                ·
                  refine ⟨19336861704985203429212195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12891241136656802286141463 19336861704985203429212195)
                  ·
                    refine ⟨29005292557477805143818293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19336861704985203429212195 29005292557477805143818293)
                    ·
                      refine ⟨2719246177263544232232965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29005292557477805143818293 2719246177263544232232965)
                      ·
                        rfl

theorem cell23_5295713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_5295713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295713 prefixEnd_5295713 := by exact prefixLift 5295713
  have htrace : WordTrace (prefixWord ++ tailWord_5295713) baseStart_5295713 baseEnd_5295713 := by
    simpa [prefixWord, tailWord_5295713, baseEnd_5295713] using wordTrace_append hprefix tailTrace_5295713
  have hstable : (prefixWord ++ tailWord_5295713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295713).length < 2 ^ (prefixWord ++ tailWord_5295713).sum := by decide
  have hdescent : baseEnd_5295713 < baseStart_5295713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295744 : List Nat := [2, 1, 1, 2, 1, 4, 2, 5, 1, 2, 2]
def baseStart_5295744 : Nat := 118140960795 + 5295744 * 2 ^ 59
def prefixEnd_5295744 : Nat := 4983230072969 + 3 ^ 40 * 5295744 * 2
def baseEnd_5295744 : Nat := 2719262095163833610945323

theorem tailTrace_5295744 : CollatzResearch.WordTrace tailWord_5295744 prefixEnd_5295744 2719262095163833610945323 := by
  unfold tailWord_5295744
  simp only [CollatzResearch.WordTrace]
  refine ⟨96575825863215701957039143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128767767817620935942718857 96575825863215701957039143)
  ·
    refine ⟨144863738794823552935558715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96575825863215701957039143 144863738794823552935558715)
    ·
      refine ⟨217295608192235329403338073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144863738794823552935558715 217295608192235329403338073)
      ·
        refine ⟨162971706144176497052503555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217295608192235329403338073 162971706144176497052503555)
        ·
          refine ⟨244457559216264745578755333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162971706144176497052503555 244457559216264745578755333)
          ·
            refine ⟨45835792353049639796016625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 244457559216264745578755333 45835792353049639796016625)
            ·
              refine ⟨34376844264787229847012469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45835792353049639796016625 34376844264787229847012469)
              ·
                refine ⟨3222829149823802798157419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34376844264787229847012469 3222829149823802798157419)
                ·
                  refine ⟨4834243724735704197236129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3222829149823802798157419 4834243724735704197236129)
                  ·
                    refine ⟨3625682793551778147927097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4834243724735704197236129 3625682793551778147927097)
                    ·
                      refine ⟨2719262095163833610945323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3625682793551778147927097 2719262095163833610945323)
                      ·
                        rfl

theorem cell23_5295744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 1, 2, 2].length) (baseStart_5295744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295744 prefixEnd_5295744 := by exact prefixLift 5295744
  have htrace : WordTrace (prefixWord ++ tailWord_5295744) baseStart_5295744 baseEnd_5295744 := by
    simpa [prefixWord, tailWord_5295744, baseEnd_5295744] using wordTrace_append hprefix tailTrace_5295744
  have hstable : (prefixWord ++ tailWord_5295744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295744).length < 2 ^ (prefixWord ++ tailWord_5295744).sum := by decide
  have hdescent : baseEnd_5295744 < baseStart_5295744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295760 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 4, 1, 3]
def baseStart_5295760 : Nat := 118140960795 + 5295760 * 2 ^ 59
def prefixEnd_5295760 : Nat := 4983230072969 + 3 ^ 40 * 5295760 * 2
def baseEnd_5295760 : Nat := 2719270310854305548345249

theorem tailTrace_5295760 : CollatzResearch.WordTrace tailWord_5295760 prefixEnd_5295760 2719270310854305548345249 := by
  unfold tailWord_5295760
  simp only [CollatzResearch.WordTrace]
  refine ⟨96576117647186719323330367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128768156862915625764440489 96576117647186719323330367)
  ·
    refine ⟨144864176470780078984995551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96576117647186719323330367 144864176470780078984995551)
    ·
      refine ⟨217296264706170118477493327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144864176470780078984995551 217296264706170118477493327)
      ·
        refine ⟨325944397059255177716239991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217296264706170118477493327 325944397059255177716239991)
        ·
          refine ⟨488916595588882766574359987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325944397059255177716239991 488916595588882766574359987)
          ·
            refine ⟨733374893383324149861539981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488916595588882766574359987 733374893383324149861539981)
            ·
              refine ⟨275015585018746556198077493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 733374893383324149861539981 275015585018746556198077493)
              ·
                refine ⟨25782711095507489643569765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275015585018746556198077493 25782711095507489643569765)
                ·
                  refine ⟨4834258330407654308169331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25782711095507489643569765 4834258330407654308169331)
                  ·
                    refine ⟨7251387495611481462253997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4834258330407654308169331 7251387495611481462253997)
                    ·
                      refine ⟨2719270310854305548345249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7251387495611481462253997 2719270310854305548345249)
                      ·
                        rfl

theorem cell23_5295760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 4, 1, 3].length) (baseStart_5295760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295760 prefixEnd_5295760 := by exact prefixLift 5295760
  have htrace : WordTrace (prefixWord ++ tailWord_5295760) baseStart_5295760 baseEnd_5295760 := by
    simpa [prefixWord, tailWord_5295760, baseEnd_5295760] using wordTrace_append hprefix tailTrace_5295760
  have hstable : (prefixWord ++ tailWord_5295760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295760).length < 2 ^ (prefixWord ++ tailWord_5295760).sum := by decide
  have hdescent : baseEnd_5295760 < baseStart_5295760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295773 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_5295773 : Nat := 118140960795 + 5295773 * 2 ^ 59
def prefixEnd_5295773 : Nat := 4983230072969 + 3 ^ 40 * 5295773 * 2
def baseEnd_5295773 : Nat := 2719276986102813997482689

theorem tailTrace_5295773 : CollatzResearch.WordTrace tailWord_5295773 prefixEnd_5295773 2719276986102813997482689 := by
  unfold tailWord_5295773
  simp only [CollatzResearch.WordTrace]
  refine ⟨193152709443326341866883973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128768472962217561244589315 193152709443326341866883973)
  ·
    refine ⟨36216133020623689100040745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193152709443326341866883973 36216133020623689100040745)
    ·
      refine ⟨27162099765467766825030559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36216133020623689100040745 27162099765467766825030559)
      ·
        refine ⟨40743149648201650237545839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27162099765467766825030559 40743149648201650237545839)
        ·
          refine ⟨61114724472302475356318759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40743149648201650237545839 61114724472302475356318759)
          ·
            refine ⟨91672086708453713034478139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61114724472302475356318759 91672086708453713034478139)
            ·
              refine ⟨137508130062680569551717209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91672086708453713034478139 137508130062680569551717209)
              ·
                refine ⟨103131097547010427163787907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137508130062680569551717209 103131097547010427163787907)
                ·
                  refine ⟨154696646320515640745681861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103131097547010427163787907 154696646320515640745681861)
                  ·
                    refine ⟨29005621185096682639815349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154696646320515640745681861 29005621185096682639815349)
                    ·
                      refine ⟨2719276986102813997482689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29005621185096682639815349 2719276986102813997482689)
                      ·
                        rfl

theorem cell23_5295773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_5295773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295773 prefixEnd_5295773 := by exact prefixLift 5295773
  have htrace : WordTrace (prefixWord ++ tailWord_5295773) baseStart_5295773 baseEnd_5295773 := by
    simpa [prefixWord, tailWord_5295773, baseEnd_5295773] using wordTrace_append hprefix tailTrace_5295773
  have hstable : (prefixWord ++ tailWord_5295773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295773).length < 2 ^ (prefixWord ++ tailWord_5295773).sum := by decide
  have hdescent : baseEnd_5295773 < baseStart_5295773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295777 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_5295777 : Nat := 118140960795 + 5295777 * 2 ^ 59
def prefixEnd_5295777 : Nat := 4983230072969 + 3 ^ 40 * 5295777 * 2
def baseEnd_5295777 : Nat := 2719279040025431981832671

theorem tailTrace_5295777 : CollatzResearch.WordTrace tailWord_5295777 prefixEnd_5295777 2719279040025431981832671 := by
  unfold tailWord_5295777
  simp only [CollatzResearch.WordTrace]
  refine ⟨193152855335311850550029585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128768570223541233700019723 193152855335311850550029585)
  ·
    refine ⟨144864641501483887912522189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193152855335311850550029585 144864641501483887912522189)
    ·
      refine ⟨54324240563056457967195821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144864641501483887912522189 54324240563056457967195821)
      ·
        refine ⟨20371590211146171737698433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54324240563056457967195821 20371590211146171737698433)
        ·
          refine ⟨15278692658359628803273825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20371590211146171737698433 15278692658359628803273825)
          ·
            refine ⟨11459019493769721602455369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15278692658359628803273825 11459019493769721602455369)
            ·
              refine ⟨8594264620327291201841527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11459019493769721602455369 8594264620327291201841527)
              ·
                refine ⟨12891396930490936802762291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8594264620327291201841527 12891396930490936802762291)
                ·
                  refine ⟨19337095395736405204143437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12891396930490936802762291 19337095395736405204143437)
                  ·
                    refine ⟨7251410773401151951553789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19337095395736405204143437 7251410773401151951553789)
                    ·
                      refine ⟨2719279040025431981832671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7251410773401151951553789 2719279040025431981832671)
                      ·
                        rfl

theorem cell23_5295777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_5295777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295777 prefixEnd_5295777 := by exact prefixLift 5295777
  have htrace : WordTrace (prefixWord ++ tailWord_5295777) baseStart_5295777 baseEnd_5295777 := by
    simpa [prefixWord, tailWord_5295777, baseEnd_5295777] using wordTrace_append hprefix tailTrace_5295777
  have hstable : (prefixWord ++ tailWord_5295777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295777).length < 2 ^ (prefixWord ++ tailWord_5295777).sum := by decide
  have hdescent : baseEnd_5295777 < baseStart_5295777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295798 : List Nat := [5, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_5295798 : Nat := 118140960795 + 5295798 * 2 ^ 59
def prefixEnd_5295798 : Nat := 4983230072969 + 3 ^ 40 * 5295798 * 2
def baseEnd_5295798 : Nat := 2719289823119176399670075

theorem tailTrace_5295798 : CollatzResearch.WordTrace tailWord_5295798 prefixEnd_5295798 2719289823119176399670075 := by
  unfold tailWord_5295798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12072101329264735696034003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128769080845490514091029365 12072101329264735696034003)
  ·
    refine ⟨18108151993897103544051005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12072101329264735696034003 18108151993897103544051005)
    ·
      refine ⟨6790556997711413829019127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18108151993897103544051005 6790556997711413829019127)
      ·
        refine ⟨10185835496567120743528691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6790556997711413829019127 10185835496567120743528691)
        ·
          refine ⟨15278753244850681115293037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10185835496567120743528691 15278753244850681115293037)
          ·
            refine ⟨5729532466819005418234889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15278753244850681115293037 5729532466819005418234889)
            ·
              refine ⟨4297149350114254063676167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5729532466819005418234889 4297149350114254063676167)
              ·
                refine ⟨6445724025171381095514251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4297149350114254063676167 6445724025171381095514251)
                ·
                  refine ⟨9668586037757071643271377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6445724025171381095514251 9668586037757071643271377)
                  ·
                    refine ⟨7251439528317803732453533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9668586037757071643271377 7251439528317803732453533)
                    ·
                      refine ⟨2719289823119176399670075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7251439528317803732453533 2719289823119176399670075)
                      ·
                        rfl

theorem cell23_5295798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_5295798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295798 prefixEnd_5295798 := by exact prefixLift 5295798
  have htrace : WordTrace (prefixWord ++ tailWord_5295798) baseStart_5295798 baseEnd_5295798 := by
    simpa [prefixWord, tailWord_5295798, baseEnd_5295798] using wordTrace_append hprefix tailTrace_5295798
  have hstable : (prefixWord ++ tailWord_5295798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295798).length < 2 ^ (prefixWord ++ tailWord_5295798).sum := by decide
  have hdescent : baseEnd_5295798 < baseStart_5295798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295803 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 5]
def baseStart_5295803 : Nat := 118140960795 + 5295803 * 2 ^ 59
def prefixEnd_5295803 : Nat := 4983230072969 + 3 ^ 40 * 5295803 * 2
def baseEnd_5295803 : Nat := 2719292390522448880107551

theorem tailTrace_5295803 : CollatzResearch.WordTrace tailWord_5295803 prefixEnd_5295803 2719292390522448880107551 := by
  unfold tailWord_5295803
  simp only [CollatzResearch.WordTrace]
  refine ⟨193153803633217656990476063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128769202422145104660317375 193153803633217656990476063)
  ·
    refine ⟨289730705449826485485714095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193153803633217656990476063 289730705449826485485714095)
    ·
      refine ⟨434596058174739728228571143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289730705449826485485714095 434596058174739728228571143)
      ·
        refine ⟨651894087262109592342856715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434596058174739728228571143 651894087262109592342856715)
        ·
          refine ⟨977841130893164388514285073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651894087262109592342856715 977841130893164388514285073)
          ·
            refine ⟨733380848169873291385713805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977841130893164388514285073 733380848169873291385713805)
            ·
              refine ⟨275017818063702484269642677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 733380848169873291385713805 275017818063702484269642677)
              ·
                refine ⟨25782920443472107900279001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275017818063702484269642677 25782920443472107900279001)
                ·
                  refine ⟨19337190332604080925209251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25782920443472107900279001 19337190332604080925209251)
                  ·
                    refine ⟨29005785498906121387813877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19337190332604080925209251 29005785498906121387813877)
                    ·
                      refine ⟨2719292390522448880107551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29005785498906121387813877 2719292390522448880107551)
                      ·
                        rfl

theorem cell23_5295803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 5].length) (baseStart_5295803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295803 prefixEnd_5295803 := by exact prefixLift 5295803
  have htrace : WordTrace (prefixWord ++ tailWord_5295803) baseStart_5295803 baseEnd_5295803 := by
    simpa [prefixWord, tailWord_5295803, baseEnd_5295803] using wordTrace_append hprefix tailTrace_5295803
  have hstable : (prefixWord ++ tailWord_5295803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295803).length < 2 ^ (prefixWord ++ tailWord_5295803).sum := by decide
  have hdescent : baseEnd_5295803 < baseStart_5295803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295804 : List Nat := [2, 2, 2, 3, 1, 3, 1, 3, 1, 3, 2]
def baseStart_5295804 : Nat := 118140960795 + 5295804 * 2 ^ 59
def prefixEnd_5295804 : Nat := 4983230072969 + 3 ^ 40 * 5295804 * 2
def baseEnd_5295804 : Nat := 2719292904003103376195047

theorem tailTrace_5295804 : CollatzResearch.WordTrace tailWord_5295804 prefixEnd_5295804 2719292904003103376195047 := by
  unfold tailWord_5295804
  simp only [CollatzResearch.WordTrace]
  refine ⟨96576920053107017080631233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128769226737476022774174977 96576920053107017080631233)
  ·
    refine ⟨72432690039830262810473425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96576920053107017080631233 72432690039830262810473425)
    ·
      refine ⟨54324517529872697107855069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72432690039830262810473425 54324517529872697107855069)
      ·
        refine ⟨20371694073702261415445651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54324517529872697107855069 20371694073702261415445651)
        ·
          refine ⟨30557541110553392123168477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20371694073702261415445651 30557541110553392123168477)
          ·
            refine ⟨11459077916457522046188179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30557541110553392123168477 11459077916457522046188179)
            ·
              refine ⟨17188616874686283069282269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11459077916457522046188179 17188616874686283069282269)
              ·
                refine ⟨6445731328007356150980851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17188616874686283069282269 6445731328007356150980851)
                ·
                  refine ⟨9668596992011034226471277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6445731328007356150980851 9668596992011034226471277)
                  ·
                    refine ⟨3625723872004137834926729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9668596992011034226471277 3625723872004137834926729)
                    ·
                      refine ⟨2719292904003103376195047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3625723872004137834926729 2719292904003103376195047)
                      ·
                        rfl

theorem cell23_5295804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_5295804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295804 prefixEnd_5295804 := by exact prefixLift 5295804
  have htrace : WordTrace (prefixWord ++ tailWord_5295804) baseStart_5295804 baseEnd_5295804 := by
    simpa [prefixWord, tailWord_5295804, baseEnd_5295804] using wordTrace_append hprefix tailTrace_5295804
  have hstable : (prefixWord ++ tailWord_5295804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295804).length < 2 ^ (prefixWord ++ tailWord_5295804).sum := by decide
  have hdescent : baseEnd_5295804 < baseStart_5295804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295813 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_5295813 : Nat := 118140960795 + 5295813 * 2 ^ 59
def prefixEnd_5295813 : Nat := 4983230072969 + 3 ^ 40 * 5295813 * 2
def baseEnd_5295813 : Nat := 2719297525328993840982505

theorem tailTrace_5295813 : CollatzResearch.WordTrace tailWord_5295813 prefixEnd_5295813 2719297525328993840982505 := by
  unfold tailWord_5295813
  simp only [CollatzResearch.WordTrace]
  refine ⟨193154168363181428698340093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128769445575454285798893395 193154168363181428698340093)
  ·
    refine ⟨72432813136193035761877535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193154168363181428698340093 72432813136193035761877535)
    ·
      refine ⟨108649219704289553642816303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72432813136193035761877535 108649219704289553642816303)
      ·
        refine ⟨162973829556434330464224455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108649219704289553642816303 162973829556434330464224455)
        ·
          refine ⟨244460744334651495696336683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162973829556434330464224455 244460744334651495696336683)
          ·
            refine ⟨366691116501977243544505025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244460744334651495696336683 366691116501977243544505025)
            ·
              refine ⟨275018337376482932658378769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366691116501977243544505025 275018337376482932658378769)
              ·
                refine ⟨206263753032362199493784077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275018337376482932658378769 206263753032362199493784077)
                ·
                  refine ⟨77348907387135824810169029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206263753032362199493784077 77348907387135824810169029)
                  ·
                    refine ⟨14502920135087967151906693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77348907387135824810169029 14502920135087967151906693)
                    ·
                      refine ⟨2719297525328993840982505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14502920135087967151906693 2719297525328993840982505)
                      ·
                        rfl

theorem cell23_5295813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_5295813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295813 prefixEnd_5295813 := by exact prefixLift 5295813
  have htrace : WordTrace (prefixWord ++ tailWord_5295813) baseStart_5295813 baseEnd_5295813 := by
    simpa [prefixWord, tailWord_5295813, baseEnd_5295813] using wordTrace_append hprefix tailTrace_5295813
  have hstable : (prefixWord ++ tailWord_5295813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295813).length < 2 ^ (prefixWord ++ tailWord_5295813).sum := by decide
  have hdescent : baseEnd_5295813 < baseStart_5295813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295834 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2]
def baseStart_5295834 : Nat := 118140960795 + 5295834 * 2 ^ 59
def prefixEnd_5295834 : Nat := 4983230072969 + 3 ^ 40 * 5295834 * 2
def baseEnd_5295834 : Nat := 2719308308422738258819909

theorem tailTrace_5295834 : CollatzResearch.WordTrace tailWord_5295834 prefixEnd_5295834 2719308308422738258819909 := by
  unfold tailWord_5295834
  simp only [CollatzResearch.WordTrace]
  refine ⟨48288733574026337321213639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128769956197403566189903037 48288733574026337321213639)
  ·
    refine ⟨72433100361039505981820459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48288733574026337321213639 72433100361039505981820459)
    ·
      refine ⟨108649650541559258972730689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72433100361039505981820459 108649650541559258972730689)
      ·
        refine ⟨81487237906169444229548017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108649650541559258972730689 81487237906169444229548017)
        ·
          refine ⟨61115428429627083172161013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81487237906169444229548017 61115428429627083172161013)
          ·
            refine ⟨5729571415277539047390095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61115428429627083172161013 5729571415277539047390095)
            ·
              refine ⟨8594357122916308571085143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5729571415277539047390095 8594357122916308571085143)
              ·
                refine ⟨12891535684374462856627715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8594357122916308571085143 12891535684374462856627715)
                ·
                  refine ⟨19337303526561694284941573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12891535684374462856627715 19337303526561694284941573)
                  ·
                    refine ⟨3625744411230317678426545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19337303526561694284941573 3625744411230317678426545)
                    ·
                      refine ⟨2719308308422738258819909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3625744411230317678426545 2719308308422738258819909)
                      ·
                        rfl

theorem cell23_5295834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_5295834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295834 prefixEnd_5295834 := by exact prefixLift 5295834
  have htrace : WordTrace (prefixWord ++ tailWord_5295834) baseStart_5295834 baseEnd_5295834 := by
    simpa [prefixWord, tailWord_5295834, baseEnd_5295834] using wordTrace_append hprefix tailTrace_5295834
  have hstable : (prefixWord ++ tailWord_5295834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295834).length < 2 ^ (prefixWord ++ tailWord_5295834).sum := by decide
  have hdescent : baseEnd_5295834 < baseStart_5295834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295850 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_5295850 : Nat := 118140960795 + 5295850 * 2 ^ 59
def prefixEnd_5295850 : Nat := 4983230072969 + 3 ^ 40 * 5295850 * 2
def baseEnd_5295850 : Nat := 2719316524113210196219835

theorem tailTrace_5295850 : CollatzResearch.WordTrace tailWord_5295850 prefixEnd_5295850 2719316524113210196219835 := by
  unfold tailWord_5295850
  simp only [CollatzResearch.WordTrace]
  refine ⟨48288879466011846004359251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128770345242698256011624669 48288879466011846004359251)
  ·
    refine ⟨72433319199017769006538877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48288879466011846004359251 72433319199017769006538877)
    ·
      refine ⟨27162494699631663377452079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72433319199017769006538877 27162494699631663377452079)
      ·
        refine ⟨40743742049447495066178119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27162494699631663377452079 40743742049447495066178119)
        ·
          refine ⟨61115613074171242599267179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40743742049447495066178119 61115613074171242599267179)
          ·
            refine ⟨91673419611256863898900769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61115613074171242599267179 91673419611256863898900769)
            ·
              refine ⟨68755064708442647924175577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91673419611256863898900769 68755064708442647924175577)
              ·
                refine ⟨51566298531331985943131683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68755064708442647924175577 51566298531331985943131683)
                ·
                  refine ⟨77349447796997978914697525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51566298531331985943131683 77349447796997978914697525)
                  ·
                    refine ⟨7251510730968560523252893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77349447796997978914697525 7251510730968560523252893)
                    ·
                      refine ⟨2719316524113210196219835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7251510730968560523252893 2719316524113210196219835)
                      ·
                        rfl

theorem cell23_5295850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_5295850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295850 prefixEnd_5295850 := by exact prefixLift 5295850
  have htrace : WordTrace (prefixWord ++ tailWord_5295850) baseStart_5295850 baseEnd_5295850 := by
    simpa [prefixWord, tailWord_5295850, baseEnd_5295850] using wordTrace_append hprefix tailTrace_5295850
  have hstable : (prefixWord ++ tailWord_5295850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295850).length < 2 ^ (prefixWord ++ tailWord_5295850).sum := by decide
  have hdescent : baseEnd_5295850 < baseStart_5295850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295857 : List Nat := [1, 2, 2, 2, 2, 3, 3, 3, 5]
def baseStart_5295857 : Nat := 118140960795 + 5295857 * 2 ^ 59
def prefixEnd_5295857 : Nat := 4983230072969 + 3 ^ 40 * 5295857 * 2
def baseEnd_5295857 : Nat := 302146679830865740981367

theorem tailTrace_5295857 : CollatzResearch.WordTrace tailWord_5295857 prefixEnd_5295857 302146679830865740981367 := by
  unfold tailWord_5295857
  simp only [CollatzResearch.WordTrace]
  refine ⟨193155773175022024212941825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128770515450014682808627883 193155773175022024212941825)
  ·
    refine ⟨144866829881266518159706369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193155773175022024212941825 144866829881266518159706369)
    ·
      refine ⟨108650122410949888619779777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144866829881266518159706369 108650122410949888619779777)
      ·
        refine ⟨81487591808212416464834833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108650122410949888619779777 81487591808212416464834833)
        ·
          refine ⟨61115693856159312348626125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81487591808212416464834833 61115693856159312348626125)
          ·
            refine ⟨22918385196059742130734797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61115693856159312348626125 22918385196059742130734797)
            ·
              refine ⟨8594394448522403299025549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22918385196059742130734797 8594394448522403299025549)
              ·
                refine ⟨3222897918195901237134581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8594394448522403299025549 3222897918195901237134581)
                ·
                  refine ⟨302146679830865740981367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3222897918195901237134581 302146679830865740981367)
                  ·
                    rfl

theorem cell23_5295857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 5].length) (baseStart_5295857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295857 prefixEnd_5295857 := by exact prefixLift 5295857
  have htrace : WordTrace (prefixWord ++ tailWord_5295857) baseStart_5295857 baseEnd_5295857 := by
    simpa [prefixWord, tailWord_5295857, baseEnd_5295857] using wordTrace_append hprefix tailTrace_5295857
  have hstable : (prefixWord ++ tailWord_5295857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295857).length < 2 ^ (prefixWord ++ tailWord_5295857).sum := by decide
  have hdescent : baseEnd_5295857 < baseStart_5295857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295880 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_5295880 : Nat := 118140960795 + 5295880 * 2 ^ 59
def prefixEnd_5295880 : Nat := 4983230072969 + 3 ^ 40 * 5295880 * 2
def baseEnd_5295880 : Nat := 2719331928532845078844697

theorem tailTrace_5295880 : CollatzResearch.WordTrace tailWord_5295880 prefixEnd_5295880 2719331928532845078844697 := by
  unfold tailWord_5295880
  simp only [CollatzResearch.WordTrace]
  refine ⟨96578306026969349570514547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128771074702625799427352729 96578306026969349570514547)
  ·
    refine ⟨144867459040454024355771821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96578306026969349570514547 144867459040454024355771821)
    ·
      refine ⟨54325297140170259133414433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144867459040454024355771821 54325297140170259133414433)
      ·
        refine ⟨40743972855127694350060825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54325297140170259133414433 40743972855127694350060825)
        ·
          refine ⟨30557979641345770762545619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40743972855127694350060825 30557979641345770762545619)
          ·
            refine ⟨45836969462018656143818429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30557979641345770762545619 45836969462018656143818429)
            ·
              refine ⟨17188863548256996053931911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45836969462018656143818429 17188863548256996053931911)
              ·
                refine ⟨25783295322385494080897867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17188863548256996053931911 25783295322385494080897867)
                ·
                  refine ⟨38674942983578241121346801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25783295322385494080897867 38674942983578241121346801)
                  ·
                    refine ⟨29006207237683680841010101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38674942983578241121346801 29006207237683680841010101)
                    ·
                      refine ⟨2719331928532845078844697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29006207237683680841010101 2719331928532845078844697)
                      ·
                        rfl

theorem cell23_5295880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_5295880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295880 prefixEnd_5295880 := by exact prefixLift 5295880
  have htrace : WordTrace (prefixWord ++ tailWord_5295880) baseStart_5295880 baseEnd_5295880 := by
    simpa [prefixWord, tailWord_5295880, baseEnd_5295880] using wordTrace_append hprefix tailTrace_5295880
  have hstable : (prefixWord ++ tailWord_5295880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295880).length < 2 ^ (prefixWord ++ tailWord_5295880).sum := by decide
  have hdescent : baseEnd_5295880 < baseStart_5295880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5295924 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_5295924 : Nat := 118140960795 + 5295924 * 2 ^ 59
def prefixEnd_5295924 : Nat := 4983230072969 + 3 ^ 40 * 5295924 * 2
def baseEnd_5295924 : Nat := 2719354521681642906694495

theorem tailTrace_5295924 : CollatzResearch.WordTrace tailWord_5295924 prefixEnd_5295924 2719354521681642906694495 := by
  unfold tailWord_5295924
  simp only [CollatzResearch.WordTrace]
  refine ⟨96579108432889647327815413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128772144577186196437087217 96579108432889647327815413)
  ·
    refine ⟨9054291415583404436982695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96579108432889647327815413 9054291415583404436982695)
    ·
      refine ⟨13581437123375106655474043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9054291415583404436982695 13581437123375106655474043)
      ·
        refine ⟨20372155685062659983211065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13581437123375106655474043 20372155685062659983211065)
        ·
          refine ⟨15279116763796994987408299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20372155685062659983211065 15279116763796994987408299)
          ·
            refine ⟨22918675145695492481112449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15279116763796994987408299 22918675145695492481112449)
            ·
              refine ⟨17189006359271619360834337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22918675145695492481112449 17189006359271619360834337)
              ·
                refine ⟨12891754769453714520625753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17189006359271619360834337 12891754769453714520625753)
                ·
                  refine ⟨9668816077090285890469315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12891754769453714520625753 9668816077090285890469315)
                  ·
                    refine ⟨14503224115635428835703973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9668816077090285890469315 14503224115635428835703973)
                    ·
                      refine ⟨2719354521681642906694495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14503224115635428835703973 2719354521681642906694495)
                      ·
                        rfl

theorem cell23_5295924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_5295924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5295924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5295924 prefixEnd_5295924 := by exact prefixLift 5295924
  have htrace : WordTrace (prefixWord ++ tailWord_5295924) baseStart_5295924 baseEnd_5295924 := by
    simpa [prefixWord, tailWord_5295924, baseEnd_5295924] using wordTrace_append hprefix tailTrace_5295924
  have hstable : (prefixWord ++ tailWord_5295924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5295924).length < 2 ^ (prefixWord ++ tailWord_5295924).sum := by decide
  have hdescent : baseEnd_5295924 < baseStart_5295924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5295924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296017 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 3]
def baseStart_5296017 : Nat := 118140960795 + 5296017 * 2 ^ 59
def prefixEnd_5296017 : Nat := 4983230072969 + 3 ^ 40 * 5296017 * 2
def baseEnd_5296017 : Nat := 2719402275382511042831567

theorem tailTrace_5296017 : CollatzResearch.WordTrace tailWord_5296017 prefixEnd_5296017 2719402275382511042831567 := by
  unfold tailWord_5296017
  simp only [CollatzResearch.WordTrace]
  refine ⟨193161608854442371538766305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128774405902961581025844203 193161608854442371538766305)
  ·
    refine ⟨144871206640831778654074729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193161608854442371538766305 144871206640831778654074729)
    ·
      refine ⟨108653404980623833990556047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144871206640831778654074729 108653404980623833990556047)
      ·
        refine ⟨162980107470935750985834071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108653404980623833990556047 162980107470935750985834071)
        ·
          refine ⟨244470161206403626478751107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162980107470935750985834071 244470161206403626478751107)
          ·
            refine ⟨366705241809605439718126661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244470161206403626478751107 366705241809605439718126661)
            ·
              refine ⟨68757232839301019947148749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 366705241809605439718126661 68757232839301019947148749)
              ·
                refine ⟨25783962314737882480180781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68757232839301019947148749 25783962314737882480180781)
                ·
                  refine ⟨9668985868026705930067793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25783962314737882480180781 9668985868026705930067793)
                  ·
                    refine ⟨7251739401020029447550845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9668985868026705930067793 7251739401020029447550845)
                    ·
                      refine ⟨2719402275382511042831567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7251739401020029447550845 2719402275382511042831567)
                      ·
                        rfl

theorem cell23_5296017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_5296017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296017 prefixEnd_5296017 := by exact prefixLift 5296017
  have htrace : WordTrace (prefixWord ++ tailWord_5296017) baseStart_5296017 baseEnd_5296017 := by
    simpa [prefixWord, tailWord_5296017, baseEnd_5296017] using wordTrace_append hprefix tailTrace_5296017
  have hstable : (prefixWord ++ tailWord_5296017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296017).length < 2 ^ (prefixWord ++ tailWord_5296017).sum := by decide
  have hdescent : baseEnd_5296017 < baseStart_5296017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296104 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_5296104 : Nat := 118140960795 + 5296104 * 2 ^ 59
def prefixEnd_5296104 : Nat := 4983230072969 + 3 ^ 40 * 5296104 * 2
def baseEnd_5296104 : Nat := 2719446948199452202443667

theorem tailTrace_5296104 : CollatzResearch.WordTrace tailWord_5296104 prefixEnd_5296104 2719446948199452202443667 := by
  unfold tailWord_5296104
  simp only [CollatzResearch.WordTrace]
  refine ⟨96582391002563592698591683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128776521336751456931455577 96582391002563592698591683)
  ·
    refine ⟨144873586503845389047887525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96582391002563592698591683 144873586503845389047887525)
    ·
      refine ⟨27163797469471010446478911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144873586503845389047887525 27163797469471010446478911)
      ·
        refine ⟨40745696204206515669718367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27163797469471010446478911 40745696204206515669718367)
        ·
          refine ⟨61118544306309773504577551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40745696204206515669718367 61118544306309773504577551)
          ·
            refine ⟨91677816459464660256866327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61118544306309773504577551 91677816459464660256866327)
            ·
              refine ⟨137516724689196990385299491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91677816459464660256866327 137516724689196990385299491)
              ·
                refine ⟨206275087033795485577949237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137516724689196990385299491 206275087033795485577949237)
                ·
                  refine ⟨19338289409418326772932741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206275087033795485577949237 19338289409418326772932741)
                  ·
                    refine ⟨3625929264265936269924889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19338289409418326772932741 3625929264265936269924889)
                    ·
                      refine ⟨2719446948199452202443667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3625929264265936269924889 2719446948199452202443667)
                      ·
                        rfl

theorem cell23_5296104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_5296104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296104 prefixEnd_5296104 := by exact prefixLift 5296104
  have htrace : WordTrace (prefixWord ++ tailWord_5296104) baseStart_5296104 baseEnd_5296104 := by
    simpa [prefixWord, tailWord_5296104, baseEnd_5296104] using wordTrace_append hprefix tailTrace_5296104
  have hstable : (prefixWord ++ tailWord_5296104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296104).length < 2 ^ (prefixWord ++ tailWord_5296104).sum := by decide
  have hdescent : baseEnd_5296104 < baseStart_5296104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296121 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 1, 4, 2]
def baseStart_5296121 : Nat := 118140960795 + 5296121 * 2 ^ 59
def prefixEnd_5296121 : Nat := 4983230072969 + 3 ^ 40 * 5296121 * 2
def baseEnd_5296121 : Nat := 2719455677370578635931089

theorem tailTrace_5296121 : CollatzResearch.WordTrace tailWord_5296121 prefixEnd_5296121 2719455677370578635931089 := by
  unfold tailWord_5296121
  simp only [CollatzResearch.WordTrace]
  refine ⟨193165402046065597300552217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128776934697377064867034811 193165402046065597300552217)
  ·
    refine ⟨144874051534549197975414163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193165402046065597300552217 144874051534549197975414163)
    ·
      refine ⟨217311077301823796963121245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144874051534549197975414163 217311077301823796963121245)
      ·
        refine ⟨81491653988183923861170467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217311077301823796963121245 81491653988183923861170467)
        ·
          refine ⟨122237480982275885791755701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81491653988183923861170467 122237480982275885791755701)
          ·
            refine ⟨11459763842088364292977097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122237480982275885791755701 11459763842088364292977097)
            ·
              refine ⟨8594822881566273219732823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11459763842088364292977097 8594822881566273219732823)
              ·
                refine ⟨12892234322349409829599235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8594822881566273219732823 12892234322349409829599235)
                ·
                  refine ⟨19338351483524114744398853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12892234322349409829599235 19338351483524114744398853)
                  ·
                    refine ⟨3625940903160771514574785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19338351483524114744398853 3625940903160771514574785)
                    ·
                      refine ⟨2719455677370578635931089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3625940903160771514574785 2719455677370578635931089)
                      ·
                        rfl

theorem cell23_5296121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_5296121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296121 prefixEnd_5296121 := by exact prefixLift 5296121
  have htrace : WordTrace (prefixWord ++ tailWord_5296121) baseStart_5296121 baseEnd_5296121 := by
    simpa [prefixWord, tailWord_5296121, baseEnd_5296121] using wordTrace_append hprefix tailTrace_5296121
  have hstable : (prefixWord ++ tailWord_5296121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296121).length < 2 ^ (prefixWord ++ tailWord_5296121).sum := by decide
  have hdescent : baseEnd_5296121 < baseStart_5296121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296154 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3]
def baseStart_5296154 : Nat := 118140960795 + 5296154 * 2 ^ 59
def prefixEnd_5296154 : Nat := 4983230072969 + 3 ^ 40 * 5296154 * 2
def baseEnd_5296154 : Nat := 2719472622232177006818437

theorem tailTrace_5296154 : CollatzResearch.WordTrace tailWord_5296154 prefixEnd_5296154 2719472622232177006818437 := by
  unfold tailWord_5296154
  simp only [CollatzResearch.WordTrace]
  refine ⟨48291651413736510984125879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128777737103297362624335677 48291651413736510984125879)
  ·
    refine ⟨72437477120604766476188819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48291651413736510984125879 72437477120604766476188819)
    ·
      refine ⟨108656215680907149714283229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72437477120604766476188819 108656215680907149714283229)
      ·
        refine ⟨40746080880340181142856211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108656215680907149714283229 40746080880340181142856211)
        ·
          refine ⟨61119121320510271714284317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40746080880340181142856211 61119121320510271714284317)
          ·
            refine ⟨22919670495191351892856619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61119121320510271714284317 22919670495191351892856619)
            ·
              refine ⟨34379505742787027839284929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22919670495191351892856619 34379505742787027839284929)
              ·
                refine ⟨25784629307090270879463697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34379505742787027839284929 25784629307090270879463697)
                ·
                  refine ⟨19338471980317703159597773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25784629307090270879463697 19338471980317703159597773)
                  ·
                    refine ⟨7251926992619138684849165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19338471980317703159597773 7251926992619138684849165)
                    ·
                      refine ⟨2719472622232177006818437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7251926992619138684849165 2719472622232177006818437)
                      ·
                        rfl

theorem cell23_5296154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_5296154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296154 prefixEnd_5296154 := by exact prefixLift 5296154
  have htrace : WordTrace (prefixWord ++ tailWord_5296154) baseStart_5296154 baseEnd_5296154 := by
    simpa [prefixWord, tailWord_5296154, baseEnd_5296154] using wordTrace_append hprefix tailTrace_5296154
  have hstable : (prefixWord ++ tailWord_5296154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296154).length < 2 ^ (prefixWord ++ tailWord_5296154).sum := by decide
  have hdescent : baseEnd_5296154 < baseStart_5296154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296174 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_5296174 : Nat := 118140960795 + 5296174 * 2 ^ 59
def prefixEnd_5296174 : Nat := 4983230072969 + 3 ^ 40 * 5296174 * 2
def baseEnd_5296174 : Nat := 906494297281755642856115

theorem tailTrace_5296174 : CollatzResearch.WordTrace tailWord_5296174 prefixEnd_5296174 906494297281755642856115 := by
  unfold tailWord_5296174
  simp only [CollatzResearch.WordTrace]
  refine ⟨24145916889359198419028947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128778223409915724901487717 24145916889359198419028947)
  ·
    refine ⟨36218875334038797628543421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24145916889359198419028947 36218875334038797628543421)
    ·
      refine ⟨13582078250264549110703783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36218875334038797628543421 13582078250264549110703783)
      ·
        refine ⟨20373117375396823666055675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13582078250264549110703783 20373117375396823666055675)
        ·
          refine ⟨30559676063095235499083513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20373117375396823666055675 30559676063095235499083513)
          ·
            refine ⟨22919757047321426624312635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30559676063095235499083513 22919757047321426624312635)
            ·
              refine ⟨34379635570982139936468953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22919757047321426624312635 34379635570982139936468953)
              ·
                refine ⟨25784726678236604952351715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34379635570982139936468953 25784726678236604952351715)
                ·
                  refine ⟨38677090017354907428527573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25784726678236604952351715 38677090017354907428527573)
                  ·
                    refine ⟨906494297281755642856115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38677090017354907428527573 906494297281755642856115)
                    ·
                      rfl

theorem cell23_5296174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_5296174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296174 prefixEnd_5296174 := by exact prefixLift 5296174
  have htrace : WordTrace (prefixWord ++ tailWord_5296174) baseStart_5296174 baseEnd_5296174 := by
    simpa [prefixWord, tailWord_5296174, baseEnd_5296174] using wordTrace_append hprefix tailTrace_5296174
  have hstable : (prefixWord ++ tailWord_5296174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296174).length < 2 ^ (prefixWord ++ tailWord_5296174).sum := by decide
  have hdescent : baseEnd_5296174 < baseStart_5296174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296197 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_5296197 : Nat := 118140960795 + 5296197 * 2 ^ 59
def prefixEnd_5296197 : Nat := 4983230072969 + 3 ^ 40 * 5296197 * 2
def baseEnd_5296197 : Nat := 2719494701900320338580739

theorem tailTrace_5296197 : CollatzResearch.WordTrace tailWord_5296197 prefixEnd_5296197 2719494701900320338580739 := by
  unfold tailWord_5296197
  simp only [CollatzResearch.WordTrace]
  refine ⟨193168173993790262280318845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128778782662526841520212563 193168173993790262280318845)
  ·
    refine ⟨72438065247671348355119567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193168173993790262280318845 72438065247671348355119567)
    ·
      refine ⟨108657097871507022532679351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72438065247671348355119567 108657097871507022532679351)
      ·
        refine ⟨162985646807260533799019027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108657097871507022532679351 162985646807260533799019027)
        ·
          refine ⟨244478470210890800698528541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162985646807260533799019027 244478470210890800698528541)
          ·
            refine ⟨91679426329084050261948203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244478470210890800698528541 91679426329084050261948203)
            ·
              refine ⟨137519139493626075392922305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91679426329084050261948203 137519139493626075392922305)
              ·
                refine ⟨103139354620219556544691729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137519139493626075392922305 103139354620219556544691729)
                ·
                  refine ⟨77354515965164667408518797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103139354620219556544691729 77354515965164667408518797)
                  ·
                    refine ⟨29007943486936750278194549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77354515965164667408518797 29007943486936750278194549)
                    ·
                      refine ⟨2719494701900320338580739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29007943486936750278194549 2719494701900320338580739)
                      ·
                        rfl

theorem cell23_5296197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_5296197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296197 prefixEnd_5296197 := by exact prefixLift 5296197
  have htrace : WordTrace (prefixWord ++ tailWord_5296197) baseStart_5296197 baseEnd_5296197 := by
    simpa [prefixWord, tailWord_5296197, baseEnd_5296197] using wordTrace_append hprefix tailTrace_5296197
  have hstable : (prefixWord ++ tailWord_5296197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296197).length < 2 ^ (prefixWord ++ tailWord_5296197).sum := by decide
  have hdescent : baseEnd_5296197 < baseStart_5296197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296204 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 5, 4]
def baseStart_5296204 : Nat := 118140960795 + 5296204 * 2 ^ 59
def prefixEnd_5296204 : Nat := 4983230072969 + 3 ^ 40 * 5296204 * 2
def baseEnd_5296204 : Nat := 906499432088300603731069

theorem tailTrace_5296204 : CollatzResearch.WordTrace tailWord_5296204 prefixEnd_5296204 906499432088300603731069 := by
  unfold tailWord_5296204
  simp only [CollatzResearch.WordTrace]
  refine ⟨96584214652382451237911833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128778952869843268317215777 96584214652382451237911833)
  ·
    refine ⟨72438160989286838428433875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96584214652382451237911833 72438160989286838428433875)
    ·
      refine ⟨108657241483930257642650813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72438160989286838428433875 108657241483930257642650813)
      ·
        refine ⟨40746465556473846615994055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108657241483930257642650813 40746465556473846615994055)
        ·
          refine ⟨61119698334710769923991083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40746465556473846615994055 61119698334710769923991083)
          ·
            refine ⟨91679547502066154885986625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61119698334710769923991083 91679547502066154885986625)
            ·
              refine ⟨68759660626549616164489969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91679547502066154885986625 68759660626549616164489969)
              ·
                refine ⟨51569745469912212123367477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68759660626549616164489969 51569745469912212123367477)
                ·
                  refine ⟨4834663637804269886565701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51569745469912212123367477 4834663637804269886565701)
                  ·
                    refine ⟨906499432088300603731069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4834663637804269886565701 906499432088300603731069)
                    ·
                      rfl

theorem cell23_5296204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_5296204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296204 prefixEnd_5296204 := by exact prefixLift 5296204
  have htrace : WordTrace (prefixWord ++ tailWord_5296204) baseStart_5296204 baseEnd_5296204 := by
    simpa [prefixWord, tailWord_5296204, baseEnd_5296204] using wordTrace_append hprefix tailTrace_5296204
  have hstable : (prefixWord ++ tailWord_5296204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296204).length < 2 ^ (prefixWord ++ tailWord_5296204).sum := by decide
  have hdescent : baseEnd_5296204 < baseStart_5296204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296207 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 4]
def baseStart_5296207 : Nat := 118140960795 + 5296207 * 2 ^ 59
def prefixEnd_5296207 : Nat := 4983230072969 + 3 ^ 40 * 5296207 * 2
def baseEnd_5296207 : Nat := 2719499836706865299455693

theorem tailTrace_5296207 : CollatzResearch.WordTrace tailWord_5296207 prefixEnd_5296207 2719499836706865299455693 := by
  unfold tailWord_5296207
  simp only [CollatzResearch.WordTrace]
  refine ⟨193168538723754033988182875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128779025815836022658788583 193168538723754033988182875)
  ·
    refine ⟨289752808085631050982274313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193168538723754033988182875 289752808085631050982274313)
    ·
      refine ⟨217314606064223288236705735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289752808085631050982274313 217314606064223288236705735)
      ·
        refine ⟨325971909096334932355058603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217314606064223288236705735 325971909096334932355058603)
        ·
          refine ⟨488957863644502398532587905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325971909096334932355058603 488957863644502398532587905)
          ·
            refine ⟨366718397733376798899440929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488957863644502398532587905 366718397733376798899440929)
            ·
              refine ⟨275038798300032599174580697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366718397733376798899440929 275038798300032599174580697)
              ·
                refine ⟨206279098725024449380935523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275038798300032599174580697 206279098725024449380935523)
                ·
                  refine ⟨309418648087536674071403285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206279098725024449380935523 309418648087536674071403285)
                  ·
                    refine ⟨14503999129103281597097029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 309418648087536674071403285 14503999129103281597097029)
                    ·
                      refine ⟨2719499836706865299455693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14503999129103281597097029 2719499836706865299455693)
                      ·
                        rfl

theorem cell23_5296207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_5296207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296207 prefixEnd_5296207 := by exact prefixLift 5296207
  have htrace : WordTrace (prefixWord ++ tailWord_5296207) baseStart_5296207 baseEnd_5296207 := by
    simpa [prefixWord, tailWord_5296207, baseEnd_5296207] using wordTrace_append hprefix tailTrace_5296207
  have hstable : (prefixWord ++ tailWord_5296207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296207).length < 2 ^ (prefixWord ++ tailWord_5296207).sum := by decide
  have hdescent : baseEnd_5296207 < baseStart_5296207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296217 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 8]
def baseStart_5296217 : Nat := 118140960795 + 5296217 * 2 ^ 59
def prefixEnd_5296217 : Nat := 4983230072969 + 3 ^ 40 * 5296217 * 2
def baseEnd_5296217 : Nat := 302167219057045584481183

theorem tailTrace_5296217 : CollatzResearch.WordTrace tailWord_5296217 prefixEnd_5296217 302167219057045584481183 := by
  unfold tailWord_5296217
  simp only [CollatzResearch.WordTrace]
  refine ⟨193168903453717805696046905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128779268969145203797364603 193168903453717805696046905)
  ·
    refine ⟨144876677590288354272035179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193168903453717805696046905 144876677590288354272035179)
    ·
      refine ⟨217315016385432531408052769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144876677590288354272035179 217315016385432531408052769)
      ·
        refine ⟨162986262289074398556039577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217315016385432531408052769 162986262289074398556039577)
        ·
          refine ⟨122239696716805798917029683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162986262289074398556039577 122239696716805798917029683)
          ·
            refine ⟨183359545075208698375544525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122239696716805798917029683 183359545075208698375544525)
            ·
              refine ⟨68759829403203261890829197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183359545075208698375544525 68759829403203261890829197)
              ·
                refine ⟨25784936026201223209060949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68759829403203261890829197 25784936026201223209060949)
                ·
                  refine ⟨302167219057045584481183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25784936026201223209060949 302167219057045584481183)
                  ·
                    rfl

theorem cell23_5296217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 8].length) (baseStart_5296217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296217 prefixEnd_5296217 := by exact prefixLift 5296217
  have htrace : WordTrace (prefixWord ++ tailWord_5296217) baseStart_5296217 baseEnd_5296217 := by
    simpa [prefixWord, tailWord_5296217, baseEnd_5296217] using wordTrace_append hprefix tailTrace_5296217
  have hstable : (prefixWord ++ tailWord_5296217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296217).length < 2 ^ (prefixWord ++ tailWord_5296217).sum := by decide
  have hdescent : baseEnd_5296217 < baseStart_5296217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296295 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_5296295 : Nat := 118140960795 + 5296295 * 2 ^ 59
def prefixEnd_5296295 : Nat := 4983230072969 + 3 ^ 40 * 5296295 * 2
def baseEnd_5296295 : Nat := 2719545023004460955155289

theorem tailTrace_5296295 : CollatzResearch.WordTrace tailWord_5296295 prefixEnd_5296295 2719545023004460955155289 := by
  unfold tailWord_5296295
  simp only [CollatzResearch.WordTrace]
  refine ⟨193171748347435225017386339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128781165564956816678257559 193171748347435225017386339)
  ·
    refine ⟨289757622521152837526079509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193171748347435225017386339 289757622521152837526079509)
    ·
      refine ⟨13582388555679039259034977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 289757622521152837526079509 13582388555679039259034977)
      ·
        refine ⟨10186791416759279444276233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13582388555679039259034977 10186791416759279444276233)
        ·
          refine ⟨7640093562569459583207175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10186791416759279444276233 7640093562569459583207175)
          ·
            refine ⟨11460140343854189374810763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7640093562569459583207175 11460140343854189374810763)
            ·
              refine ⟨17190210515781284062216145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11460140343854189374810763 17190210515781284062216145)
              ·
                refine ⟨12892657886835963046662109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17190210515781284062216145 12892657886835963046662109)
                ·
                  refine ⟨4834746707563486142498291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12892657886835963046662109 4834746707563486142498291)
                  ·
                    refine ⟨7252120061345229213747437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4834746707563486142498291 7252120061345229213747437)
                    ·
                      refine ⟨2719545023004460955155289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7252120061345229213747437 2719545023004460955155289)
                      ·
                        rfl

theorem cell23_5296295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_5296295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296295 prefixEnd_5296295 := by exact prefixLift 5296295
  have htrace : WordTrace (prefixWord ++ tailWord_5296295) baseStart_5296295 baseEnd_5296295 := by
    simpa [prefixWord, tailWord_5296295, baseEnd_5296295] using wordTrace_append hprefix tailTrace_5296295
  have hstable : (prefixWord ++ tailWord_5296295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296295).length < 2 ^ (prefixWord ++ tailWord_5296295).sum := by decide
  have hdescent : baseEnd_5296295 < baseStart_5296295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296335 : List Nat := [1, 1, 2, 1, 1, 3, 3, 6, 1, 2, 2]
def baseStart_5296335 : Nat := 118140960795 + 5296335 * 2 ^ 59
def prefixEnd_5296335 : Nat := 4983230072969 + 3 ^ 40 * 5296335 * 2
def baseEnd_5296335 : Nat := 2719565562230640798655105

theorem tailTrace_5296335 : CollatzResearch.WordTrace tailWord_5296335 prefixEnd_5296335 2719565562230640798655105 := by
  unfold tailWord_5296335
  simp only [CollatzResearch.WordTrace]
  refine ⟨193173207267290311848842459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128782138178193541232561639 193173207267290311848842459)
  ·
    refine ⟨289759810900935467773263689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193173207267290311848842459 289759810900935467773263689)
    ·
      refine ⟨217319858175701600829947767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289759810900935467773263689 217319858175701600829947767)
      ·
        refine ⟨325979787263552401244921651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217319858175701600829947767 325979787263552401244921651)
        ·
          refine ⟨488969680895328601867382477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325979787263552401244921651 488969680895328601867382477)
          ·
            refine ⟨183363630335748225700268429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 488969680895328601867382477 183363630335748225700268429)
            ·
              refine ⟨68761361375905584637600661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183363630335748225700268429 68761361375905584637600661)
              ·
                refine ⟨3223188814495574279887531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68761361375905584637600661 3223188814495574279887531)
                ·
                  refine ⟨4834783221743361419831297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3223188814495574279887531 4834783221743361419831297)
                  ·
                    refine ⟨3626087416307521064873473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4834783221743361419831297 3626087416307521064873473)
                    ·
                      refine ⟨2719565562230640798655105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3626087416307521064873473 2719565562230640798655105)
                      ·
                        rfl

theorem cell23_5296335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 1, 2, 2].length) (baseStart_5296335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296335 prefixEnd_5296335 := by exact prefixLift 5296335
  have htrace : WordTrace (prefixWord ++ tailWord_5296335) baseStart_5296335 baseEnd_5296335 := by
    simpa [prefixWord, tailWord_5296335, baseEnd_5296335] using wordTrace_append hprefix tailTrace_5296335
  have hstable : (prefixWord ++ tailWord_5296335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296335).length < 2 ^ (prefixWord ++ tailWord_5296335).sum := by decide
  have hdescent : baseEnd_5296335 < baseStart_5296335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296364 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_5296364 : Nat := 118140960795 + 5296364 * 2 ^ 59
def prefixEnd_5296364 : Nat := 4983230072969 + 3 ^ 40 * 5296364 * 2
def baseEnd_5296364 : Nat := 2719580453169621185192471

theorem tailTrace_5296364 : CollatzResearch.WordTrace tailWord_5296364 prefixEnd_5296364 2719580453169621185192471 := by
  unfold tailWord_5296364
  simp only [CollatzResearch.WordTrace]
  refine ⟨96587132492092624900824073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128782843322790166534432097 96587132492092624900824073)
  ·
    refine ⟨72440349369069468675618055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96587132492092624900824073 72440349369069468675618055)
    ·
      refine ⟨108660524053604203013427083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72440349369069468675618055 108660524053604203013427083)
      ·
        refine ⟨162990786080406304520140625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108660524053604203013427083 162990786080406304520140625)
        ·
          refine ⟨122243089560304728390105469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162990786080406304520140625 122243089560304728390105469)
          ·
            refine ⟨45841158585114273146289551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122243089560304728390105469 45841158585114273146289551)
            ·
              refine ⟨68761737877671409719434327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45841158585114273146289551 68761737877671409719434327)
              ·
                refine ⟨103142606816507114579151491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68761737877671409719434327 103142606816507114579151491)
                ·
                  refine ⟨154713910224760671868727237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103142606816507114579151491 154713910224760671868727237)
                  ·
                    refine ⟨29008858167142625975386357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154713910224760671868727237 29008858167142625975386357)
                    ·
                      refine ⟨2719580453169621185192471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29008858167142625975386357 2719580453169621185192471)
                      ·
                        rfl

theorem cell23_5296364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_5296364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296364 prefixEnd_5296364 := by exact prefixLift 5296364
  have htrace : WordTrace (prefixWord ++ tailWord_5296364) baseStart_5296364 baseEnd_5296364 := by
    simpa [prefixWord, tailWord_5296364, baseEnd_5296364] using wordTrace_append hprefix tailTrace_5296364
  have hstable : (prefixWord ++ tailWord_5296364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296364).length < 2 ^ (prefixWord ++ tailWord_5296364).sum := by decide
  have hdescent : baseEnd_5296364 < baseStart_5296364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296384 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 4, 6]
def baseStart_5296384 : Nat := 118140960795 + 5296384 * 2 ^ 59
def prefixEnd_5296384 : Nat := 4983230072969 + 3 ^ 40 * 5296384 * 2
def baseEnd_5296384 : Nat := 906530240927570368980793

theorem tailTrace_5296384 : CollatzResearch.WordTrace tailWord_5296384 prefixEnd_5296384 906530240927570368980793 := by
  unfold tailWord_5296384
  simp only [CollatzResearch.WordTrace]
  refine ⟨96587497222056396608688103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128783329629408528811584137 96587497222056396608688103)
  ·
    refine ⟨144881245833084594913032155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96587497222056396608688103 144881245833084594913032155)
    ·
      refine ⟨217321868749626892369548233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144881245833084594913032155 217321868749626892369548233)
      ·
        refine ⟨162991401562220169277161175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217321868749626892369548233 162991401562220169277161175)
        ·
          refine ⟨244487102343330253915741763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162991401562220169277161175 244487102343330253915741763)
          ·
            refine ⟨366730653514995380873612645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244487102343330253915741763 366730653514995380873612645)
            ·
              refine ⟨68761997534061633913802371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 366730653514995380873612645 68761997534061633913802371)
              ·
                refine ⟨103142996301092450870703557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68761997534061633913802371 103142996301092450870703557)
                ·
                  refine ⟨19339311806454834538256917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103142996301092450870703557 19339311806454834538256917)
                  ·
                    refine ⟨906530240927570368980793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19339311806454834538256917 906530240927570368980793)
                    ·
                      rfl

theorem cell23_5296384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_5296384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296384 prefixEnd_5296384 := by exact prefixLift 5296384
  have htrace : WordTrace (prefixWord ++ tailWord_5296384) baseStart_5296384 baseEnd_5296384 := by
    simpa [prefixWord, tailWord_5296384, baseEnd_5296384] using wordTrace_append hprefix tailTrace_5296384
  have hstable : (prefixWord ++ tailWord_5296384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296384).length < 2 ^ (prefixWord ++ tailWord_5296384).sum := by decide
  have hdescent : baseEnd_5296384 < baseStart_5296384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296386 : List Nat := [3, 4, 1, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_5296386 : Nat := 118140960795 + 5296386 * 2 ^ 59
def prefixEnd_5296386 : Nat := 4983230072969 + 3 ^ 40 * 5296386 * 2
def baseEnd_5296386 : Nat := 2719591749744020099117371

theorem tailTrace_5296386 : CollatzResearch.WordTrace tailWord_5296386 prefixEnd_5296386 2719591749744020099117371 := by
  unfold tailWord_5296386
  simp only [CollatzResearch.WordTrace]
  refine ⟨48293766847526386889737253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128783378260070365039299341 48293766847526386889737253)
  ·
    refine ⟨9055081283911197541825735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48293766847526386889737253 9055081283911197541825735)
    ·
      refine ⟨13582621925866796312738603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9055081283911197541825735 13582621925866796312738603)
      ·
        refine ⟨20373932888800194469107905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13582621925866796312738603 20373932888800194469107905)
        ·
          refine ⟨15280449666600145851830929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20373932888800194469107905 15280449666600145851830929)
          ·
            refine ⟨11460337249950109388873197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15280449666600145851830929 11460337249950109388873197)
            ·
              refine ⟨4297626468731291020827449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11460337249950109388873197 4297626468731291020827449)
              ·
                refine ⟨3223219851548468265620587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4297626468731291020827449 3223219851548468265620587)
                ·
                  refine ⟨4834829777322702398430881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3223219851548468265620587 4834829777322702398430881)
                  ·
                    refine ⟨3626122332992026798823161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4834829777322702398430881 3626122332992026798823161)
                    ·
                      refine ⟨2719591749744020099117371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3626122332992026798823161 2719591749744020099117371)
                      ·
                        rfl

theorem cell23_5296386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_5296386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296386 prefixEnd_5296386 := by exact prefixLift 5296386
  have htrace : WordTrace (prefixWord ++ tailWord_5296386) baseStart_5296386 baseEnd_5296386 := by
    simpa [prefixWord, tailWord_5296386, baseEnd_5296386] using wordTrace_append hprefix tailTrace_5296386
  have hstable : (prefixWord ++ tailWord_5296386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296386).length < 2 ^ (prefixWord ++ tailWord_5296386).sum := by decide
  have hdescent : baseEnd_5296386 < baseStart_5296386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296408 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 1, 4, 2]
def baseStart_5296408 : Nat := 118140960795 + 5296408 * 2 ^ 59
def prefixEnd_5296408 : Nat := 4983230072969 + 3 ^ 40 * 5296408 * 2
def baseEnd_5296408 : Nat := 2719603046318419013042269

theorem tailTrace_5296408 : CollatzResearch.WordTrace tailWord_5296408 prefixEnd_5296408 2719603046318419013042269 := by
  unfold tailWord_5296408
  simp only [CollatzResearch.WordTrace]
  refine ⟨96587934898012922658124939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128783913197350563544166585 96587934898012922658124939)
  ·
    refine ⟨144881902347019383987187409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96587934898012922658124939 144881902347019383987187409)
    ·
      refine ⟨108661426760264537990390557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144881902347019383987187409 108661426760264537990390557)
      ·
        refine ⟨40748035035099201746396459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108661426760264537990390557 40748035035099201746396459)
        ·
          refine ⟨61122052552648802619594689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40748035035099201746396459 61122052552648802619594689)
          ·
            refine ⟨45841539414486601964696017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61122052552648802619594689 45841539414486601964696017)
            ·
              refine ⟨34381154560864951473522013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45841539414486601964696017 34381154560864951473522013)
              ·
                refine ⟨12892932960324356802570755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34381154560864951473522013 12892932960324356802570755)
                ·
                  refine ⟨19339399440486535203856133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12892932960324356802570755 19339399440486535203856133)
                  ·
                    refine ⟨3626137395091225350723025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19339399440486535203856133 3626137395091225350723025)
                    ·
                      refine ⟨2719603046318419013042269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3626137395091225350723025 2719603046318419013042269)
                      ·
                        rfl

theorem cell23_5296408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_5296408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296408 prefixEnd_5296408 := by exact prefixLift 5296408
  have htrace : WordTrace (prefixWord ++ tailWord_5296408) baseStart_5296408 baseEnd_5296408 := by
    simpa [prefixWord, tailWord_5296408, baseEnd_5296408] using wordTrace_append hprefix tailTrace_5296408
  have hstable : (prefixWord ++ tailWord_5296408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296408).length < 2 ^ (prefixWord ++ tailWord_5296408).sum := by decide
  have hdescent : baseEnd_5296408 < baseStart_5296408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296442 : List Nat := [3, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2]
def baseStart_5296442 : Nat := 118140960795 + 5296442 * 2 ^ 59
def prefixEnd_5296442 : Nat := 4983230072969 + 3 ^ 40 * 5296442 * 2
def baseEnd_5296442 : Nat := 2719620504660671880017113

theorem tailTrace_5296442 : CollatzResearch.WordTrace tailWord_5296442 prefixEnd_5296442 2719620504660671880017113 := by
  unfold tailWord_5296442
  simp only [CollatzResearch.WordTrace]
  refine ⟨48294277469475667280746895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128784739918601779415325053 48294277469475667280746895)
  ·
    refine ⟨72441416204213500921120343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48294277469475667280746895 72441416204213500921120343)
    ·
      refine ⟨108662124306320251381680515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72441416204213500921120343 108662124306320251381680515)
      ·
        refine ⟨162993186459480377072520773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108662124306320251381680515 162993186459480377072520773)
        ·
          refine ⟨30561222461152570701097645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162993186459480377072520773 30561222461152570701097645)
          ·
            refine ⟨11460458422932214012911617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30561222461152570701097645 11460458422932214012911617)
            ·
              refine ⟨8595343817199160509683713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11460458422932214012911617 8595343817199160509683713)
              ·
                refine ⟨6446507862899370382262785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8595343817199160509683713 6446507862899370382262785)
                ·
                  refine ⟨4834880897174527786697089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6446507862899370382262785 4834880897174527786697089)
                  ·
                    refine ⟨3626160672880895840022817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4834880897174527786697089 3626160672880895840022817)
                    ·
                      refine ⟨2719620504660671880017113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3626160672880895840022817 2719620504660671880017113)
                      ·
                        rfl

theorem cell23_5296442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2].length) (baseStart_5296442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296442 prefixEnd_5296442 := by exact prefixLift 5296442
  have htrace : WordTrace (prefixWord ++ tailWord_5296442) baseStart_5296442 baseEnd_5296442 := by
    simpa [prefixWord, tailWord_5296442, baseEnd_5296442] using wordTrace_append hprefix tailTrace_5296442
  have hstable : (prefixWord ++ tailWord_5296442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296442).length < 2 ^ (prefixWord ++ tailWord_5296442).sum := by decide
  have hdescent : baseEnd_5296442 < baseStart_5296442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296552 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_5296552 : Nat := 118140960795 + 5296552 * 2 ^ 59
def prefixEnd_5296552 : Nat := 4983230072969 + 3 ^ 40 * 5296552 * 2
def baseEnd_5296552 : Nat := 2719676987532666449641607

theorem tailTrace_5296552 : CollatzResearch.WordTrace tailWord_5296552 prefixEnd_5296552 2719676987532666449641607 := by
  unfold tailWord_5296552
  simp only [CollatzResearch.WordTrace]
  refine ⟨96590560953752078954745955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128787414605002771939661273 96590560953752078954745955)
  ·
    refine ⟨144885841430628118432118933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96590560953752078954745955 144885841430628118432118933)
    ·
      refine ⟨6791523817060693051505575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 144885841430628118432118933 6791523817060693051505575)
      ·
        refine ⟨10187285725591039577258363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6791523817060693051505575 10187285725591039577258363)
        ·
          refine ⟨15280928588386559365887545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10187285725591039577258363 15280928588386559365887545)
          ·
            refine ⟨11460696441289919524415659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15280928588386559365887545 11460696441289919524415659)
            ·
              refine ⟨17191044661934879286623489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11460696441289919524415659 17191044661934879286623489)
              ·
                refine ⟨12893283496451159464967617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17191044661934879286623489 12893283496451159464967617)
                ·
                  refine ⟨9669962622338369598725713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12893283496451159464967617 9669962622338369598725713)
                  ·
                    refine ⟨7252471966753777199044285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9669962622338369598725713 7252471966753777199044285)
                    ·
                      refine ⟨2719676987532666449641607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7252471966753777199044285 2719676987532666449641607)
                      ·
                        rfl

theorem cell23_5296552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_5296552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296552 prefixEnd_5296552 := by exact prefixLift 5296552
  have htrace : WordTrace (prefixWord ++ tailWord_5296552) baseStart_5296552 baseEnd_5296552 := by
    simpa [prefixWord, tailWord_5296552, baseEnd_5296552] using wordTrace_append hprefix tailTrace_5296552
  have hstable : (prefixWord ++ tailWord_5296552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296552).length < 2 ^ (prefixWord ++ tailWord_5296552).sum := by decide
  have hdescent : baseEnd_5296552 < baseStart_5296552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296572 : List Nat := [2, 2, 2, 4, 1, 3, 2, 1, 6]
def baseStart_5296572 : Nat := 118140960795 + 5296572 * 2 ^ 59
def prefixEnd_5296572 : Nat := 4983230072969 + 3 ^ 40 * 5296572 * 2
def baseEnd_5296572 : Nat := 302187473016195152376835

theorem tailTrace_5296572 : CollatzResearch.WordTrace tailWord_5296572 prefixEnd_5296572 302187473016195152376835 := by
  unfold tailWord_5296572
  simp only [CollatzResearch.WordTrace]
  refine ⟨96590925683715850662609985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128787900911621134216813313 96590925683715850662609985)
  ·
    refine ⟨72443194262786887996957489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96590925683715850662609985 72443194262786887996957489)
    ·
      refine ⟨54332395697090165997718117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72443194262786887996957489 54332395697090165997718117)
      ·
        refine ⟨10187324193204406124572147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54332395697090165997718117 10187324193204406124572147)
        ·
          refine ⟨15280986289806609186858221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10187324193204406124572147 15280986289806609186858221)
          ·
            refine ⟨5730369858677478445071833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15280986289806609186858221 5730369858677478445071833)
            ·
              refine ⟨4297777394008108833803875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5730369858677478445071833 4297777394008108833803875)
              ·
                refine ⟨6446666091012163250705813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4297777394008108833803875 6446666091012163250705813)
                ·
                  refine ⟨302187473016195152376835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6446666091012163250705813 302187473016195152376835)
                  ·
                    rfl

theorem cell23_5296572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_5296572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296572 prefixEnd_5296572 := by exact prefixLift 5296572
  have htrace : WordTrace (prefixWord ++ tailWord_5296572) baseStart_5296572 baseEnd_5296572 := by
    simpa [prefixWord, tailWord_5296572, baseEnd_5296572] using wordTrace_append hprefix tailTrace_5296572
  have hstable : (prefixWord ++ tailWord_5296572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296572).length < 2 ^ (prefixWord ++ tailWord_5296572).sum := by decide
  have hdescent : baseEnd_5296572 < baseStart_5296572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296581 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 7, 6]
def baseStart_5296581 : Nat := 118140960795 + 5296581 * 2 ^ 59
def prefixEnd_5296581 : Nat := 4983230072969 + 3 ^ 40 * 5296581 * 2
def baseEnd_5296581 : Nat := 906563959490548945392991

theorem tailTrace_5296581 : CollatzResearch.WordTrace tailWord_5296581 prefixEnd_5296581 906563959490548945392991 := by
  unfold tailWord_5296581
  simp only [CollatzResearch.WordTrace]
  refine ⟨193182179624399095862297597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128788119749599397241531731 193182179624399095862297597)
  ·
    refine ⟨72443317359149660948361599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193182179624399095862297597 72443317359149660948361599)
    ·
      refine ⟨108664976038724491422542399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72443317359149660948361599 108664976038724491422542399)
      ·
        refine ⟨162997464058086737133813599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108664976038724491422542399 162997464058086737133813599)
        ·
          refine ⟨244496196087130105700720399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162997464058086737133813599 244496196087130105700720399)
          ·
            refine ⟨366744294130695158551080599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244496196087130105700720399 366744294130695158551080599)
            ·
              refine ⟨550116441196042737826620899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366744294130695158551080599 550116441196042737826620899)
              ·
                refine ⟨825174661794064106739931349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550116441196042737826620899 825174661794064106739931349)
                ·
                  refine ⟨19340031135798377501717141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 825174661794064106739931349 19340031135798377501717141)
                  ·
                    refine ⟨906563959490548945392991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19340031135798377501717141 906563959490548945392991)
                    ·
                      rfl

theorem cell23_5296581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_5296581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296581 prefixEnd_5296581 := by exact prefixLift 5296581
  have htrace : WordTrace (prefixWord ++ tailWord_5296581) baseStart_5296581 baseEnd_5296581 := by
    simpa [prefixWord, tailWord_5296581, baseEnd_5296581] using wordTrace_append hprefix tailTrace_5296581
  have hstable : (prefixWord ++ tailWord_5296581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296581).length < 2 ^ (prefixWord ++ tailWord_5296581).sum := by decide
  have hdescent : baseEnd_5296581 < baseStart_5296581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296610 : List Nat := [3, 3, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_5296610 : Nat := 118140960795 + 5296610 * 2 ^ 59
def prefixEnd_5296610 : Nat := 4983230072969 + 3 ^ 40 * 5296610 * 2
def baseEnd_5296610 : Nat := 906568923136875740905447

theorem tailTrace_5296610 : CollatzResearch.WordTrace tailWord_5296610 prefixEnd_5296610 906568923136875740905447 := by
  unfold tailWord_5296610
  simp only [CollatzResearch.WordTrace]
  refine ⟨48295809335323508453775821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128788824894196022543402189 48295809335323508453775821)
  ·
    refine ⟨18110928500746315670165933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48295809335323508453775821 18110928500746315670165933)
    ·
      refine ⟨6791598187779868376312225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18110928500746315670165933 6791598187779868376312225)
      ·
        refine ⟨5093698640834901282234169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6791598187779868376312225 5093698640834901282234169)
        ·
          refine ⟨3820273980626175961675627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5093698640834901282234169 3820273980626175961675627)
          ·
            refine ⟨5730410970939263942513441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3820273980626175961675627 5730410970939263942513441)
            ·
              refine ⟨4297808228204447956885081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5730410970939263942513441 4297808228204447956885081)
              ·
                refine ⟨3223356171153335967663811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4297808228204447956885081 3223356171153335967663811)
                ·
                  refine ⟨4835034256730003951495717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3223356171153335967663811 4835034256730003951495717)
                  ·
                    refine ⟨906568923136875740905447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4835034256730003951495717 906568923136875740905447)
                    ·
                      rfl

theorem cell23_5296610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_5296610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296610 prefixEnd_5296610 := by exact prefixLift 5296610
  have htrace : WordTrace (prefixWord ++ tailWord_5296610) baseStart_5296610 baseEnd_5296610 := by
    simpa [prefixWord, tailWord_5296610, baseEnd_5296610] using wordTrace_append hprefix tailTrace_5296610
  have hstable : (prefixWord ++ tailWord_5296610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296610).length < 2 ^ (prefixWord ++ tailWord_5296610).sum := by decide
  have hdescent : baseEnd_5296610 < baseStart_5296610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296611 : List Nat := [1, 1, 1, 6, 14]
def baseStart_5296611 : Nat := 118140960795 + 5296611 * 2 ^ 59
def prefixEnd_5296611 : Nat := 4983230072969 + 3 ^ 40 * 5296611 * 2
def baseEnd_5296611 : Nat := 3730737013568287680115

theorem tailTrace_5296611 : CollatzResearch.WordTrace tailWord_5296611 prefixEnd_5296611 3730737013568287680115 := by
  unfold tailWord_5296611
  simp only [CollatzResearch.WordTrace]
  refine ⟨193183273814290410985889687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128788849209526940657259791 193183273814290410985889687)
  ·
    refine ⟨289774910721435616478834531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193183273814290410985889687 289774910721435616478834531)
    ·
      refine ⟨434662366082153424718251797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289774910721435616478834531 434662366082153424718251797)
      ·
        refine ⟨20374798410100941783668053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 434662366082153424718251797 20374798410100941783668053)
        ·
          refine ⟨3730737013568287680115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 20374798410100941783668053 3730737013568287680115)
          ·
            rfl

theorem cell23_5296611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 14].length) (baseStart_5296611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296611 prefixEnd_5296611 := by exact prefixLift 5296611
  have htrace : WordTrace (prefixWord ++ tailWord_5296611) baseStart_5296611 baseEnd_5296611 := by
    simpa [prefixWord, tailWord_5296611, baseEnd_5296611] using wordTrace_append hprefix tailTrace_5296611
  have hstable : (prefixWord ++ tailWord_5296611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296611).length < 2 ^ (prefixWord ++ tailWord_5296611).sum := by decide
  have hdescent : baseEnd_5296611 < baseStart_5296611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296616 : List Nat := [2, 1, 4, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_5296616 : Nat := 118140960795 + 5296616 * 2 ^ 59
def prefixEnd_5296616 : Nat := 4983230072969 + 3 ^ 40 * 5296616 * 2
def baseEnd_5296616 : Nat := 2719709850294554199241313

theorem tailTrace_5296616 : CollatzResearch.WordTrace tailWord_5296616 prefixEnd_5296616 2719709850294554199241313 := by
  unfold tailWord_5296616
  simp only [CollatzResearch.WordTrace]
  refine ⟨96591728089636148419910851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128788970786181531226547801 96591728089636148419910851)
  ·
    refine ⟨144887592134454222629866277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96591728089636148419910851 144887592134454222629866277)
    ·
      refine ⟨27166423525210166743099927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144887592134454222629866277 27166423525210166743099927)
      ·
        refine ⟨40749635287815250114649891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27166423525210166743099927 40749635287815250114649891)
        ·
          refine ⟨61124452931722875171974837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40749635287815250114649891 61124452931722875171974837)
          ·
            refine ⟨5730417462349019547372641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61124452931722875171974837 5730417462349019547372641)
            ·
              refine ⟨4297813096761764660529481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5730417462349019547372641 4297813096761764660529481)
              ·
                refine ⟨3223359822571323495397111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4297813096761764660529481 3223359822571323495397111)
                ·
                  refine ⟨4835039733856985243095667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3223359822571323495397111 4835039733856985243095667)
                  ·
                    refine ⟨7252559600785477864643501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4835039733856985243095667 7252559600785477864643501)
                    ·
                      refine ⟨2719709850294554199241313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7252559600785477864643501 2719709850294554199241313)
                      ·
                        rfl

theorem cell23_5296616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_5296616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296616 prefixEnd_5296616 := by exact prefixLift 5296616
  have htrace : WordTrace (prefixWord ++ tailWord_5296616) baseStart_5296616 baseEnd_5296616 := by
    simpa [prefixWord, tailWord_5296616, baseEnd_5296616] using wordTrace_append hprefix tailTrace_5296616
  have hstable : (prefixWord ++ tailWord_5296616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296616).length < 2 ^ (prefixWord ++ tailWord_5296616).sum := by decide
  have hdescent : baseEnd_5296616 < baseStart_5296616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296688 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 2, 6]
def baseStart_5296688 : Nat := 118140960795 + 5296688 * 2 ^ 59
def prefixEnd_5296688 : Nat := 4983230072969 + 3 ^ 40 * 5296688 * 2
def baseEnd_5296688 : Nat := 906582273633892639180327

theorem tailTrace_5296688 : CollatzResearch.WordTrace tailWord_5296688 prefixEnd_5296688 906582273633892639180327 := by
  unfold tailWord_5296688
  simp only [CollatzResearch.WordTrace]
  refine ⟨96593041117505726568221359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128790721490007635424295145 96593041117505726568221359)
  ·
    refine ⟨144889561676258589852332039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96593041117505726568221359 144889561676258589852332039)
    ·
      refine ⟨217334342514387884778498059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144889561676258589852332039 217334342514387884778498059)
      ·
        refine ⟨326001513771581827167747089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217334342514387884778498059 326001513771581827167747089)
        ·
          refine ⟨244501135328686370375810317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326001513771581827167747089 244501135328686370375810317)
          ·
            refine ⟨91687925748257388890928869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244501135328686370375810317 91687925748257388890928869)
            ·
              refine ⟨17191486077798260417049163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91687925748257388890928869 17191486077798260417049163)
              ·
                refine ⟨25787229116697390625573745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17191486077798260417049163 25787229116697390625573745)
                ·
                  refine ⟨19340421837523042969180309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25787229116697390625573745 19340421837523042969180309)
                  ·
                    refine ⟨906582273633892639180327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19340421837523042969180309 906582273633892639180327)
                    ·
                      rfl

theorem cell23_5296688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_5296688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296688 prefixEnd_5296688 := by exact prefixLift 5296688
  have htrace : WordTrace (prefixWord ++ tailWord_5296688) baseStart_5296688 baseEnd_5296688 := by
    simpa [prefixWord, tailWord_5296688, baseEnd_5296688] using wordTrace_append hprefix tailTrace_5296688
  have hstable : (prefixWord ++ tailWord_5296688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296688).length < 2 ^ (prefixWord ++ tailWord_5296688).sum := by decide
  have hdescent : baseEnd_5296688 < baseStart_5296688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296718 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 9]
def baseStart_5296718 : Nat := 118140960795 + 5296718 * 2 ^ 59
def prefixEnd_5296718 : Nat := 4983230072969 + 3 ^ 40 * 5296718 * 2
def baseEnd_5296718 : Nat := 302195802813479200018427

theorem tailTrace_5296718 : CollatzResearch.WordTrace tailWord_5296718 prefixEnd_5296718 302195802813479200018427 := by
  unfold tailWord_5296718
  simp only [CollatzResearch.WordTrace]
  refine ⟨24148397053112846032504351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128791450949935178840023205 24148397053112846032504351)
  ·
    refine ⟨36222595579669269048756527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24148397053112846032504351 36222595579669269048756527)
    ·
      refine ⟨54333893369503903573134791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36222595579669269048756527 54333893369503903573134791)
      ·
        refine ⟨81500840054255855359702187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54333893369503903573134791 81500840054255855359702187)
        ·
          refine ⟨122251260081383783039553281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81500840054255855359702187 122251260081383783039553281)
          ·
            refine ⟨91688445061037837279664961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122251260081383783039553281 91688445061037837279664961)
            ·
              refine ⟨68766333795778377959748721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91688445061037837279664961 68766333795778377959748721)
              ·
                refine ⟨51574750346833783469811541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68766333795778377959748721 51574750346833783469811541)
                ·
                  refine ⟨302195802813479200018427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51574750346833783469811541 302195802813479200018427)
                  ·
                    rfl

theorem cell23_5296718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_5296718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296718 prefixEnd_5296718 := by exact prefixLift 5296718
  have htrace : WordTrace (prefixWord ++ tailWord_5296718) baseStart_5296718 baseEnd_5296718 := by
    simpa [prefixWord, tailWord_5296718, baseEnd_5296718] using wordTrace_append hprefix tailTrace_5296718
  have hstable : (prefixWord ++ tailWord_5296718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296718).length < 2 ^ (prefixWord ++ tailWord_5296718).sum := by decide
  have hdescent : baseEnd_5296718 < baseStart_5296718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296735 : List Nat := [1, 1, 2, 3, 1, 1, 1, 8, 5]
def baseStart_5296735 : Nat := 118140960795 + 5296735 * 2 ^ 59
def prefixEnd_5296735 : Nat := 4983230072969 + 3 ^ 40 * 5296735 * 2
def baseEnd_5296735 : Nat := 302196772721382137072585

theorem tailTrace_5296735 : CollatzResearch.WordTrace tailWord_5296735 prefixEnd_5296735 302196772721382137072585 := by
  unfold tailWord_5296735
  simp only [CollatzResearch.WordTrace]
  refine ⟨193187796465841180163403659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128791864310560786775602439 193187796465841180163403659)
  ·
    refine ⟨289781694698761770245105489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193187796465841180163403659 289781694698761770245105489)
    ·
      refine ⟨217336271024071327683829117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289781694698761770245105489 217336271024071327683829117)
      ·
        refine ⟨81501101634026747881435919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217336271024071327683829117 81501101634026747881435919)
        ·
          refine ⟨122251652451040121822153879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81501101634026747881435919 122251652451040121822153879)
          ·
            refine ⟨183377478676560182733230819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122251652451040121822153879 183377478676560182733230819)
            ·
              refine ⟨275066218014840274099846229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183377478676560182733230819 275066218014840274099846229)
              ·
                refine ⟨3223432242361409462107573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 275066218014840274099846229 3223432242361409462107573)
                ·
                  refine ⟨302196772721382137072585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3223432242361409462107573 302196772721382137072585)
                  ·
                    rfl

theorem cell23_5296735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 5].length) (baseStart_5296735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296735 prefixEnd_5296735 := by exact prefixLift 5296735
  have htrace : WordTrace (prefixWord ++ tailWord_5296735) baseStart_5296735 baseEnd_5296735 := by
    simpa [prefixWord, tailWord_5296735, baseEnd_5296735] using wordTrace_append hprefix tailTrace_5296735
  have hstable : (prefixWord ++ tailWord_5296735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296735).length < 2 ^ (prefixWord ++ tailWord_5296735).sum := by decide
  have hdescent : baseEnd_5296735 < baseStart_5296735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296748 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 3, 7]
def baseStart_5296748 : Nat := 118140960795 + 5296748 * 2 ^ 59
def prefixEnd_5296748 : Nat := 4983230072969 + 3 ^ 40 * 5296748 * 2
def baseEnd_5296748 : Nat := 906592543246982560930235

theorem tailTrace_5296748 : CollatzResearch.WordTrace tailWord_5296748 prefixEnd_5296748 906592543246982560930235 := by
  unfold tailWord_5296748
  simp only [CollatzResearch.WordTrace]
  refine ⟨96594135307397041691813449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128792180409862722255751265 96594135307397041691813449)
  ·
    refine ⟨72445601480547781268860087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96594135307397041691813449 72445601480547781268860087)
    ·
      refine ⟨108668402220821671903290131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72445601480547781268860087 108668402220821671903290131)
      ·
        refine ⟨163002603331232507854935197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108668402220821671903290131 163002603331232507854935197)
        ·
          refine ⟨61125976249212190445600699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163002603331232507854935197 61125976249212190445600699)
          ·
            refine ⟨91688964373818285668401049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61125976249212190445600699 91688964373818285668401049)
            ·
              refine ⟨68766723280363714251300787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91688964373818285668401049 68766723280363714251300787)
              ·
                refine ⟨103150084920545571376951181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68766723280363714251300787 103150084920545571376951181)
                ·
                  refine ⟨38681281845204589266356693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103150084920545571376951181 38681281845204589266356693)
                  ·
                    refine ⟨906592543246982560930235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38681281845204589266356693 906592543246982560930235)
                    ·
                      rfl

theorem cell23_5296748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_5296748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296748 prefixEnd_5296748 := by exact prefixLift 5296748
  have htrace : WordTrace (prefixWord ++ tailWord_5296748) baseStart_5296748 baseEnd_5296748 := by
    simpa [prefixWord, tailWord_5296748, baseEnd_5296748] using wordTrace_append hprefix tailTrace_5296748
  have hstable : (prefixWord ++ tailWord_5296748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296748).length < 2 ^ (prefixWord ++ tailWord_5296748).sum := by decide
  have hdescent : baseEnd_5296748 < baseStart_5296748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296755 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 4, 5, 2]
def baseStart_5296755 : Nat := 118140960795 + 5296755 * 2 ^ 59
def prefixEnd_5296755 : Nat := 4983230072969 + 3 ^ 40 * 5296755 * 2
def baseEnd_5296755 : Nat := 2719781224105529155403173

theorem tailTrace_5296755 : CollatzResearch.WordTrace tailWord_5296755 prefixEnd_5296755 2719781224105529155403173 := by
  unfold tailWord_5296755
  simp only [CollatzResearch.WordTrace]
  refine ⟨193188525925768723579131719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128792350617179149052754479 193188525925768723579131719)
  ·
    refine ⟨289782788888653085368697579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193188525925768723579131719 289782788888653085368697579)
    ·
      refine ⟨434674183332979628053046369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289782788888653085368697579 434674183332979628053046369)
      ·
        refine ⟨326005637499734721039784777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434674183332979628053046369 326005637499734721039784777)
        ·
          refine ⟨244504228124801040779838583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326005637499734721039784777 244504228124801040779838583)
          ·
            refine ⟨366756342187201561169757875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244504228124801040779838583 366756342187201561169757875)
            ·
              refine ⟨550134513280802341754636813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366756342187201561169757875 550134513280802341754636813)
              ·
                refine ⟨206300442480300878157988805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 550134513280802341754636813 206300442480300878157988805)
                ·
                  refine ⟨38681332965056414654622901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 206300442480300878157988805 38681332965056414654622901)
                  ·
                    refine ⟨3626374965474038873870897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38681332965056414654622901 3626374965474038873870897)
                    ·
                      refine ⟨2719781224105529155403173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3626374965474038873870897 2719781224105529155403173)
                      ·
                        rfl

theorem cell23_5296755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 5, 2].length) (baseStart_5296755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296755 prefixEnd_5296755 := by exact prefixLift 5296755
  have htrace : WordTrace (prefixWord ++ tailWord_5296755) baseStart_5296755 baseEnd_5296755 := by
    simpa [prefixWord, tailWord_5296755, baseEnd_5296755] using wordTrace_append hprefix tailTrace_5296755
  have hstable : (prefixWord ++ tailWord_5296755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296755).length < 2 ^ (prefixWord ++ tailWord_5296755).sum := by decide
  have hdescent : baseEnd_5296755 < baseStart_5296755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296786 : List Nat := [3, 2, 3, 1, 2, 3, 2, 2, 5]
def baseStart_5296786 : Nat := 118140960795 + 5296786 * 2 ^ 59
def prefixEnd_5296786 : Nat := 4983230072969 + 3 ^ 40 * 5296786 * 2
def baseEnd_5296786 : Nat := 302199682445090948235059

theorem tailTrace_5296786 : CollatzResearch.WordTrace tailWord_5296786 prefixEnd_5296786 302199682445090948235059 := by
  unfold tailWord_5296786
  simp only [CollatzResearch.WordTrace]
  refine ⟨48297414147164103968377553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128793104392437610582340141 48297414147164103968377553)
  ·
    refine ⟨36223060610373077976283165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48297414147164103968377553 36223060610373077976283165)
    ·
      refine ⟨13583647728889904241106187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36223060610373077976283165 13583647728889904241106187)
      ·
        refine ⟨20375471593334856361659281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13583647728889904241106187 20375471593334856361659281)
        ·
          refine ⟨15281603695001142271244461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20375471593334856361659281 15281603695001142271244461)
          ·
            refine ⟨5730601385625428351716673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15281603695001142271244461 5730601385625428351716673)
            ·
              refine ⟨4297951039219071263787505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5730601385625428351716673 4297951039219071263787505)
              ·
                refine ⟨3223463279414303447840629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4297951039219071263787505 3223463279414303447840629)
                ·
                  refine ⟨302199682445090948235059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3223463279414303447840629 302199682445090948235059)
                  ·
                    rfl

theorem cell23_5296786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_5296786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296786 prefixEnd_5296786 := by exact prefixLift 5296786
  have htrace : WordTrace (prefixWord ++ tailWord_5296786) baseStart_5296786 baseEnd_5296786 := by
    simpa [prefixWord, tailWord_5296786, baseEnd_5296786] using wordTrace_append hprefix tailTrace_5296786
  have hstable : (prefixWord ++ tailWord_5296786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296786).length < 2 ^ (prefixWord ++ tailWord_5296786).sum := by decide
  have hdescent : baseEnd_5296786 < baseStart_5296786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296805 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 1, 4, 3]
def baseStart_5296805 : Nat := 118140960795 + 5296805 * 2 ^ 59
def prefixEnd_5296805 : Nat := 4983230072969 + 3 ^ 40 * 5296805 * 2
def baseEnd_5296805 : Nat := 2719806898138253959777943

theorem tailTrace_5296805 : CollatzResearch.WordTrace tailWord_5296805 prefixEnd_5296805 2719806898138253959777943 := by
  unfold tailWord_5296805
  simp only [CollatzResearch.WordTrace]
  refine ⟨193190349575587582118451869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128793566383725054745634579 193190349575587582118451869)
  ·
    refine ⟨72446381090845343294419451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193190349575587582118451869 72446381090845343294419451)
    ·
      refine ⟨108669571636268014941629177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72446381090845343294419451 108669571636268014941629177)
      ·
        refine ⟨81502178727201011206221883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108669571636268014941629177 81502178727201011206221883)
        ·
          refine ⟨122253268090801516809332825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81502178727201011206221883 122253268090801516809332825)
          ·
            refine ⟨91689951068101137606999619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122253268090801516809332825 91689951068101137606999619)
            ·
              refine ⟨137534926602151706410499429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91689951068101137606999619 137534926602151706410499429)
              ·
                refine ⟨25787798737903444951968643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137534926602151706410499429 25787798737903444951968643)
                ·
                  refine ⟨38681698106855167427952965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25787798737903444951968643 38681698106855167427952965)
                  ·
                    refine ⟨7252818395035343892741181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38681698106855167427952965 7252818395035343892741181)
                    ·
                      refine ⟨2719806898138253959777943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7252818395035343892741181 2719806898138253959777943)
                      ·
                        rfl

theorem cell23_5296805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_5296805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296805 prefixEnd_5296805 := by exact prefixLift 5296805
  have htrace : WordTrace (prefixWord ++ tailWord_5296805) baseStart_5296805 baseEnd_5296805 := by
    simpa [prefixWord, tailWord_5296805, baseEnd_5296805] using wordTrace_append hprefix tailTrace_5296805
  have hstable : (prefixWord ++ tailWord_5296805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296805).length < 2 ^ (prefixWord ++ tailWord_5296805).sum := by decide
  have hdescent : baseEnd_5296805 < baseStart_5296805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296829 : List Nat := [1, 4, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_5296829 : Nat := 118140960795 + 5296829 * 2 ^ 59
def prefixEnd_5296829 : Nat := 4983230072969 + 3 ^ 40 * 5296829 * 2
def baseEnd_5296829 : Nat := 906606407224653955292611

theorem tailTrace_5296829 : CollatzResearch.WordTrace tailWord_5296829 prefixEnd_5296829 906606407224653955292611 := by
  unfold tailWord_5296829
  simp only [CollatzResearch.WordTrace]
  refine ⟨193191224927500634217325541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128794149951667089478217027 193191224927500634217325541)
  ·
    refine ⟨36223354673906368915748539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193191224927500634217325541 36223354673906368915748539)
    ·
      refine ⟨54335032010859553373622809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36223354673906368915748539 54335032010859553373622809)
      ·
        refine ⟨40751274008144665030217107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54335032010859553373622809 40751274008144665030217107)
        ·
          refine ⟨61126911012216997545325661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40751274008144665030217107 61126911012216997545325661)
          ·
            refine ⟨22922591629581374079497123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61126911012216997545325661 22922591629581374079497123)
            ·
              refine ⟨34383887444372061119245685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22922591629581374079497123 34383887444372061119245685)
              ·
                refine ⟨3223489447909880729929283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34383887444372061119245685 3223489447909880729929283)
                ·
                  refine ⟨4835234171864821094893925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3223489447909880729929283 4835234171864821094893925)
                  ·
                    refine ⟨906606407224653955292611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4835234171864821094893925 906606407224653955292611)
                    ·
                      rfl

theorem cell23_5296829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_5296829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296829 prefixEnd_5296829 := by exact prefixLift 5296829
  have htrace : WordTrace (prefixWord ++ tailWord_5296829) baseStart_5296829 baseEnd_5296829 := by
    simpa [prefixWord, tailWord_5296829, baseEnd_5296829] using wordTrace_append hprefix tailTrace_5296829
  have hstable : (prefixWord ++ tailWord_5296829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296829).length < 2 ^ (prefixWord ++ tailWord_5296829).sum := by decide
  have hdescent : baseEnd_5296829 < baseStart_5296829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296842 : List Nat := [3, 1, 2, 1, 4, 1, 3, 2, 6]
def baseStart_5296842 : Nat := 118140960795 + 5296842 * 2 ^ 59
def prefixEnd_5296842 : Nat := 4983230072969 + 3 ^ 40 * 5296842 * 2
def baseEnd_5296842 : Nat := 302202877435830035001697

theorem tailTrace_5296842 : CollatzResearch.WordTrace tailWord_5296842 prefixEnd_5296842 302202877435830035001697 := by
  unfold tailWord_5296842
  simp only [CollatzResearch.WordTrace]
  refine ⟨48297924769113384359387195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128794466050969024958365853 48297924769113384359387195)
  ·
    refine ⟨72446887153670076539080793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48297924769113384359387195 72446887153670076539080793)
    ·
      refine ⟨54335165365252557404310595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72446887153670076539080793 54335165365252557404310595)
      ·
        refine ⟨81502748047878836106465893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54335165365252557404310595 81502748047878836106465893)
        ·
          refine ⟨15281765258977281769962355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81502748047878836106465893 15281765258977281769962355)
          ·
            refine ⟨22922647888465922654943533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15281765258977281769962355 22922647888465922654943533)
            ·
              refine ⟨8595992958174720995603825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22922647888465922654943533 8595992958174720995603825)
              ·
                refine ⟨6446994718631040746702869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8595992958174720995603825 6446994718631040746702869)
                ·
                  refine ⟨302202877435830035001697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6446994718631040746702869 302202877435830035001697)
                  ·
                    rfl

theorem cell23_5296842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_5296842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296842 prefixEnd_5296842 := by exact prefixLift 5296842
  have htrace : WordTrace (prefixWord ++ tailWord_5296842) baseStart_5296842 baseEnd_5296842 := by
    simpa [prefixWord, tailWord_5296842, baseEnd_5296842] using wordTrace_append hprefix tailTrace_5296842
  have hstable : (prefixWord ++ tailWord_5296842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296842).length < 2 ^ (prefixWord ++ tailWord_5296842).sum := by decide
  have hdescent : baseEnd_5296842 < baseStart_5296842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296869 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 3, 1, 3]
def baseStart_5296869 : Nat := 118140960795 + 5296869 * 2 ^ 59
def prefixEnd_5296869 : Nat := 4983230072969 + 3 ^ 40 * 5296869 * 2
def baseEnd_5296869 : Nat := 2719839760900141709377649

theorem tailTrace_5296869 : CollatzResearch.WordTrace tailWord_5296869 prefixEnd_5296869 2719839760900141709377649 := by
  unfold tailWord_5296869
  simp only [CollatzResearch.WordTrace]
  refine ⟨193192683847355721048781661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128795122564903814032521107 193192683847355721048781661)
  ·
    refine ⟨72447256442758395393293123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193192683847355721048781661 72447256442758395393293123)
    ·
      refine ⟨108670884664137593089939685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72447256442758395393293123 108670884664137593089939685)
      ·
        refine ⟨20375790874525798704363691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108670884664137593089939685 20375790874525798704363691)
        ·
          refine ⟨30563686311788698056545537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20375790874525798704363691 30563686311788698056545537)
          ·
            refine ⟨22922764733841523542409153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30563686311788698056545537 22922764733841523542409153)
            ·
              refine ⟨17192073550381142656806865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22922764733841523542409153 17192073550381142656806865)
              ·
                refine ⟨12894055162785856992605149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17192073550381142656806865 12894055162785856992605149)
                ·
                  refine ⟨4835270686044696372226931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12894055162785856992605149 4835270686044696372226931)
                  ·
                    refine ⟨7252906029067044558340397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4835270686044696372226931 7252906029067044558340397)
                    ·
                      refine ⟨2719839760900141709377649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7252906029067044558340397 2719839760900141709377649)
                      ·
                        rfl

theorem cell23_5296869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_5296869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296869 prefixEnd_5296869 := by exact prefixLift 5296869
  have htrace : WordTrace (prefixWord ++ tailWord_5296869) baseStart_5296869 baseEnd_5296869 := by
    simpa [prefixWord, tailWord_5296869, baseEnd_5296869] using wordTrace_append hprefix tailTrace_5296869
  have hstable : (prefixWord ++ tailWord_5296869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296869).length < 2 ^ (prefixWord ++ tailWord_5296869).sum := by decide
  have hdescent : baseEnd_5296869 < baseStart_5296869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296905 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 6]
def baseStart_5296905 : Nat := 118140960795 + 5296905 * 2 ^ 59
def prefixEnd_5296905 : Nat := 4983230072969 + 3 ^ 40 * 5296905 * 2
def baseEnd_5296905 : Nat := 2719858246203703568527483

theorem tailTrace_5296905 : CollatzResearch.WordTrace tailWord_5296905 prefixEnd_5296905 2719858246203703568527483 := by
  unfold tailWord_5296905
  simp only [CollatzResearch.WordTrace]
  refine ⟨193193996875225299197092169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128795997916816866131394779 193193996875225299197092169)
  ·
    refine ⟨144895497656418974397819127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193193996875225299197092169 144895497656418974397819127)
    ·
      refine ⟨217343246484628461596728691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144895497656418974397819127 217343246484628461596728691)
      ·
        refine ⟨326014869726942692395093037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217343246484628461596728691 326014869726942692395093037)
        ·
          refine ⟨122255576147603509648159889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326014869726942692395093037 122255576147603509648159889)
          ·
            refine ⟨91691682110702632236119917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122255576147603509648159889 91691682110702632236119917)
            ·
              refine ⟨34384380791513487088544969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91691682110702632236119917 34384380791513487088544969)
              ·
                refine ⟨25788285593635115316408727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34384380791513487088544969 25788285593635115316408727)
                ·
                  refine ⟨38682428390452672974613091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25788285593635115316408727 38682428390452672974613091)
                  ·
                    refine ⟨58023642585679009461919637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38682428390452672974613091 58023642585679009461919637)
                    ·
                      refine ⟨2719858246203703568527483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58023642585679009461919637 2719858246203703568527483)
                      ·
                        rfl

theorem cell23_5296905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_5296905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296905 prefixEnd_5296905 := by exact prefixLift 5296905
  have htrace : WordTrace (prefixWord ++ tailWord_5296905) baseStart_5296905 baseEnd_5296905 := by
    simpa [prefixWord, tailWord_5296905, baseEnd_5296905] using wordTrace_append hprefix tailTrace_5296905
  have hstable : (prefixWord ++ tailWord_5296905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296905).length < 2 ^ (prefixWord ++ tailWord_5296905).sum := by decide
  have hdescent : baseEnd_5296905 < baseStart_5296905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296915 : List Nat := [1, 1, 1, 2, 1, 3, 6, 8]
def baseStart_5296915 : Nat := 118140960795 + 5296915 * 2 ^ 59
def prefixEnd_5296915 : Nat := 4983230072969 + 3 ^ 40 * 5296915 * 2
def baseEnd_5296915 : Nat := 100735680778157352940831

theorem tailTrace_5296915 : CollatzResearch.WordTrace tailWord_5296915 prefixEnd_5296915 100735680778157352940831 := by
  unfold tailWord_5296915
  simp only [CollatzResearch.WordTrace]
  refine ⟨193194361605189070904956199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128796241070126047269970799 193194361605189070904956199)
  ·
    refine ⟨289791542407783606357434299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193194361605189070904956199 289791542407783606357434299)
    ·
      refine ⟨434687313611675409536151449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289791542407783606357434299 434687313611675409536151449)
      ·
        refine ⟨326015485208756557152113587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434687313611675409536151449 326015485208756557152113587)
        ·
          refine ⟨489023227813134835728170381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326015485208756557152113587 489023227813134835728170381)
          ·
            refine ⟨183383710429925563398063893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 489023227813134835728170381 183383710429925563398063893)
            ·
              refine ⟨8596111426402760784284245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 183383710429925563398063893 8596111426402760784284245)
              ·
                refine ⟨100735680778157352940831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8596111426402760784284245 100735680778157352940831)
                ·
                  rfl

theorem cell23_5296915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 8].length) (baseStart_5296915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296915 prefixEnd_5296915 := by exact prefixLift 5296915
  have htrace : WordTrace (prefixWord ++ tailWord_5296915) baseStart_5296915 baseEnd_5296915 := by
    simpa [prefixWord, tailWord_5296915, baseEnd_5296915] using wordTrace_append hprefix tailTrace_5296915
  have hstable : (prefixWord ++ tailWord_5296915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296915).length < 2 ^ (prefixWord ++ tailWord_5296915).sum := by decide
  have hdescent : baseEnd_5296915 < baseStart_5296915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296922 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_5296922 : Nat := 118140960795 + 5296922 * 2 ^ 59
def prefixEnd_5296922 : Nat := 4983230072969 + 3 ^ 40 * 5296922 * 2
def baseEnd_5296922 : Nat := 2719866975374830002014905

theorem tailTrace_5296922 : CollatzResearch.WordTrace tailWord_5296922 prefixEnd_5296922 2719866975374830002014905 := by
  unfold tailWord_5296922
  simp only [CollatzResearch.WordTrace]
  refine ⟨48298654229040927775115255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128796411277442474066974013 48298654229040927775115255)
  ·
    refine ⟨72447981343561391662672883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48298654229040927775115255 72447981343561391662672883)
    ·
      refine ⟨108671972015342087494009325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72447981343561391662672883 108671972015342087494009325)
      ·
        refine ⟨40751989505753282810253497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108671972015342087494009325 40751989505753282810253497)
        ·
          refine ⟨30563992129314962107690123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40751989505753282810253497 30563992129314962107690123)
          ·
            refine ⟨45845988193972443161535185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30563992129314962107690123 45845988193972443161535185)
            ·
              refine ⟨34384491145479332371151389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45845988193972443161535185 34384491145479332371151389)
              ·
                refine ⟨12894184179554749639181771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34384491145479332371151389 12894184179554749639181771)
                ·
                  refine ⟨19341276269332124458772657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12894184179554749639181771 19341276269332124458772657)
                  ·
                    refine ⟨14505957201999093344079493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19341276269332124458772657 14505957201999093344079493)
                    ·
                      refine ⟨2719866975374830002014905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14505957201999093344079493 2719866975374830002014905)
                      ·
                        rfl

theorem cell23_5296922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_5296922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296922 prefixEnd_5296922 := by exact prefixLift 5296922
  have htrace : WordTrace (prefixWord ++ tailWord_5296922) baseStart_5296922 baseEnd_5296922 := by
    simpa [prefixWord, tailWord_5296922, baseEnd_5296922] using wordTrace_append hprefix tailTrace_5296922
  have hstable : (prefixWord ++ tailWord_5296922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296922).length < 2 ^ (prefixWord ++ tailWord_5296922).sum := by decide
  have hdescent : baseEnd_5296922 < baseStart_5296922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296946 : List Nat := [3, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3]
def baseStart_5296946 : Nat := 118140960795 + 5296946 * 2 ^ 59
def prefixEnd_5296946 : Nat := 4983230072969 + 3 ^ 40 * 5296946 * 2
def baseEnd_5296946 : Nat := 2719879298910537908114795

theorem tailTrace_5296946 : CollatzResearch.WordTrace tailWord_5296946 prefixEnd_5296946 2719879298910537908114795 := by
  unfold tailWord_5296946
  simp only [CollatzResearch.WordTrace]
  refine ⟨48298873067019190799833673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128796994845384508799556461 48298873067019190799833673)
  ·
    refine ⟨36224154800264393099875255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48298873067019190799833673 36224154800264393099875255)
    ·
      refine ⟨54336232200396589649812883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36224154800264393099875255 54336232200396589649812883)
      ·
        refine ⟨81504348300594884474719325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54336232200396589649812883 81504348300594884474719325)
        ·
          refine ⟨30564130612723081678019747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81504348300594884474719325 30564130612723081678019747)
          ·
            refine ⟨45846195919084622517029621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30564130612723081678019747 45846195919084622517029621)
            ·
              refine ⟨4298080867414183360971527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45846195919084622517029621 4298080867414183360971527)
              ·
                refine ⟨6447121301121275041457291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4298080867414183360971527 6447121301121275041457291)
                ·
                  refine ⟨9670681951681912562185937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6447121301121275041457291 9670681951681912562185937)
                  ·
                    refine ⟨7253011463761434421639453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9670681951681912562185937 7253011463761434421639453)
                    ·
                      refine ⟨2719879298910537908114795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7253011463761434421639453 2719879298910537908114795)
                      ·
                        rfl

theorem cell23_5296946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_5296946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296946 prefixEnd_5296946 := by exact prefixLift 5296946
  have htrace : WordTrace (prefixWord ++ tailWord_5296946) baseStart_5296946 baseEnd_5296946 := by
    simpa [prefixWord, tailWord_5296946, baseEnd_5296946] using wordTrace_append hprefix tailTrace_5296946
  have hstable : (prefixWord ++ tailWord_5296946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296946).length < 2 ^ (prefixWord ++ tailWord_5296946).sum := by decide
  have hdescent : baseEnd_5296946 < baseStart_5296946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5296969 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 3, 3, 2]
def baseStart_5296969 : Nat := 118140960795 + 5296969 * 2 ^ 59
def prefixEnd_5296969 : Nat := 4983230072969 + 3 ^ 40 * 5296969 * 2
def baseEnd_5296969 : Nat := 2719891108965591318127189

theorem tailTrace_5296969 : CollatzResearch.WordTrace tailWord_5296969 prefixEnd_5296969 2719891108965591318127189 := by
  unfold tailWord_5296969
  simp only [CollatzResearch.WordTrace]
  refine ⟨193196331146993438127421961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128797554097995625418281307 193196331146993438127421961)
  ·
    refine ⟨144897248360245078595566471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193196331146993438127421961 144897248360245078595566471)
    ·
      refine ⟨217345872540367617893349707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144897248360245078595566471 217345872540367617893349707)
      ·
        refine ⟨326018808810551426840024561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217345872540367617893349707 326018808810551426840024561)
        ·
          refine ⟨244514106607913570130018421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326018808810551426840024561 244514106607913570130018421)
          ·
            refine ⟨22923197494491897199689227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 244514106607913570130018421 22923197494491897199689227)
            ·
              refine ⟨34384796241737845799533841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22923197494491897199689227 34384796241737845799533841)
              ·
                refine ⟨25788597181303384349650381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34384796241737845799533841 25788597181303384349650381)
                ·
                  refine ⟨9670723942988769131118893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25788597181303384349650381 9670723942988769131118893)
                  ·
                    refine ⟨3626521478620788424169585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9670723942988769131118893 3626521478620788424169585)
                    ·
                      refine ⟨2719891108965591318127189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3626521478620788424169585 2719891108965591318127189)
                      ·
                        rfl

theorem cell23_5296969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 3, 2].length) (baseStart_5296969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5296969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5296969 prefixEnd_5296969 := by exact prefixLift 5296969
  have htrace : WordTrace (prefixWord ++ tailWord_5296969) baseStart_5296969 baseEnd_5296969 := by
    simpa [prefixWord, tailWord_5296969, baseEnd_5296969] using wordTrace_append hprefix tailTrace_5296969
  have hstable : (prefixWord ++ tailWord_5296969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5296969).length < 2 ^ (prefixWord ++ tailWord_5296969).sum := by decide
  have hdescent : baseEnd_5296969 < baseStart_5296969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5296969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297016 : List Nat := [2, 1, 2, 1, 1, 1, 1, 8, 2, 2, 2]
def baseStart_5297016 : Nat := 118140960795 + 5297016 * 2 ^ 59
def prefixEnd_5297016 : Nat := 4983230072969 + 3 ^ 40 * 5297016 * 2
def baseEnd_5297016 : Nat := 2719915242556352634239473

theorem tailTrace_5297016 : CollatzResearch.WordTrace tailWord_5297016 prefixEnd_5297016 2719915242556352634239473 := by
  unfold tailWord_5297016
  simp only [CollatzResearch.WordTrace]
  refine ⟨96599022688911582577191451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128798696918548776769588601 96599022688911582577191451)
  ·
    refine ⟨144898534033367373865787177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96599022688911582577191451 144898534033367373865787177)
    ·
      refine ⟨108673900525025530399340383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144898534033367373865787177 108673900525025530399340383)
      ·
        refine ⟨163010850787538295599010575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108673900525025530399340383 163010850787538295599010575)
        ·
          refine ⟨244516276181307443398515863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163010850787538295599010575 244516276181307443398515863)
          ·
            refine ⟨366774414271961165097773795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244516276181307443398515863 366774414271961165097773795)
            ·
              refine ⟨550161621407941747646660693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366774414271961165097773795 550161621407941747646660693)
              ·
                refine ⟨6447206500874317355234305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 550161621407941747646660693 6447206500874317355234305)
                ·
                  refine ⟨4835404875655738016425729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6447206500874317355234305 4835404875655738016425729)
                  ·
                    refine ⟨3626553656741803512319297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4835404875655738016425729 3626553656741803512319297)
                    ·
                      refine ⟨2719915242556352634239473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3626553656741803512319297 2719915242556352634239473)
                      ·
                        rfl

theorem cell23_5297016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 2, 2, 2].length) (baseStart_5297016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297016 prefixEnd_5297016 := by exact prefixLift 5297016
  have htrace : WordTrace (prefixWord ++ tailWord_5297016) baseStart_5297016 baseEnd_5297016 := by
    simpa [prefixWord, tailWord_5297016, baseEnd_5297016] using wordTrace_append hprefix tailTrace_5297016
  have hstable : (prefixWord ++ tailWord_5297016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297016).length < 2 ^ (prefixWord ++ tailWord_5297016).sum := by decide
  have hdescent : baseEnd_5297016 < baseStart_5297016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297073 : List Nat := [1, 2, 2, 4, 3, 1, 3, 2, 5]
def baseStart_5297073 : Nat := 118140960795 + 5297073 * 2 ^ 59
def prefixEnd_5297073 : Nat := 4983230072969 + 3 ^ 40 * 5297073 * 2
def baseEnd_5297073 : Nat := 302216056772628767914079

theorem tailTrace_5297073 : CollatzResearch.WordTrace tailWord_5297073 prefixEnd_5297073 302216056772628767914079 := by
  unfold tailWord_5297073
  simp only [CollatzResearch.WordTrace]
  refine ⟨193200124338616663889207873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128800082892411109259471915 193200124338616663889207873)
  ·
    refine ⟨144900093253962497916905905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193200124338616663889207873 144900093253962497916905905)
    ·
      refine ⟨108675069940471873437679429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144900093253962497916905905 108675069940471873437679429)
      ·
        refine ⟨20376575613838476269564893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108675069940471873437679429 20376575613838476269564893)
        ·
          refine ⟨7641215855189428601086835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20376575613838476269564893 7641215855189428601086835)
          ·
            refine ⟨11461823782784142901630253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7641215855189428601086835 11461823782784142901630253)
            ·
              refine ⟨4298183918544053588111345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11461823782784142901630253 4298183918544053588111345)
              ·
                refine ⟨3223637938908040191083509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4298183918544053588111345 3223637938908040191083509)
                ·
                  refine ⟨302216056772628767914079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3223637938908040191083509 302216056772628767914079)
                  ·
                    rfl

theorem cell23_5297073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 5].length) (baseStart_5297073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297073 prefixEnd_5297073 := by exact prefixLift 5297073
  have htrace : WordTrace (prefixWord ++ tailWord_5297073) baseStart_5297073 baseEnd_5297073 := by
    simpa [prefixWord, tailWord_5297073, baseEnd_5297073] using wordTrace_append hprefix tailTrace_5297073
  have hstable : (prefixWord ++ tailWord_5297073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297073).length < 2 ^ (prefixWord ++ tailWord_5297073).sum := by decide
  have hdescent : baseEnd_5297073 < baseStart_5297073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297106 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_5297106 : Nat := 118140960795 + 5297106 * 2 ^ 59
def prefixEnd_5297106 : Nat := 4983230072969 + 3 ^ 40 * 5297106 * 2
def baseEnd_5297106 : Nat := 2719961455815257282114059

theorem tailTrace_5297106 : CollatzResearch.WordTrace tailWord_5297106 prefixEnd_5297106 2719961455815257282114059 := by
  unfold tailWord_5297106
  simp only [CollatzResearch.WordTrace]
  refine ⟨48300331986874277631289793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128800885298331407016772781 48300331986874277631289793)
  ·
    refine ⟨36225248990155708223467345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48300331986874277631289793 36225248990155708223467345)
    ·
      refine ⟨27168936742616781167600509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36225248990155708223467345 27168936742616781167600509)
      ·
        refine ⟨10188351278481292937850191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27168936742616781167600509 10188351278481292937850191)
        ·
          refine ⟨15282526917721939406775287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10188351278481292937850191 15282526917721939406775287)
          ·
            refine ⟨22923790376582909110162931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15282526917721939406775287 22923790376582909110162931)
            ·
              refine ⟨34385685564874363665244397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22923790376582909110162931 34385685564874363665244397)
              ·
                refine ⟨12894632086827886374466649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34385685564874363665244397 12894632086827886374466649)
                ·
                  refine ⟨9670974065120914780849987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12894632086827886374466649 9670974065120914780849987)
                  ·
                    refine ⟨14506461097681372171274981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9670974065120914780849987 14506461097681372171274981)
                    ·
                      refine ⟨2719961455815257282114059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14506461097681372171274981 2719961455815257282114059)
                      ·
                        rfl

theorem cell23_5297106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_5297106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297106 prefixEnd_5297106 := by exact prefixLift 5297106
  have htrace : WordTrace (prefixWord ++ tailWord_5297106) baseStart_5297106 baseEnd_5297106 := by
    simpa [prefixWord, tailWord_5297106, baseEnd_5297106] using wordTrace_append hprefix tailTrace_5297106
  have hstable : (prefixWord ++ tailWord_5297106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297106).length < 2 ^ (prefixWord ++ tailWord_5297106).sum := by decide
  have hdescent : baseEnd_5297106 < baseStart_5297106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297152 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 5]
def baseStart_5297152 : Nat := 118140960795 + 5297152 * 2 ^ 59
def prefixEnd_5297152 : Nat := 4983230072969 + 3 ^ 40 * 5297152 * 2
def baseEnd_5297152 : Nat := 2719985075925364102138847

theorem tailTrace_5297152 : CollatzResearch.WordTrace tailWord_5297152 prefixEnd_5297152 2719985075925364102138847 := by
  unfold tailWord_5297152
  simp only [CollatzResearch.WordTrace]
  refine ⟨96601502852665230190666855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128802003803553640254222473 96601502852665230190666855)
  ·
    refine ⟨144902254278997845286000283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96601502852665230190666855 144902254278997845286000283)
    ·
      refine ⟨217353381418496767929000425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144902254278997845286000283 217353381418496767929000425)
      ·
        refine ⟨163015036063872575946750319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217353381418496767929000425 163015036063872575946750319)
        ·
          refine ⟨244522554095808863920125479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163015036063872575946750319 244522554095808863920125479)
          ·
            refine ⟨366783831143713295880188219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244522554095808863920125479 366783831143713295880188219)
            ·
              refine ⟨550175746715569943820282329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366783831143713295880188219 550175746715569943820282329)
              ·
                refine ⟨412631810036677457865211747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550175746715569943820282329 412631810036677457865211747)
                ·
                  refine ⟨618947715055016186797817621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412631810036677457865211747 618947715055016186797817621)
                  ·
                    refine ⟨29013174143203883756147701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 618947715055016186797817621 29013174143203883756147701)
                    ·
                      refine ⟨2719985075925364102138847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29013174143203883756147701 2719985075925364102138847)
                      ·
                        rfl

theorem cell23_5297152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_5297152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297152 prefixEnd_5297152 := by exact prefixLift 5297152
  have htrace : WordTrace (prefixWord ++ tailWord_5297152) baseStart_5297152 baseEnd_5297152 := by
    simpa [prefixWord, tailWord_5297152, baseEnd_5297152] using wordTrace_append hprefix tailTrace_5297152
  have hstable : (prefixWord ++ tailWord_5297152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297152).length < 2 ^ (prefixWord ++ tailWord_5297152).sum := by decide
  have hdescent : baseEnd_5297152 < baseStart_5297152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297159 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 3, 5]
def baseStart_5297159 : Nat := 118140960795 + 5297159 * 2 ^ 59
def prefixEnd_5297159 : Nat := 4983230072969 + 3 ^ 40 * 5297159 * 2
def baseEnd_5297159 : Nat := 906662890096648524917105

theorem tailTrace_5297159 : CollatzResearch.WordTrace tailWord_5297159 prefixEnd_5297159 906662890096648524917105 := by
  unfold tailWord_5297159
  simp only [CollatzResearch.WordTrace]
  refine ⟨193203261016305100576838531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128802174010870067051225687 193203261016305100576838531)
  ·
    refine ⟨289804891524457650865257797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193203261016305100576838531 289804891524457650865257797)
    ·
      refine ⟨54338417160835809537235837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289804891524457650865257797 54338417160835809537235837)
      ·
        refine ⟨20376906435313428576463439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54338417160835809537235837 20376906435313428576463439)
        ·
          refine ⟨30565359652970142864695159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20376906435313428576463439 30565359652970142864695159)
          ·
            refine ⟨45848039479455214297042739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30565359652970142864695159 45848039479455214297042739)
            ·
              refine ⟨68772059219182821445564109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45848039479455214297042739 68772059219182821445564109)
              ·
                refine ⟨25789522207193558042086541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68772059219182821445564109 25789522207193558042086541)
                ·
                  refine ⟨9671070827697584265782453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25789522207193558042086541 9671070827697584265782453)
                  ·
                    refine ⟨906662890096648524917105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9671070827697584265782453 906662890096648524917105)
                    ·
                      rfl

theorem cell23_5297159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_5297159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297159 prefixEnd_5297159 := by exact prefixLift 5297159
  have htrace : WordTrace (prefixWord ++ tailWord_5297159) baseStart_5297159 baseEnd_5297159 := by
    simpa [prefixWord, tailWord_5297159, baseEnd_5297159] using wordTrace_append hprefix tailTrace_5297159
  have hstable : (prefixWord ++ tailWord_5297159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297159).length < 2 ^ (prefixWord ++ tailWord_5297159).sum := by decide
  have hdescent : baseEnd_5297159 < baseStart_5297159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297176 : List Nat := [2, 1, 2, 3, 2, 3, 1, 3, 1, 5]
def baseStart_5297176 : Nat := 118140960795 + 5297176 * 2 ^ 59
def prefixEnd_5297176 : Nat := 4983230072969 + 3 ^ 40 * 5297176 * 2
def baseEnd_5297176 : Nat := 906665799820357336079579

theorem tailTrace_5297176 : CollatzResearch.WordTrace tailWord_5297176 prefixEnd_5297176 906665799820357336079579 := by
  unfold tailWord_5297176
  simp only [CollatzResearch.WordTrace]
  refine ⟨96601940528621756240103691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128802587371495674986804921 96601940528621756240103691)
  ·
    refine ⟨144902910792932634360155537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96601940528621756240103691 144902910792932634360155537)
    ·
      refine ⟨108677183094699475770116653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144902910792932634360155537 108677183094699475770116653)
      ·
        refine ⟨40753943660512303413793745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108677183094699475770116653 40753943660512303413793745)
        ·
          refine ⟨30565457745384227560345309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40753943660512303413793745 30565457745384227560345309)
          ·
            refine ⟨11462046654519085335129491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30565457745384227560345309 11462046654519085335129491)
            ·
              refine ⟨17193069981778628002694237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11462046654519085335129491 17193069981778628002694237)
              ·
                refine ⟨6447401243166985501010339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17193069981778628002694237 6447401243166985501010339)
                ·
                  refine ⟨9671101864750478251515509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6447401243166985501010339 9671101864750478251515509)
                  ·
                    refine ⟨906665799820357336079579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9671101864750478251515509 906665799820357336079579)
                    ·
                      rfl

theorem cell23_5297176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_5297176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297176 prefixEnd_5297176 := by exact prefixLift 5297176
  have htrace : WordTrace (prefixWord ++ tailWord_5297176) baseStart_5297176 baseEnd_5297176 := by
    simpa [prefixWord, tailWord_5297176, baseEnd_5297176] using wordTrace_append hprefix tailTrace_5297176
  have hstable : (prefixWord ++ tailWord_5297176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297176).length < 2 ^ (prefixWord ++ tailWord_5297176).sum := by decide
  have hdescent : baseEnd_5297176 < baseStart_5297176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297213 : List Nat := [1, 4, 1, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_5297213 : Nat := 118140960795 + 5297213 * 2 ^ 59
def prefixEnd_5297213 : Nat := 4983230072969 + 3 ^ 40 * 5297213 * 2
def baseEnd_5297213 : Nat := 2720016398245288363476067

theorem tailTrace_5297213 : CollatzResearch.WordTrace tailWord_5297213 prefixEnd_5297213 2720016398245288363476067 := by
  unfold tailWord_5297213
  simp only [CollatzResearch.WordTrace]
  refine ⟨193205230558109467799304293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128803487038739645199536195 193205230558109467799304293)
  ·
    refine ⟨36225980729645525212369555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193205230558109467799304293 36225980729645525212369555)
    ·
      refine ⟨54338971094468287818554333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36225980729645525212369555 54338971094468287818554333)
      ·
        refine ⟨20377114160425607931957875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54338971094468287818554333 20377114160425607931957875)
        ·
          refine ⟨30565671240638411897936813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20377114160425607931957875 30565671240638411897936813)
          ·
            refine ⟨11462126715239404461726305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30565671240638411897936813 11462126715239404461726305)
            ·
              refine ⟨8596595036429553346294729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11462126715239404461726305 8596595036429553346294729)
              ·
                refine ⟨6447446277322165009721047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8596595036429553346294729 6447446277322165009721047)
                ·
                  refine ⟨9671169415983247514581571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6447446277322165009721047 9671169415983247514581571)
                  ·
                    refine ⟨14506754123974871271872357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9671169415983247514581571 14506754123974871271872357)
                    ·
                      refine ⟨2720016398245288363476067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14506754123974871271872357 2720016398245288363476067)
                      ·
                        rfl

theorem cell23_5297213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_5297213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297213 prefixEnd_5297213 := by exact prefixLift 5297213
  have htrace : WordTrace (prefixWord ++ tailWord_5297213) baseStart_5297213 baseEnd_5297213 := by
    simpa [prefixWord, tailWord_5297213, baseEnd_5297213] using wordTrace_append hprefix tailTrace_5297213
  have hstable : (prefixWord ++ tailWord_5297213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297213).length < 2 ^ (prefixWord ++ tailWord_5297213).sum := by decide
  have hdescent : baseEnd_5297213 < baseStart_5297213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297247 : List Nat := [1, 1, 2, 3, 1, 1, 7, 2, 1, 2, 2]
def baseStart_5297247 : Nat := 118140960795 + 5297247 * 2 ^ 59
def prefixEnd_5297247 : Nat := 4983230072969 + 3 ^ 40 * 5297247 * 2
def baseEnd_5297247 : Nat := 2720033856587541230450911

theorem tailTrace_5297247 : CollatzResearch.WordTrace tailWord_5297247 prefixEnd_5297247 2720033856587541230450911 := by
  unfold tailWord_5297247
  simp only [CollatzResearch.WordTrace]
  refine ⟨193206470639986291606041995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128804313759990861070694663 193206470639986291606041995)
  ·
    refine ⟨289809705959979437409062993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193206470639986291606041995 289809705959979437409062993)
    ·
      refine ⟨217357279469984578056797245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289809705959979437409062993 217357279469984578056797245)
      ·
        refine ⟨81508979801244216771298967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217357279469984578056797245 81508979801244216771298967)
        ·
          refine ⟨122263469701866325156948451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81508979801244216771298967 122263469701866325156948451)
          ·
            refine ⟨183395204552799487735422677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122263469701866325156948451 183395204552799487735422677)
            ·
              refine ⟨4298325106706237993798969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 183395204552799487735422677 4298325106706237993798969)
              ·
                refine ⟨3223743830029678495349227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4298325106706237993798969 3223743830029678495349227)
                ·
                  refine ⟨4835615745044517743023841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3223743830029678495349227 4835615745044517743023841)
                  ·
                    refine ⟨3626711808783388307267881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4835615745044517743023841 3626711808783388307267881)
                    ·
                      refine ⟨2720033856587541230450911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3626711808783388307267881 2720033856587541230450911)
                      ·
                        rfl

theorem cell23_5297247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_5297247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297247 prefixEnd_5297247 := by exact prefixLift 5297247
  have htrace : WordTrace (prefixWord ++ tailWord_5297247) baseStart_5297247 baseEnd_5297247 := by
    simpa [prefixWord, tailWord_5297247, baseEnd_5297247] using wordTrace_append hprefix tailTrace_5297247
  have hstable : (prefixWord ++ tailWord_5297247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297247).length < 2 ^ (prefixWord ++ tailWord_5297247).sum := by decide
  have hdescent : baseEnd_5297247 < baseStart_5297247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297263 : List Nat := [1, 1, 2, 1, 3, 3, 3, 3, 2, 1, 3]
def baseStart_5297263 : Nat := 118140960795 + 5297263 * 2 ^ 59
def prefixEnd_5297263 : Nat := 4983230072969 + 3 ^ 40 * 5297263 * 2
def baseEnd_5297263 : Nat := 2720042072278013167850837

theorem tailTrace_5297263 : CollatzResearch.WordTrace tailWord_5297263 prefixEnd_5297263 2720042072278013167850837 := by
  unfold tailWord_5297263
  simp only [CollatzResearch.WordTrace]
  refine ⟨193207054207928326338624443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128804702805285550892416295 193207054207928326338624443)
  ·
    refine ⟨289810581311892489507936665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193207054207928326338624443 289810581311892489507936665)
    ·
      refine ⟨217357935983919367130952499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289810581311892489507936665 217357935983919367130952499)
      ·
        refine ⟨326036903975879050696428749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217357935983919367130952499 326036903975879050696428749)
        ·
          refine ⟨122263838990954644011160781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326036903975879050696428749 122263838990954644011160781)
          ·
            refine ⟨45848939621607991504185293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122263838990954644011160781 45848939621607991504185293)
            ·
              refine ⟨17193352358102996814069485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45848939621607991504185293 17193352358102996814069485)
              ·
                refine ⟨6447507134288623805276057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17193352358102996814069485 6447507134288623805276057)
                ·
                  refine ⟨4835630350716467853957043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6447507134288623805276057 4835630350716467853957043)
                  ·
                    refine ⟨7253445526074701780935565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4835630350716467853957043 7253445526074701780935565)
                    ·
                      refine ⟨2720042072278013167850837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7253445526074701780935565 2720042072278013167850837)
                      ·
                        rfl

theorem cell23_5297263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 1, 3].length) (baseStart_5297263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297263 prefixEnd_5297263 := by exact prefixLift 5297263
  have htrace : WordTrace (prefixWord ++ tailWord_5297263) baseStart_5297263 baseEnd_5297263 := by
    simpa [prefixWord, tailWord_5297263, baseEnd_5297263] using wordTrace_append hprefix tailTrace_5297263
  have hstable : (prefixWord ++ tailWord_5297263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297263).length < 2 ^ (prefixWord ++ tailWord_5297263).sum := by decide
  have hdescent : baseEnd_5297263 < baseStart_5297263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297316 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_5297316 : Nat := 118140960795 + 5297316 * 2 ^ 59
def prefixEnd_5297316 : Nat := 4983230072969 + 3 ^ 40 * 5297316 * 2
def baseEnd_5297316 : Nat := 2720069286752701460488093

theorem tailTrace_5297316 : CollatzResearch.WordTrace tailWord_5297316 prefixEnd_5297316 2720069286752701460488093 := by
  unfold tailWord_5297316
  simp only [CollatzResearch.WordTrace]
  refine ⟨96604493638368158195151901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128805991517824210926869201 96604493638368158195151901)
  ·
    refine ⟨36226685114388059323181963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96604493638368158195151901 36226685114388059323181963)
    ·
      refine ⟨54340027671582088984772945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36226685114388059323181963 54340027671582088984772945)
      ·
        refine ⟨40755020753686566738579709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54340027671582088984772945 40755020753686566738579709)
        ·
          refine ⟨15283132782632462526967391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40755020753686566738579709 15283132782632462526967391)
          ·
            refine ⟨22924699173948693790451087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15283132782632462526967391 22924699173948693790451087)
            ·
              refine ⟨34387048760923040685676631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22924699173948693790451087 34387048760923040685676631)
              ·
                refine ⟨51580573141384561028514947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34387048760923040685676631 51580573141384561028514947)
                ·
                  refine ⟨77370859712076841542772421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51580573141384561028514947 77370859712076841542772421)
                  ·
                    refine ⟨14507036196014407789269829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77370859712076841542772421 14507036196014407789269829)
                    ·
                      refine ⟨2720069286752701460488093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14507036196014407789269829 2720069286752701460488093)
                      ·
                        rfl

theorem cell23_5297316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_5297316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297316 prefixEnd_5297316 := by exact prefixLift 5297316
  have htrace : WordTrace (prefixWord ++ tailWord_5297316) baseStart_5297316 baseEnd_5297316 := by
    simpa [prefixWord, tailWord_5297316, baseEnd_5297316] using wordTrace_append hprefix tailTrace_5297316
  have hstable : (prefixWord ++ tailWord_5297316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297316).length < 2 ^ (prefixWord ++ tailWord_5297316).sum := by decide
  have hdescent : baseEnd_5297316 < baseStart_5297316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297376 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 4]
def baseStart_5297376 : Nat := 118140960795 + 5297376 * 2 ^ 59
def prefixEnd_5297376 : Nat := 4983230072969 + 3 ^ 40 * 5297376 * 2
def baseEnd_5297376 : Nat := 2720100095591971225737817

theorem tailTrace_5297376 : CollatzResearch.WordTrace tailWord_5297376 prefixEnd_5297376 2720100095591971225737817 := by
  unfold tailWord_5297376
  simp only [CollatzResearch.WordTrace]
  refine ⟨96605587828259473318743991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128807450437679297758325321 96605587828259473318743991)
  ·
    refine ⟨144908381742389209978115987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96605587828259473318743991 144908381742389209978115987)
    ·
      refine ⟨217362572613583814967173981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144908381742389209978115987 217362572613583814967173981)
      ·
        refine ⟨81510964730093930612690243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217362572613583814967173981 81510964730093930612690243)
        ·
          refine ⟨122266447095140895919035365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81510964730093930612690243 122266447095140895919035365)
          ·
            refine ⟨22924958830338917984819131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122266447095140895919035365 22924958830338917984819131)
            ·
              refine ⟨34387438245508376977228697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22924958830338917984819131 34387438245508376977228697)
              ·
                refine ⟨25790578684131282732921523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34387438245508376977228697 25790578684131282732921523)
                ·
                  refine ⟨38685868026196924099382285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25790578684131282732921523 38685868026196924099382285)
                  ·
                    refine ⟨14507200509823846537268357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38685868026196924099382285 14507200509823846537268357)
                    ·
                      refine ⟨2720100095591971225737817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14507200509823846537268357 2720100095591971225737817)
                      ·
                        rfl

theorem cell23_5297376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_5297376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297376 prefixEnd_5297376 := by exact prefixLift 5297376
  have htrace : WordTrace (prefixWord ++ tailWord_5297376) baseStart_5297376 baseEnd_5297376 := by
    simpa [prefixWord, tailWord_5297376, baseEnd_5297376] using wordTrace_append hprefix tailTrace_5297376
  have hstable : (prefixWord ++ tailWord_5297376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297376).length < 2 ^ (prefixWord ++ tailWord_5297376).sum := by decide
  have hdescent : baseEnd_5297376 < baseStart_5297376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297413 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 2, 2, 3]
def baseStart_5297413 : Nat := 118140960795 + 5297413 * 2 ^ 59
def prefixEnd_5297413 : Nat := 4983230072969 + 3 ^ 40 * 5297413 * 2
def baseEnd_5297413 : Nat := 2720119094376187580975147

theorem tailTrace_5297413 : CollatzResearch.WordTrace tailWord_5297413 prefixEnd_5297413 2720119094376187580975147 := by
  unfold tailWord_5297413
  simp only [CollatzResearch.WordTrace]
  refine ⟨193212525157384901956584893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128808350104923267971056595 193212525157384901956584893)
  ·
    refine ⟨72454696934019338233719335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193212525157384901956584893 72454696934019338233719335)
    ·
      refine ⟨108682045401029007350579003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72454696934019338233719335 108682045401029007350579003)
      ·
        refine ⟨163023068101543511025868505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108682045401029007350579003 163023068101543511025868505)
        ·
          refine ⟨122267301076157633269401379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163023068101543511025868505 122267301076157633269401379)
          ·
            refine ⟨183400951614236449904102069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122267301076157633269401379 183400951614236449904102069)
            ·
              refine ⟨17193839213834667178509569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 183400951614236449904102069 17193839213834667178509569)
              ·
                refine ⟨12895379410376000383882177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17193839213834667178509569 12895379410376000383882177)
                ·
                  refine ⟨9671534557782000287911633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12895379410376000383882177 9671534557782000287911633)
                  ·
                    refine ⟨7253650918336500215933725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9671534557782000287911633 7253650918336500215933725)
                    ·
                      refine ⟨2720119094376187580975147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7253650918336500215933725 2720119094376187580975147)
                      ·
                        rfl

theorem cell23_5297413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_5297413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297413 prefixEnd_5297413 := by exact prefixLift 5297413
  have htrace : WordTrace (prefixWord ++ tailWord_5297413) baseStart_5297413 baseEnd_5297413 := by
    simpa [prefixWord, tailWord_5297413, baseEnd_5297413] using wordTrace_append hprefix tailTrace_5297413
  have hstable : (prefixWord ++ tailWord_5297413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297413).length < 2 ^ (prefixWord ++ tailWord_5297413).sum := by decide
  have hdescent : baseEnd_5297413 < baseStart_5297413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297420 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 3, 4]
def baseStart_5297420 : Nat := 118140960795 + 5297420 * 2 ^ 59
def prefixEnd_5297420 : Nat := 4983230072969 + 3 ^ 40 * 5297420 * 2
def baseEnd_5297420 : Nat := 906707562913589684529205

theorem tailTrace_5297420 : CollatzResearch.WordTrace tailWord_5297420 prefixEnd_5297420 906707562913589684529205 := by
  unfold tailWord_5297420
  simp only [CollatzResearch.WordTrace]
  refine ⟨96606390234179771076044857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128808520312239694768059809 96606390234179771076044857)
  ·
    refine ⟨72454792675634828307033643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96606390234179771076044857 72454792675634828307033643)
    ·
      refine ⟨108682189013452242460550465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72454792675634828307033643 108682189013452242460550465)
      ·
        refine ⟨81511641760089181845412849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108682189013452242460550465 81511641760089181845412849)
        ·
          refine ⟨61133731320066886384059637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81511641760089181845412849 61133731320066886384059637)
          ·
            refine ⟨5731287311256270598505591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61133731320066886384059637 5731287311256270598505591)
            ·
              refine ⟨8596930966884405897758387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5731287311256270598505591 8596930966884405897758387)
              ·
                refine ⟨12895396450326608846637581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8596930966884405897758387 12895396450326608846637581)
                ·
                  refine ⟨4835773668872478317489093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12895396450326608846637581 4835773668872478317489093)
                  ·
                    refine ⟨906707562913589684529205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4835773668872478317489093 906707562913589684529205)
                    ·
                      rfl

theorem cell23_5297420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_5297420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297420 prefixEnd_5297420 := by exact prefixLift 5297420
  have htrace : WordTrace (prefixWord ++ tailWord_5297420) baseStart_5297420 baseEnd_5297420 := by
    simpa [prefixWord, tailWord_5297420, baseEnd_5297420] using wordTrace_append hprefix tailTrace_5297420
  have hstable : (prefixWord ++ tailWord_5297420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297420).length < 2 ^ (prefixWord ++ tailWord_5297420).sum := by decide
  have hdescent : baseEnd_5297420 < baseStart_5297420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297436 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_5297436 : Nat := 118140960795 + 5297436 * 2 ^ 59
def prefixEnd_5297436 : Nat := 4983230072969 + 3 ^ 40 * 5297436 * 2
def baseEnd_5297436 : Nat := 2720130904431240990987541

theorem tailTrace_5297436 : CollatzResearch.WordTrace tailWord_5297436 prefixEnd_5297436 2720130904431240990987541 := by
  unfold tailWord_5297436
  simp only [CollatzResearch.WordTrace]
  refine ⟨96606682018150788442336081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128808909357534384589781441 96606682018150788442336081)
  ·
    refine ⟨72455011513613091331752061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96606682018150788442336081 72455011513613091331752061)
    ·
      refine ⟨27170629317604909249407023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72455011513613091331752061 27170629317604909249407023)
      ·
        refine ⟨40755943976407363874110535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27170629317604909249407023 40755943976407363874110535)
        ·
          refine ⟨61133915964611045811165803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40755943976407363874110535 61133915964611045811165803)
          ·
            refine ⟨91700873946916568716748705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61133915964611045811165803 91700873946916568716748705)
            ·
              refine ⟨68775655460187426537561529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91700873946916568716748705 68775655460187426537561529)
              ·
                refine ⟨51581741595140569903171147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68775655460187426537561529 51581741595140569903171147)
                ·
                  refine ⟨77372612392710854854756721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51581741595140569903171147 77372612392710854854756721)
                  ·
                    refine ⟨58029459294533141141067541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77372612392710854854756721 58029459294533141141067541)
                    ·
                      refine ⟨2720130904431240990987541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58029459294533141141067541 2720130904431240990987541)
                      ·
                        rfl

theorem cell23_5297436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_5297436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297436 prefixEnd_5297436 := by exact prefixLift 5297436
  have htrace : WordTrace (prefixWord ++ tailWord_5297436) baseStart_5297436 baseEnd_5297436 := by
    simpa [prefixWord, tailWord_5297436, baseEnd_5297436] using wordTrace_append hprefix tailTrace_5297436
  have hstable : (prefixWord ++ tailWord_5297436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297436).length < 2 ^ (prefixWord ++ tailWord_5297436).sum := by decide
  have hdescent : baseEnd_5297436 < baseStart_5297436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297493 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 1, 6]
def baseStart_5297493 : Nat := 118140960795 + 5297493 * 2 ^ 59
def prefixEnd_5297493 : Nat := 4983230072969 + 3 ^ 40 * 5297493 * 2
def baseEnd_5297493 : Nat := 906720057609515755991593

theorem tailTrace_5297493 : CollatzResearch.WordTrace tailWord_5297493 prefixEnd_5297493 906720057609515755991593 := by
  unfold tailWord_5297493
  simp only [CollatzResearch.WordTrace]
  refine ⟨193215442997095075619497133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128810295331396717079664755 193215442997095075619497133)
  ·
    refine ⟨72455791123910653357311425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193215442997095075619497133 72455791123910653357311425)
    ·
      refine ⟨54341843342932990017983569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72455791123910653357311425 54341843342932990017983569)
      ·
        refine ⟨40756382507199742513487677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54341843342932990017983569 40756382507199742513487677)
        ·
          refine ⟨15283643440199903442557879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40756382507199742513487677 15283643440199903442557879)
          ·
            refine ⟨22925465160299855163836819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15283643440199903442557879 22925465160299855163836819)
            ·
              refine ⟨34388197740449782745755229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22925465160299855163836819 34388197740449782745755229)
              ·
                refine ⟨12895574152668668529658211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34388197740449782745755229 12895574152668668529658211)
                ·
                  refine ⟨19343361229003002794487317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12895574152668668529658211 19343361229003002794487317)
                  ·
                    refine ⟨906720057609515755991593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19343361229003002794487317 906720057609515755991593)
                    ·
                      rfl

theorem cell23_5297493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_5297493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297493 prefixEnd_5297493 := by exact prefixLift 5297493
  have htrace : WordTrace (prefixWord ++ tailWord_5297493) baseStart_5297493 baseEnd_5297493 := by
    simpa [prefixWord, tailWord_5297493, baseEnd_5297493] using wordTrace_append hprefix tailTrace_5297493
  have hstable : (prefixWord ++ tailWord_5297493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297493).length < 2 ^ (prefixWord ++ tailWord_5297493).sum := by decide
  have hdescent : baseEnd_5297493 < baseStart_5297493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297514 : List Nat := [3, 1, 3, 3, 2, 2, 2, 1, 1, 5]
def baseStart_5297514 : Nat := 118140960795 + 5297514 * 2 ^ 59
def prefixEnd_5297514 : Nat := 4983230072969 + 3 ^ 40 * 5297514 * 2
def baseEnd_5297514 : Nat := 906723651974097228604061

theorem tailTrace_5297514 : CollatzResearch.WordTrace tailWord_5297514 prefixEnd_5297514 906723651974097228604061 := by
  unfold tailWord_5297514
  simp only [CollatzResearch.WordTrace]
  refine ⟨48304052232504749051502899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128810805953345997470674397 48304052232504749051502899)
  ·
    refine ⟨72456078348757123577254349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48304052232504749051502899 72456078348757123577254349)
    ·
      refine ⟨27171029380783921341470381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72456078348757123577254349 27171029380783921341470381)
      ·
        refine ⟨10189136017793970503051393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27171029380783921341470381 10189136017793970503051393)
        ·
          refine ⟨7641852013345477877288545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10189136017793970503051393 7641852013345477877288545)
          ·
            refine ⟨5731389010009108407966409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7641852013345477877288545 5731389010009108407966409)
            ·
              refine ⟨4298541757506831305974807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5731389010009108407966409 4298541757506831305974807)
              ·
                refine ⟨6447812636260246958962211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4298541757506831305974807 6447812636260246958962211)
                ·
                  refine ⟨9671718954390370438443317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6447812636260246958962211 9671718954390370438443317)
                  ·
                    refine ⟨906723651974097228604061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9671718954390370438443317 906723651974097228604061)
                    ·
                      rfl

theorem cell23_5297514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_5297514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297514 prefixEnd_5297514 := by exact prefixLift 5297514
  have htrace : WordTrace (prefixWord ++ tailWord_5297514) baseStart_5297514 baseEnd_5297514 := by
    simpa [prefixWord, tailWord_5297514, baseEnd_5297514] using wordTrace_append hprefix tailTrace_5297514
  have hstable : (prefixWord ++ tailWord_5297514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297514).length < 2 ^ (prefixWord ++ tailWord_5297514).sum := by decide
  have hdescent : baseEnd_5297514 < baseStart_5297514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297517 : List Nat := [1, 5, 1, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_5297517 : Nat := 118140960795 + 5297517 * 2 ^ 59
def prefixEnd_5297517 : Nat := 4983230072969 + 3 ^ 40 * 5297517 * 2
def baseEnd_5297517 : Nat := 2720172496364255174074669

theorem tailTrace_5297517 : CollatzResearch.WordTrace tailWord_5297517 prefixEnd_5297517 2720172496364255174074669 := by
  unfold tailWord_5297517
  simp only [CollatzResearch.WordTrace]
  refine ⟨193216318349008127718370805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128810878899338751812247203 193216318349008127718370805)
  ·
    refine ⟨18114029845219511973597263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193216318349008127718370805 18114029845219511973597263)
    ·
      refine ⟨27171044767829267960395895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18114029845219511973597263 27171044767829267960395895)
      ·
        refine ⟨40756567151743901940593843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27171044767829267960395895 40756567151743901940593843)
        ·
          refine ⟨61134850727615852910890765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40756567151743901940593843 61134850727615852910890765)
          ·
            refine ⟨22925569022855944841584037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61134850727615852910890765 22925569022855944841584037)
            ·
              refine ⟨4298544191785489657797007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22925569022855944841584037 4298544191785489657797007)
              ·
                refine ⟨6447816287678234486695511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4298544191785489657797007 6447816287678234486695511)
                ·
                  refine ⟨9671724431517351730043267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6447816287678234486695511 9671724431517351730043267)
                  ·
                    refine ⟨14507586647276027595064901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9671724431517351730043267 14507586647276027595064901)
                    ·
                      refine ⟨2720172496364255174074669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14507586647276027595064901 2720172496364255174074669)
                      ·
                        rfl

theorem cell23_5297517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_5297517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297517 prefixEnd_5297517 := by exact prefixLift 5297517
  have htrace : WordTrace (prefixWord ++ tailWord_5297517) baseStart_5297517 baseEnd_5297517 := by
    simpa [prefixWord, tailWord_5297517, baseEnd_5297517] using wordTrace_append hprefix tailTrace_5297517
  have hstable : (prefixWord ++ tailWord_5297517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297517).length < 2 ^ (prefixWord ++ tailWord_5297517).sum := by decide
  have hdescent : baseEnd_5297517 < baseStart_5297517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
