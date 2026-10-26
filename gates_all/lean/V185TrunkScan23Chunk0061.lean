import V185TrunkScan23Chunk0060

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_360476 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_360476 : Nat := 118140960795 + 360476 * 2 ^ 59
def prefixEnd_360476 : Nat := 4983230072969 + 3 ^ 40 * 360476 * 2
def baseEnd_360476 : Nat := 185097452410236869692207

theorem tailTrace_360476 : CollatzResearch.WordTrace tailWord_360476 prefixEnd_360476 185097452410236869692207 := by
  unfold tailWord_360476
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573819921032245622258641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8765093228042994163011521 6573819921032245622258641)
  ·
    refine ⟨4930364940774184216693981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6573819921032245622258641 4930364940774184216693981)
    ·
      refine ⟨1848886852790319081260243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4930364940774184216693981 1848886852790319081260243)
      ·
        refine ⟨2773330279185478621890365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848886852790319081260243 2773330279185478621890365)
        ·
          refine ⟨1039998854694554483208887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2773330279185478621890365 1039998854694554483208887)
          ·
            refine ⟨1559998282041831724813331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039998854694554483208887 1559998282041831724813331)
            ·
              refine ⟨2339997423062747587219997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559998282041831724813331 2339997423062747587219997)
              ·
                refine ⟨877499033648530345207499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2339997423062747587219997 877499033648530345207499)
                ·
                  refine ⟨1316248550472795517811249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 877499033648530345207499 1316248550472795517811249)
                  ·
                    refine ⟨987186412854596638358437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1316248550472795517811249 987186412854596638358437)
                    ·
                      refine ⟨185097452410236869692207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 987186412854596638358437 185097452410236869692207)
                      ·
                        rfl

theorem cell23_360476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_360476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360476 prefixEnd_360476 := by exact prefixLift 360476
  have htrace : WordTrace (prefixWord ++ tailWord_360476) baseStart_360476 baseEnd_360476 := by
    simpa [prefixWord, tailWord_360476, baseEnd_360476] using wordTrace_append hprefix tailTrace_360476
  have hstable : (prefixWord ++ tailWord_360476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360476).length < 2 ^ (prefixWord ++ tailWord_360476).sum := by decide
  have hdescent : baseEnd_360476 < baseStart_360476 := by decide
  rcases family_descends (prefixWord ++ tailWord_360476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360496 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 3]
def baseStart_360496 : Nat := 118140960795 + 360496 * 2 ^ 59
def prefixEnd_360496 : Nat := 4983230072969 + 3 ^ 40 * 360496 * 2
def baseEnd_360496 : Nat := 185107722023326791442115

theorem tailTrace_360496 : CollatzResearch.WordTrace tailWord_360496 prefixEnd_360496 185107722023326791442115 := by
  unfold tailWord_360496
  simp only [CollatzResearch.WordTrace]
  refine ⟨6574184650996017330122671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8765579534661356440163561 6574184650996017330122671)
  ·
    refine ⟨9861276976494025995184007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6574184650996017330122671 9861276976494025995184007)
    ·
      refine ⟨14791915464741038992776011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9861276976494025995184007 14791915464741038992776011)
      ·
        refine ⟨22187873197111558489164017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14791915464741038992776011 22187873197111558489164017)
        ·
          refine ⟨16640904897833668866873013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22187873197111558489164017 16640904897833668866873013)
          ·
            refine ⟨1560084834171906456269345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16640904897833668866873013 1560084834171906456269345)
            ·
              refine ⟨1170063625628929842202009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1560084834171906456269345 1170063625628929842202009)
              ·
                refine ⟨877547719221697381651507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170063625628929842202009 877547719221697381651507)
                ·
                  refine ⟨1316321578832546072477261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 877547719221697381651507 1316321578832546072477261)
                  ·
                    refine ⟨493620592062204777178973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1316321578832546072477261 493620592062204777178973)
                    ·
                      refine ⟨185107722023326791442115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 493620592062204777178973 185107722023326791442115)
                      ·
                        rfl

theorem cell23_360496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 3].length) (baseStart_360496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360496 prefixEnd_360496 := by exact prefixLift 360496
  have htrace : WordTrace (prefixWord ++ tailWord_360496) baseStart_360496 baseEnd_360496 := by
    simpa [prefixWord, tailWord_360496, baseEnd_360496] using wordTrace_append hprefix tailTrace_360496
  have hstable : (prefixWord ++ tailWord_360496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360496).length < 2 ^ (prefixWord ++ tailWord_360496).sum := by decide
  have hdescent : baseEnd_360496 < baseStart_360496 := by decide
  rcases family_descends (prefixWord ++ tailWord_360496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360497 : List Nat := [1, 2, 2, 3, 1, 4, 2, 3, 1, 2, 2]
def baseStart_360497 : Nat := 118140960795 + 360497 * 2 ^ 59
def prefixEnd_360497 : Nat := 4983230072969 + 3 ^ 40 * 360497 * 2
def baseEnd_360497 : Nat := 185108235503981287529611

theorem tailTrace_360497 : CollatzResearch.WordTrace tailWord_360497 prefixEnd_360497 185108235503981287529611 := by
  unfold tailWord_360497
  simp only [CollatzResearch.WordTrace]
  refine ⟨13148405774988411831031745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8765603849992274554021163 13148405774988411831031745)
  ·
    refine ⟨9861304331241308873273809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13148405774988411831031745 9861304331241308873273809)
    ·
      refine ⟨7395978248430981654955357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9861304331241308873273809 7395978248430981654955357)
      ·
        refine ⟨2773491843161618120608259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7395978248430981654955357 2773491843161618120608259)
        ·
          refine ⟨4160237764742427180912389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773491843161618120608259 4160237764742427180912389)
          ·
            refine ⟨780044580889205096421073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4160237764742427180912389 780044580889205096421073)
            ·
              refine ⟨585033435666903822315805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 780044580889205096421073 585033435666903822315805)
              ·
                refine ⟨219387538375088933368427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 585033435666903822315805 219387538375088933368427)
                ·
                  refine ⟨329081307562633400052641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219387538375088933368427 329081307562633400052641)
                  ·
                    refine ⟨246810980671975050039481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 329081307562633400052641 246810980671975050039481)
                    ·
                      refine ⟨185108235503981287529611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246810980671975050039481 185108235503981287529611)
                      ·
                        rfl

theorem cell23_360497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_360497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360497 prefixEnd_360497 := by exact prefixLift 360497
  have htrace : WordTrace (prefixWord ++ tailWord_360497) baseStart_360497 baseEnd_360497 := by
    simpa [prefixWord, tailWord_360497, baseEnd_360497] using wordTrace_append hprefix tailTrace_360497
  have hstable : (prefixWord ++ tailWord_360497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360497).length < 2 ^ (prefixWord ++ tailWord_360497).sum := by decide
  have hdescent : baseEnd_360497 < baseStart_360497 := by decide
  rcases family_descends (prefixWord ++ tailWord_360497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360530 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_360530 : Nat := 118140960795 + 360530 * 2 ^ 59
def prefixEnd_360530 : Nat := 4983230072969 + 3 ^ 40 * 360530 * 2
def baseEnd_360530 : Nat := 185125180365579658416959

theorem tailTrace_360530 : CollatzResearch.WordTrace tailWord_360530 prefixEnd_360530 185125180365579658416959 := by
  unfold tailWord_360530
  simp only [CollatzResearch.WordTrace]
  refine ⟨3287402345967214616745761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8766406255912572311322029 3287402345967214616745761)
  ·
    refine ⟨2465551759475410962559321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3287402345967214616745761 2465551759475410962559321)
    ·
      refine ⟨1849163819606558221919491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2465551759475410962559321 1849163819606558221919491)
      ·
        refine ⟨2773745729409837332879237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849163819606558221919491 2773745729409837332879237)
        ·
          refine ⟨520077324264344499914857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2773745729409837332879237 520077324264344499914857)
          ·
            refine ⟨390057993198258374936143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520077324264344499914857 390057993198258374936143)
            ·
              refine ⟨585086989797387562404215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390057993198258374936143 585086989797387562404215)
              ·
                refine ⟨877630484696081343606323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585086989797387562404215 877630484696081343606323)
                ·
                  refine ⟨1316445727044122015409485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 877630484696081343606323 1316445727044122015409485)
                  ·
                    refine ⟨493667147641545755778557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1316445727044122015409485 493667147641545755778557)
                    ·
                      refine ⟨185125180365579658416959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 493667147641545755778557 185125180365579658416959)
                      ·
                        rfl

theorem cell23_360530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_360530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360530 prefixEnd_360530 := by exact prefixLift 360530
  have htrace : WordTrace (prefixWord ++ tailWord_360530) baseStart_360530 baseEnd_360530 := by
    simpa [prefixWord, tailWord_360530, baseEnd_360530] using wordTrace_append hprefix tailTrace_360530
  have hstable : (prefixWord ++ tailWord_360530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360530).length < 2 ^ (prefixWord ++ tailWord_360530).sum := by decide
  have hdescent : baseEnd_360530 < baseStart_360530 := by decide
  rcases family_descends (prefixWord ++ tailWord_360530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360540 : List Nat := [2, 2, 4, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_360540 : Nat := 118140960795 + 360540 * 2 ^ 59
def prefixEnd_360540 : Nat := 4983230072969 + 3 ^ 40 * 360540 * 2
def baseEnd_360540 : Nat := 185130315172124619291913

theorem tailTrace_360540 : CollatzResearch.WordTrace tailWord_360540 prefixEnd_360540 185130315172124619291913 := by
  unfold tailWord_360540
  simp only [CollatzResearch.WordTrace]
  refine ⟨6574987056916315087423537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8766649409221753449898049 6574987056916315087423537)
  ·
    refine ⟨4931240292687236315567653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6574987056916315087423537 4931240292687236315567653)
    ·
      refine ⟨924607554878856809168935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4931240292687236315567653 924607554878856809168935)
      ·
        refine ⟨1386911332318285213753403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 924607554878856809168935 1386911332318285213753403)
        ·
          refine ⟨2080366998477427820630105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386911332318285213753403 2080366998477427820630105)
          ·
            refine ⟨1560275248858070865472579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2080366998477427820630105 1560275248858070865472579)
            ·
              refine ⟨2340412873287106298208869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1560275248858070865472579 2340412873287106298208869)
              ·
                refine ⟨438827413741332430914163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2340412873287106298208869 438827413741332430914163)
                ·
                  refine ⟨658241120611998646371245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438827413741332430914163 658241120611998646371245)
                  ·
                    refine ⟨246840420229499492389217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 658241120611998646371245 246840420229499492389217)
                    ·
                      refine ⟨185130315172124619291913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246840420229499492389217 185130315172124619291913)
                      ·
                        rfl

theorem cell23_360540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_360540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360540 prefixEnd_360540 := by exact prefixLift 360540
  have htrace : WordTrace (prefixWord ++ tailWord_360540) baseStart_360540 baseEnd_360540 := by
    simpa [prefixWord, tailWord_360540, baseEnd_360540] using wordTrace_append hprefix tailTrace_360540
  have hstable : (prefixWord ++ tailWord_360540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360540).length < 2 ^ (prefixWord ++ tailWord_360540).sum := by decide
  have hdescent : baseEnd_360540 < baseStart_360540 := by decide
  rcases family_descends (prefixWord ++ tailWord_360540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360553 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 6, 2, 2]
def baseStart_360553 : Nat := 118140960795 + 360553 * 2 ^ 59
def prefixEnd_360553 : Nat := 4983230072969 + 3 ^ 40 * 360553 * 2
def baseEnd_360553 : Nat := 185136990420633068429353

theorem tailTrace_360553 : CollatzResearch.WordTrace tailWord_360553 prefixEnd_360553 185136990420633068429353 := by
  unfold tailWord_360553
  simp only [CollatzResearch.WordTrace]
  refine ⟨13150448262785533395070313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8766965508523688930046875 13150448262785533395070313)
  ·
    refine ⟨9862836197089150046302735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13150448262785533395070313 9862836197089150046302735)
    ·
      refine ⟨14794254295633725069454103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9862836197089150046302735 14794254295633725069454103)
      ·
        refine ⟨22191381443450587604181155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14794254295633725069454103 22191381443450587604181155)
        ·
          refine ⟨33287072165175881406271733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22191381443450587604181155 33287072165175881406271733)
          ·
            refine ⟨3120663015485238881837975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33287072165175881406271733 3120663015485238881837975)
            ·
              refine ⟨4680994523227858322756963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120663015485238881837975 4680994523227858322756963)
              ·
                refine ⟨7021491784841787484135445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680994523227858322756963 7021491784841787484135445)
                ·
                  refine ⟨329132427414458788318849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7021491784841787484135445 329132427414458788318849)
                  ·
                    refine ⟨246849320560844091239137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 329132427414458788318849 246849320560844091239137)
                    ·
                      refine ⟨185136990420633068429353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246849320560844091239137 185136990420633068429353)
                      ·
                        rfl

theorem cell23_360553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 2, 2].length) (baseStart_360553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360553 prefixEnd_360553 := by exact prefixLift 360553
  have htrace : WordTrace (prefixWord ++ tailWord_360553) baseStart_360553 baseEnd_360553 := by
    simpa [prefixWord, tailWord_360553, baseEnd_360553] using wordTrace_append hprefix tailTrace_360553
  have hstable : (prefixWord ++ tailWord_360553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360553).length < 2 ^ (prefixWord ++ tailWord_360553).sum := by decide
  have hdescent : baseEnd_360553 < baseStart_360553 := by decide
  rcases family_descends (prefixWord ++ tailWord_360553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360556 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_360556 : Nat := 118140960795 + 360556 * 2 ^ 59
def prefixEnd_360556 : Nat := 4983230072969 + 3 ^ 40 * 360556 * 2
def baseEnd_360556 : Nat := 185138530862596556691839

theorem tailTrace_360556 : CollatzResearch.WordTrace tailWord_360556 prefixEnd_360556 185138530862596556691839 := by
  unfold tailWord_360556
  simp only [CollatzResearch.WordTrace]
  refine ⟨6575278840887332453714761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8767038454516443271619681 6575278840887332453714761)
  ·
    refine ⟨4931459130665499340286071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6575278840887332453714761 4931459130665499340286071)
    ·
      refine ⟨7397188695998249010429107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4931459130665499340286071 7397188695998249010429107)
      ·
        refine ⟨11095783043997373515643661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7397188695998249010429107 11095783043997373515643661)
        ·
          refine ⟨4160918641499015068366373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11095783043997373515643661 4160918641499015068366373)
          ·
            refine ⟨780172245281065325318695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4160918641499015068366373 780172245281065325318695)
            ·
              refine ⟨1170258367921597987978043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780172245281065325318695 1170258367921597987978043)
              ·
                refine ⟨1755387551882396981967065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170258367921597987978043 1755387551882396981967065)
                ·
                  refine ⟨1316540663911797736475299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1755387551882396981967065 1316540663911797736475299)
                  ·
                    refine ⟨1974810995867696604712949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1316540663911797736475299 1974810995867696604712949)
                    ·
                      refine ⟨185138530862596556691839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1974810995867696604712949 185138530862596556691839)
                      ·
                        rfl

theorem cell23_360556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_360556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360556 prefixEnd_360556 := by exact prefixLift 360556
  have htrace : WordTrace (prefixWord ++ tailWord_360556) baseStart_360556 baseEnd_360556 := by
    simpa [prefixWord, tailWord_360556, baseEnd_360556] using wordTrace_append hprefix tailTrace_360556
  have hstable : (prefixWord ++ tailWord_360556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360556).length < 2 ^ (prefixWord ++ tailWord_360556).sum := by decide
  have hdescent : baseEnd_360556 < baseStart_360556 := by decide
  rcases family_descends (prefixWord ++ tailWord_360556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360619 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 6, 8]
def baseStart_360619 : Nat := 118140960795 + 360619 * 2 ^ 59
def prefixEnd_360619 : Nat := 4983230072969 + 3 ^ 40 * 360619 * 2
def baseEnd_360619 : Nat := 61723626714609936734683

theorem tailTrace_360619 : CollatzResearch.WordTrace tailWord_360619 prefixEnd_360619 61723626714609936734683 := by
  unfold tailWord_360619
  simp only [CollatzResearch.WordTrace]
  refine ⟨13152855480546426666972911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8768570320364284444648607 13152855480546426666972911)
  ·
    refine ⟨19729283220819640000459367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13152855480546426666972911 19729283220819640000459367)
    ·
      refine ⟨29593924831229460000689051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19729283220819640000459367 29593924831229460000689051)
      ·
        refine ⟨44390887246844190001033577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29593924831229460000689051 44390887246844190001033577)
        ·
          refine ⟨33293165435133142500775183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44390887246844190001033577 33293165435133142500775183)
          ·
            refine ⟨49939748152699713751162775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33293165435133142500775183 49939748152699713751162775)
            ·
              refine ⟨74909622229049570626744163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49939748152699713751162775 74909622229049570626744163)
              ·
                refine ⟨112364433343574355940116245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74909622229049570626744163 112364433343574355940116245)
                ·
                  refine ⟨5267082812980047934692949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112364433343574355940116245 5267082812980047934692949)
                  ·
                    refine ⟨61723626714609936734683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5267082812980047934692949 61723626714609936734683)
                    ·
                      rfl

theorem cell23_360619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 8].length) (baseStart_360619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360619 prefixEnd_360619 := by exact prefixLift 360619
  have htrace : WordTrace (prefixWord ++ tailWord_360619) baseStart_360619 baseEnd_360619 := by
    simpa [prefixWord, tailWord_360619, baseEnd_360619] using wordTrace_append hprefix tailTrace_360619
  have hstable : (prefixWord ++ tailWord_360619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360619).length < 2 ^ (prefixWord ++ tailWord_360619).sum := by decide
  have hdescent : baseEnd_360619 < baseStart_360619 := by decide
  rcases family_descends (prefixWord ++ tailWord_360619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360696 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 5, 5]
def baseStart_360696 : Nat := 118140960795 + 360696 * 2 ^ 59
def prefixEnd_360696 : Nat := 4983230072969 + 3 ^ 40 * 360696 * 2
def baseEnd_360696 : Nat := 61736806051408669647065

theorem tailTrace_360696 : CollatzResearch.WordTrace tailWord_360696 prefixEnd_360696 61736806051408669647065 := by
  unfold tailWord_360696
  simp only [CollatzResearch.WordTrace]
  refine ⟨6577831950633734408762971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8770442600844979211683961 6577831950633734408762971)
  ·
    refine ⟨9866747925950601613144457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6577831950633734408762971 9866747925950601613144457)
    ·
      refine ⟨7400060944462951209858343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9866747925950601613144457 7400060944462951209858343)
      ·
        refine ⟨11100091416694426814787515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7400060944462951209858343 11100091416694426814787515)
        ·
          refine ⟨16650137125041640222181273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11100091416694426814787515 16650137125041640222181273)
          ·
            refine ⟨12487602843781230166635955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16650137125041640222181273 12487602843781230166635955)
            ·
              refine ⟨18731404265671845249953933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12487602843781230166635955 18731404265671845249953933)
              ·
                refine ⟨7024276599626941968732725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18731404265671845249953933 7024276599626941968732725)
                ·
                  refine ⟨658525931215025809568693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7024276599626941968732725 658525931215025809568693)
                  ·
                    refine ⟨61736806051408669647065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 658525931215025809568693 61736806051408669647065)
                    ·
                      rfl

theorem cell23_360696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_360696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360696 prefixEnd_360696 := by exact prefixLift 360696
  have htrace : WordTrace (prefixWord ++ tailWord_360696) baseStart_360696 baseEnd_360696 := by
    simpa [prefixWord, tailWord_360696, baseEnd_360696] using wordTrace_append hprefix tailTrace_360696
  have hstable : (prefixWord ++ tailWord_360696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360696).length < 2 ^ (prefixWord ++ tailWord_360696).sum := by decide
  have hdescent : baseEnd_360696 < baseStart_360696 := by decide
  rcases family_descends (prefixWord ++ tailWord_360696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360700 : List Nat := [2, 2, 2, 1, 4, 2, 3, 1, 6]
def baseStart_360700 : Nat := 118140960795 + 360700 * 2 ^ 59
def prefixEnd_360700 : Nat := 4983230072969 + 3 ^ 40 * 360700 * 2
def baseEnd_360700 : Nat := 20579163564093777032353

theorem tailTrace_360700 : CollatzResearch.WordTrace tailWord_360700 prefixEnd_360700 20579163564093777032353 := by
  unfold tailWord_360700
  simp only [CollatzResearch.WordTrace]
  refine ⟨6577904896626488750335777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8770539862168651667114369 6577904896626488750335777)
  ·
    refine ⟨4933428672469866562751833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6577904896626488750335777 4933428672469866562751833)
    ·
      refine ⟨3700071504352399922063875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4933428672469866562751833 3700071504352399922063875)
      ·
        refine ⟨5550107256528599883095813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3700071504352399922063875 5550107256528599883095813)
        ·
          refine ⟨1040645110599112478080465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5550107256528599883095813 1040645110599112478080465)
          ·
            refine ⟨780483832949334358560349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1040645110599112478080465 780483832949334358560349)
            ·
              refine ⟨292681437356000384460131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780483832949334358560349 292681437356000384460131)
              ·
                refine ⟨439022156034000576690197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292681437356000384460131 439022156034000576690197)
                ·
                  refine ⟨20579163564093777032353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 439022156034000576690197 20579163564093777032353)
                  ·
                    rfl

theorem cell23_360700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_360700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360700 prefixEnd_360700 := by exact prefixLift 360700
  have htrace : WordTrace (prefixWord ++ tailWord_360700) baseStart_360700 baseEnd_360700 := by
    simpa [prefixWord, tailWord_360700, baseEnd_360700] using wordTrace_append hprefix tailTrace_360700
  have hstable : (prefixWord ++ tailWord_360700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360700).length < 2 ^ (prefixWord ++ tailWord_360700).sum := by decide
  have hdescent : baseEnd_360700 < baseStart_360700 := by decide
  rcases family_descends (prefixWord ++ tailWord_360700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360703 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 3, 5, 2]
def baseStart_360703 : Nat := 118140960795 + 360703 * 2 ^ 59
def prefixEnd_360703 : Nat := 4983230072969 + 3 ^ 40 * 360703 * 2
def baseEnd_360703 : Nat := 185214012518807481553663

theorem tailTrace_360703 : CollatzResearch.WordTrace tailWord_360703 prefixEnd_360703 185214012518807481553663 := by
  unfold tailWord_360703
  simp only [CollatzResearch.WordTrace]
  refine ⟨13155919212242109013030763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8770612808161406008687175 13155919212242109013030763)
  ·
    refine ⟨19733878818363163519546145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13155919212242109013030763 19733878818363163519546145)
    ·
      refine ⟨14800409113772372639659609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19733878818363163519546145 14800409113772372639659609)
      ·
        refine ⟨11100306835329279479744707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14800409113772372639659609 11100306835329279479744707)
        ·
          refine ⟨16650460252993919219617061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11100306835329279479744707 16650460252993919219617061)
          ·
            refine ⟨3121961297436359853678199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16650460252993919219617061 3121961297436359853678199)
            ·
              refine ⟨4682941946154539780517299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3121961297436359853678199 4682941946154539780517299)
              ·
                refine ⟨7024412919231809670775949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4682941946154539780517299 7024412919231809670775949)
                ·
                  refine ⟨2634154844711928626540981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7024412919231809670775949 2634154844711928626540981)
                  ·
                    refine ⟨246952016691743308738217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2634154844711928626540981 246952016691743308738217)
                    ·
                      refine ⟨185214012518807481553663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246952016691743308738217 185214012518807481553663)
                      ·
                        rfl

theorem cell23_360703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 5, 2].length) (baseStart_360703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360703 prefixEnd_360703 := by exact prefixLift 360703
  have htrace : WordTrace (prefixWord ++ tailWord_360703) baseStart_360703 baseEnd_360703 := by
    simpa [prefixWord, tailWord_360703, baseEnd_360703] using wordTrace_append hprefix tailTrace_360703
  have hstable : (prefixWord ++ tailWord_360703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360703).length < 2 ^ (prefixWord ++ tailWord_360703).sum := by decide
  have hdescent : baseEnd_360703 < baseStart_360703 := by decide
  rcases family_descends (prefixWord ++ tailWord_360703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360713 : List Nat := [1, 2, 1, 1, 3, 4, 1, 4, 1, 5]
def baseStart_360713 : Nat := 118140960795 + 360713 * 2 ^ 59
def prefixEnd_360713 : Nat := 4983230072969 + 3 ^ 40 * 360713 * 2
def baseEnd_360713 : Nat := 61739715775117480809539

theorem tailTrace_360713 : CollatzResearch.WordTrace tailWord_360713 prefixEnd_360713 61739715775117480809539 := by
  unfold tailWord_360713
  simp only [CollatzResearch.WordTrace]
  refine ⟨13156283942205880720894793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8770855961470587147263195 13156283942205880720894793)
  ·
    refine ⟨9867212956654410540671095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13156283942205880720894793 9867212956654410540671095)
    ·
      refine ⟨14800819434981615811006643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9867212956654410540671095 14800819434981615811006643)
      ·
        refine ⟨22201229152472423716509965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14800819434981615811006643 22201229152472423716509965)
        ·
          refine ⟨8325460932177158893691237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22201229152472423716509965 8325460932177158893691237)
          ·
            refine ⟨1561023924783217292567107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8325460932177158893691237 1561023924783217292567107)
            ·
              refine ⟨2341535887174825938850661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561023924783217292567107 2341535887174825938850661)
              ·
                refine ⟨439037978845279863534499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2341535887174825938850661 439037978845279863534499)
                ·
                  refine ⟨658556968267919795301749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439037978845279863534499 658556968267919795301749)
                  ·
                    refine ⟨61739715775117480809539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 658556968267919795301749 61739715775117480809539)
                    ·
                      rfl

theorem cell23_360713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 5].length) (baseStart_360713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360713 prefixEnd_360713 := by exact prefixLift 360713
  have htrace : WordTrace (prefixWord ++ tailWord_360713) baseStart_360713 baseEnd_360713 := by
    simpa [prefixWord, tailWord_360713, baseEnd_360713] using wordTrace_append hprefix tailTrace_360713
  have hstable : (prefixWord ++ tailWord_360713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360713).length < 2 ^ (prefixWord ++ tailWord_360713).sum := by decide
  have hdescent : baseEnd_360713 < baseStart_360713 := by decide
  rcases family_descends (prefixWord ++ tailWord_360713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360744 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_360744 : Nat := 118140960795 + 360744 * 2 ^ 59
def prefixEnd_360744 : Nat := 4983230072969 + 3 ^ 40 * 360744 * 2
def baseEnd_360744 : Nat := 185235065225641821140975

theorem tailTrace_360744 : CollatzResearch.WordTrace tailWord_360744 prefixEnd_360744 185235065225641821140975 := by
  unfold tailWord_360744
  simp only [CollatzResearch.WordTrace]
  refine ⟨6578707302546786507636643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8771609736729048676848857 6578707302546786507636643)
  ·
    refine ⟨9868060953820179761454965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6578707302546786507636643 9868060953820179761454965)
    ·
      refine ⟨925130714420641852636403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9868060953820179761454965 925130714420641852636403)
      ·
        refine ⟨1387696071630962778954605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 925130714420641852636403 1387696071630962778954605)
        ·
          refine ⟨520386026861611042107977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1387696071630962778954605 520386026861611042107977)
          ·
            refine ⟨390289520146208281580983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520386026861611042107977 390289520146208281580983)
            ·
              refine ⟨585434280219312422371475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390289520146208281580983 585434280219312422371475)
              ·
                refine ⟨878151420328968633557213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585434280219312422371475 878151420328968633557213)
                ·
                  refine ⟨329306782623363237583955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878151420328968633557213 329306782623363237583955)
                  ·
                    refine ⟨493960173935044856375933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 329306782623363237583955 493960173935044856375933)
                    ·
                      refine ⟨185235065225641821140975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 493960173935044856375933 185235065225641821140975)
                      ·
                        rfl

theorem cell23_360744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_360744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360744 prefixEnd_360744 := by exact prefixLift 360744
  have htrace : WordTrace (prefixWord ++ tailWord_360744) baseStart_360744 baseEnd_360744 := by
    simpa [prefixWord, tailWord_360744, baseEnd_360744] using wordTrace_append hprefix tailTrace_360744
  have hstable : (prefixWord ++ tailWord_360744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360744).length < 2 ^ (prefixWord ++ tailWord_360744).sum := by decide
  have hdescent : baseEnd_360744 < baseStart_360744 := by decide
  rcases family_descends (prefixWord ++ tailWord_360744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360790 : List Nat := [5, 2, 3, 13]
def baseStart_360790 : Nat := 118140960795 + 360790 * 2 ^ 59
def prefixEnd_360790 : Nat := 4983230072969 + 3 ^ 40 * 360790 * 2
def baseEnd_360790 : Nat := 84709046792752007849

theorem tailTrace_360790 : CollatzResearch.WordTrace tailWord_360790 prefixEnd_360790 84709046792752007849 := by
  unfold tailWord_360790
  simp only [CollatzResearch.WordTrace]
  refine ⟨822443272682932679465489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8772728241951281914298549 822443272682932679465489)
  ·
    refine ⟨616832454512199509599117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 822443272682932679465489 616832454512199509599117)
    ·
      refine ⟨231312170442074816099669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 616832454512199509599117 231312170442074816099669)
      ·
        refine ⟨84709046792752007849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 231312170442074816099669 84709046792752007849)
        ·
          rfl

theorem cell23_360790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 13].length) (baseStart_360790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360790 prefixEnd_360790 := by exact prefixLift 360790
  have htrace : WordTrace (prefixWord ++ tailWord_360790) baseStart_360790 baseEnd_360790 := by
    simpa [prefixWord, tailWord_360790, baseEnd_360790] using wordTrace_append hprefix tailTrace_360790
  have hstable : (prefixWord ++ tailWord_360790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360790).length < 2 ^ (prefixWord ++ tailWord_360790).sum := by decide
  have hdescent : baseEnd_360790 < baseStart_360790 := by decide
  rcases family_descends (prefixWord ++ tailWord_360790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360844 : List Nat := [2, 2, 1, 2, 1, 4, 4, 1, 1, 3, 2]
def baseStart_360844 : Nat := 118140960795 + 360844 * 2 ^ 59
def prefixEnd_360844 : Nat := 4983230072969 + 3 ^ 40 * 360844 * 2
def baseEnd_360844 : Nat := 185286413291091429890515

theorem tailTrace_360844 : CollatzResearch.WordTrace tailWord_360844 prefixEnd_360844 185286413291091429890515 := by
  unfold tailWord_360844
  simp only [CollatzResearch.WordTrace]
  refine ⟨6580530952365645046956793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8774041269820860062609057 6580530952365645046956793)
  ·
    refine ⟨4935398214274233785217595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6580530952365645046956793 4935398214274233785217595)
    ·
      refine ⟨7403097321411350677826393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4935398214274233785217595 7403097321411350677826393)
      ·
        refine ⟨5552322991058513008369795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7403097321411350677826393 5552322991058513008369795)
        ·
          refine ⟨8328484486587769512554693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5552322991058513008369795 8328484486587769512554693)
          ·
            refine ⟨1561590841235206783604005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8328484486587769512554693 1561590841235206783604005)
            ·
              refine ⟨292798282731601271925751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1561590841235206783604005 292798282731601271925751)
              ·
                refine ⟨439197424097401907888627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292798282731601271925751 439197424097401907888627)
                ·
                  refine ⟨658796136146102861832941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439197424097401907888627 658796136146102861832941)
                  ·
                    refine ⟨247048551054788573187353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 658796136146102861832941 247048551054788573187353)
                    ·
                      refine ⟨185286413291091429890515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 247048551054788573187353 185286413291091429890515)
                      ·
                        rfl

theorem cell23_360844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_360844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360844 prefixEnd_360844 := by exact prefixLift 360844
  have htrace : WordTrace (prefixWord ++ tailWord_360844) baseStart_360844 baseEnd_360844 := by
    simpa [prefixWord, tailWord_360844, baseEnd_360844] using wordTrace_append hprefix tailTrace_360844
  have hstable : (prefixWord ++ tailWord_360844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360844).length < 2 ^ (prefixWord ++ tailWord_360844).sum := by decide
  have hdescent : baseEnd_360844 < baseStart_360844 := by decide
  rcases family_descends (prefixWord ++ tailWord_360844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360857 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 4, 2, 2]
def baseStart_360857 : Nat := 118140960795 + 360857 * 2 ^ 59
def prefixEnd_360857 : Nat := 4983230072969 + 3 ^ 40 * 360857 * 2
def baseEnd_360857 : Nat := 185293088539599879027955

theorem tailTrace_360857 : CollatzResearch.WordTrace tailWord_360857 prefixEnd_360857 185293088539599879027955 := by
  unfold tailWord_360857
  simp only [CollatzResearch.WordTrace]
  refine ⟨13161536053684193314136825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8774357369122795542757883 13161536053684193314136825)
  ·
    refine ⟨9871152040263144985602619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13161536053684193314136825 9871152040263144985602619)
    ·
      refine ⟨14806728060394717478403929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9871152040263144985602619 14806728060394717478403929)
      ·
        refine ⟨11105046045296038108802947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14806728060394717478403929 11105046045296038108802947)
        ·
          refine ⟨16657569067944057163204421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11105046045296038108802947 16657569067944057163204421)
          ·
            refine ⟨3123294200239510718100829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16657569067944057163204421 3123294200239510718100829)
            ·
              refine ⟨1171235325089816519287811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3123294200239510718100829 1171235325089816519287811)
              ·
                refine ⟨1756852987634724778931717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171235325089816519287811 1756852987634724778931717)
                ·
                  refine ⟨329409935181510896049697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1756852987634724778931717 329409935181510896049697)
                  ·
                    refine ⟨247057451386133172037273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 329409935181510896049697 247057451386133172037273)
                    ·
                      refine ⟨185293088539599879027955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 247057451386133172037273 185293088539599879027955)
                      ·
                        rfl

theorem cell23_360857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 2, 2].length) (baseStart_360857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360857 prefixEnd_360857 := by exact prefixLift 360857
  have htrace : WordTrace (prefixWord ++ tailWord_360857) baseStart_360857 baseEnd_360857 := by
    simpa [prefixWord, tailWord_360857, baseEnd_360857] using wordTrace_append hprefix tailTrace_360857
  have hstable : (prefixWord ++ tailWord_360857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360857).length < 2 ^ (prefixWord ++ tailWord_360857).sum := by decide
  have hdescent : baseEnd_360857 < baseStart_360857 := by decide
  rcases family_descends (prefixWord ++ tailWord_360857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360914 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 7]
def baseStart_360914 : Nat := 118140960795 + 360914 * 2 ^ 59
def prefixEnd_360914 : Nat := 4983230072969 + 3 ^ 40 * 360914 * 2
def baseEnd_360914 : Nat := 20591372992989572890577

theorem tailTrace_360914 : CollatzResearch.WordTrace tailWord_360914 prefixEnd_360914 20591372992989572890577 := by
  unfold tailWord_360914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3290903753619423012240449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8775743342985128032641197 3290903753619423012240449)
  ·
    refine ⟨2468177815214567259180337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3290903753619423012240449 2468177815214567259180337)
    ·
      refine ⟨1851133361410925444385253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2468177815214567259180337 1851133361410925444385253)
      ·
        refine ⟨347087505264548520822235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1851133361410925444385253 347087505264548520822235)
        ·
          refine ⟨520631257896822781233353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347087505264548520822235 520631257896822781233353)
          ·
            refine ⟨390473443422617085925015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520631257896822781233353 390473443422617085925015)
            ·
              refine ⟨585710165133925628887523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390473443422617085925015 585710165133925628887523)
              ·
                refine ⟨878565247700888443331285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585710165133925628887523 878565247700888443331285)
                ·
                  refine ⟨20591372992989572890577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 878565247700888443331285 20591372992989572890577)
                  ·
                    rfl

theorem cell23_360914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_360914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360914 prefixEnd_360914 := by exact prefixLift 360914
  have htrace : WordTrace (prefixWord ++ tailWord_360914) baseStart_360914 baseEnd_360914 := by
    simpa [prefixWord, tailWord_360914, baseEnd_360914] using wordTrace_append hprefix tailTrace_360914
  have hstable : (prefixWord ++ tailWord_360914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360914).length < 2 ^ (prefixWord ++ tailWord_360914).sum := by decide
  have hdescent : baseEnd_360914 < baseStart_360914 := by decide
  rcases family_descends (prefixWord ++ tailWord_360914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360940 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 5, 4]
def baseStart_360940 : Nat := 118140960795 + 360940 * 2 ^ 59
def prefixEnd_360940 : Nat := 4983230072969 + 3 ^ 40 * 360940 * 2
def baseEnd_360940 : Nat := 61778569144641018096691

theorem tailTrace_360940 : CollatzResearch.WordTrace tailWord_360940 prefixEnd_360940 61778569144641018096691 := by
  unfold tailWord_360940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582281656191749244704137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8776375541588998992938849 6582281656191749244704137)
  ·
    refine ⟨4936711242143811933528103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6582281656191749244704137 4936711242143811933528103)
    ·
      refine ⟨7405066863215717900292155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4936711242143811933528103 7405066863215717900292155)
      ·
        refine ⟨11107600294823576850438233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7405066863215717900292155 11107600294823576850438233)
        ·
          refine ⟨8330700221117682637828675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11107600294823576850438233 8330700221117682637828675)
          ·
            refine ⟨12496050331676523956743013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8330700221117682637828675 12496050331676523956743013)
            ·
              refine ⟨2343009437189348241889315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12496050331676523956743013 2343009437189348241889315)
              ·
                refine ⟨3514514155784022362833973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343009437189348241889315 3514514155784022362833973)
                ·
                  refine ⟨329485702104752096515685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3514514155784022362833973 329485702104752096515685)
                  ·
                    refine ⟨61778569144641018096691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 329485702104752096515685 61778569144641018096691)
                    ·
                      rfl

theorem cell23_360940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_360940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360940 prefixEnd_360940 := by exact prefixLift 360940
  have htrace : WordTrace (prefixWord ++ tailWord_360940) baseStart_360940 baseEnd_360940 := by
    simpa [prefixWord, tailWord_360940, baseEnd_360940] using wordTrace_append hprefix tailTrace_360940
  have hstable : (prefixWord ++ tailWord_360940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360940).length < 2 ^ (prefixWord ++ tailWord_360940).sum := by decide
  have hdescent : baseEnd_360940 < baseStart_360940 := by decide
  rcases family_descends (prefixWord ++ tailWord_360940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360943 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 6]
def baseStart_360943 : Nat := 118140960795 + 360943 * 2 ^ 59
def prefixEnd_360943 : Nat := 4983230072969 + 3 ^ 40 * 360943 * 2
def baseEnd_360943 : Nat := 185337247875886542552559

theorem tailTrace_360943 : CollatzResearch.WordTrace tailWord_360943 prefixEnd_360943 185337247875886542552559 := by
  unfold tailWord_360943
  simp only [CollatzResearch.WordTrace]
  refine ⟨13164672731372630001767483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8776448487581753334511655 13164672731372630001767483)
  ·
    refine ⟨19747009097058945002651225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13164672731372630001767483 19747009097058945002651225)
    ·
      refine ⟨14810256822794208751988419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19747009097058945002651225 14810256822794208751988419)
      ·
        refine ⟨22215385234191313127982629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14810256822794208751988419 22215385234191313127982629)
        ·
          refine ⟨4165384731410871211496743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22215385234191313127982629 4165384731410871211496743)
          ·
            refine ⟨6248077097116306817245115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4165384731410871211496743 6248077097116306817245115)
            ·
              refine ⟨9372115645674460225867673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6248077097116306817245115 9372115645674460225867673)
              ·
                refine ⟨7029086734255845169400755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9372115645674460225867673 7029086734255845169400755)
                ·
                  refine ⟨10543630101383767754101133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7029086734255845169400755 10543630101383767754101133)
                  ·
                    refine ⟨3953861288018912907787925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10543630101383767754101133 3953861288018912907787925)
                    ·
                      refine ⟨185337247875886542552559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3953861288018912907787925 185337247875886542552559)
                      ·
                        rfl

theorem cell23_360943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_360943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360943 prefixEnd_360943 := by exact prefixLift 360943
  have htrace : WordTrace (prefixWord ++ tailWord_360943) baseStart_360943 baseEnd_360943 := by
    simpa [prefixWord, tailWord_360943, baseEnd_360943] using wordTrace_append hprefix tailTrace_360943
  have hstable : (prefixWord ++ tailWord_360943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360943).length < 2 ^ (prefixWord ++ tailWord_360943).sum := by decide
  have hdescent : baseEnd_360943 < baseStart_360943 := by decide
  rcases family_descends (prefixWord ++ tailWord_360943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360953 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 10]
def baseStart_360953 : Nat := 118140960795 + 360953 * 2 ^ 59
def prefixEnd_360953 : Nat := 4983230072969 + 3 ^ 40 * 360953 * 2
def baseEnd_360953 : Nat := 20593598075825722603057

theorem tailTrace_360953 : CollatzResearch.WordTrace tailWord_360953 prefixEnd_360953 20593598075825722603057 := by
  unfold tailWord_360953
  simp only [CollatzResearch.WordTrace]
  refine ⟨13165037461336401709631513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8776691640890934473087675 13165037461336401709631513)
  ·
    refine ⟨9873778096002301282223635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13165037461336401709631513 9873778096002301282223635)
    ·
      refine ⟨14810667144003451923335453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9873778096002301282223635 14810667144003451923335453)
      ·
        refine ⟨5554000179001294471250795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14810667144003451923335453 5554000179001294471250795)
        ·
          refine ⟨8331000268501941706876193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5554000179001294471250795 8331000268501941706876193)
          ·
            refine ⟨6248250201376456280157145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8331000268501941706876193 6248250201376456280157145)
            ·
              refine ⟨4686187651032342210117859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6248250201376456280157145 4686187651032342210117859)
              ·
                refine ⟨7029281476548513315176789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4686187651032342210117859 7029281476548513315176789)
                ·
                  refine ⟨20593598075825722603057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 7029281476548513315176789 20593598075825722603057)
                  ·
                    rfl

theorem cell23_360953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 10].length) (baseStart_360953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360953 prefixEnd_360953 := by exact prefixLift 360953
  have htrace : WordTrace (prefixWord ++ tailWord_360953) baseStart_360953 baseEnd_360953 := by
    simpa [prefixWord, tailWord_360953, baseEnd_360953] using wordTrace_append hprefix tailTrace_360953
  have hstable : (prefixWord ++ tailWord_360953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360953).length < 2 ^ (prefixWord ++ tailWord_360953).sum := by decide
  have hdescent : baseEnd_360953 < baseStart_360953 := by decide
  rcases family_descends (prefixWord ++ tailWord_360953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360997 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 5, 1, 3]
def baseStart_360997 : Nat := 118140960795 + 360997 * 2 ^ 59
def prefixEnd_360997 : Nat := 4983230072969 + 3 ^ 40 * 360997 * 2
def baseEnd_360997 : Nat := 185364975831229331277311

theorem tailTrace_360997 : CollatzResearch.WordTrace tailWord_360997 prefixEnd_360997 185364975831229331277311 := by
  unfold tailWord_360997
  simp only [CollatzResearch.WordTrace]
  refine ⟨13166642273176997224233245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8777761515451331482822163 13166642273176997224233245)
  ·
    refine ⟨4937490852441373959087467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13166642273176997224233245 4937490852441373959087467)
    ·
      refine ⟨7406236278662060938631201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4937490852441373959087467 7406236278662060938631201)
      ·
        refine ⟨5554677208996545703973401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7406236278662060938631201 5554677208996545703973401)
        ·
          refine ⟨4166007906747409277980051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5554677208996545703973401 4166007906747409277980051)
          ·
            refine ⟨6249011860121113916970077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166007906747409277980051 6249011860121113916970077)
            ·
              refine ⟨2343379447545417718863779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6249011860121113916970077 2343379447545417718863779)
              ·
                refine ⟨3515069171318126578295669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343379447545417718863779 3515069171318126578295669)
                ·
                  refine ⟨329537734811074366715219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3515069171318126578295669 329537734811074366715219)
                  ·
                    refine ⟨494306602216611550072829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 329537734811074366715219 494306602216611550072829)
                    ·
                      refine ⟨185364975831229331277311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 494306602216611550072829 185364975831229331277311)
                      ·
                        rfl

theorem cell23_360997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_360997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360997 prefixEnd_360997 := by exact prefixLift 360997
  have htrace : WordTrace (prefixWord ++ tailWord_360997) baseStart_360997 baseEnd_360997 := by
    simpa [prefixWord, tailWord_360997, baseEnd_360997] using wordTrace_append hprefix tailTrace_360997
  have hstable : (prefixWord ++ tailWord_360997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360997).length < 2 ^ (prefixWord ++ tailWord_360997).sum := by decide
  have hdescent : baseEnd_360997 < baseStart_360997 := by decide
  rcases family_descends (prefixWord ++ tailWord_360997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361017 : List Nat := [1, 2, 1, 5, 1, 1, 3, 3, 1, 5]
def baseStart_361017 : Nat := 118140960795 + 361017 * 2 ^ 59
def prefixEnd_361017 : Nat := 4983230072969 + 3 ^ 40 * 361017 * 2
def baseEnd_361017 : Nat := 61791748481439751009073

theorem tailTrace_361017 : CollatzResearch.WordTrace tailWord_361017 prefixEnd_361017 61791748481439751009073 := by
  unfold tailWord_361017
  simp only [CollatzResearch.WordTrace]
  refine ⟨13167371733104540639961305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8778247822069693759974203 13167371733104540639961305)
  ·
    refine ⟨9875528799828405479970979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13167371733104540639961305 9875528799828405479970979)
    ·
      refine ⟨14813293199742608219956469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9875528799828405479970979 14813293199742608219956469)
      ·
        refine ⟨1388746237475869520620919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14813293199742608219956469 1388746237475869520620919)
        ·
          refine ⟨2083119356213804280931379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388746237475869520620919 2083119356213804280931379)
          ·
            refine ⟨3124679034320706421397069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083119356213804280931379 3124679034320706421397069)
            ·
              refine ⟨1171754637870264908023901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3124679034320706421397069 1171754637870264908023901)
              ·
                refine ⟨439407989201349340508963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1171754637870264908023901 439407989201349340508963)
                ·
                  refine ⟨659111983802024010763445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439407989201349340508963 659111983802024010763445)
                  ·
                    refine ⟨61791748481439751009073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 659111983802024010763445 61791748481439751009073)
                    ·
                      rfl

theorem cell23_361017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 5].length) (baseStart_361017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361017 prefixEnd_361017 := by exact prefixLift 361017
  have htrace : WordTrace (prefixWord ++ tailWord_361017) baseStart_361017 baseEnd_361017 := by
    simpa [prefixWord, tailWord_361017, baseEnd_361017] using wordTrace_append hprefix tailTrace_361017
  have hstable : (prefixWord ++ tailWord_361017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361017).length < 2 ^ (prefixWord ++ tailWord_361017).sum := by decide
  have hdescent : baseEnd_361017 < baseStart_361017 := by decide
  rcases family_descends (prefixWord ++ tailWord_361017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361031 : List Nat := [1, 1, 4, 1, 4, 1, 2, 4, 1, 1, 3]
def baseStart_361031 : Nat := 118140960795 + 361031 * 2 ^ 59
def prefixEnd_361031 : Nat := 4983230072969 + 3 ^ 40 * 361031 * 2
def baseEnd_361031 : Nat := 185382434173482198252155

theorem tailTrace_361031 : CollatzResearch.WordTrace tailWord_361031 prefixEnd_361031 185382434173482198252155 := by
  unfold tailWord_361031
  simp only [CollatzResearch.WordTrace]
  refine ⟨13167882355053821030970947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8778588236702547353980631 13167882355053821030970947)
  ·
    refine ⟨19751823532580731546456421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13167882355053821030970947 19751823532580731546456421)
    ·
      refine ⟨3703466912358887164960579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19751823532580731546456421 3703466912358887164960579)
      ·
        refine ⟨5555200368538330747440869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3703466912358887164960579 5555200368538330747440869)
        ·
          refine ⟨1041600069100937015145163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5555200368538330747440869 1041600069100937015145163)
          ·
            refine ⟨1562400103651405522717745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041600069100937015145163 1562400103651405522717745)
            ·
              refine ⟨1171800077738554142038309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562400103651405522717745 1171800077738554142038309)
              ·
                refine ⟨219712514575978901632183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1171800077738554142038309 219712514575978901632183)
                ·
                  refine ⟨329568771863968352448275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219712514575978901632183 329568771863968352448275)
                  ·
                    refine ⟨494353157795952528672413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 329568771863968352448275 494353157795952528672413)
                    ·
                      refine ⟨185382434173482198252155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 494353157795952528672413 185382434173482198252155)
                      ·
                        rfl

theorem cell23_361031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_361031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361031 prefixEnd_361031 := by exact prefixLift 361031
  have htrace : WordTrace (prefixWord ++ tailWord_361031) baseStart_361031 baseEnd_361031 := by
    simpa [prefixWord, tailWord_361031, baseEnd_361031] using wordTrace_append hprefix tailTrace_361031
  have hstable : (prefixWord ++ tailWord_361031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361031).length < 2 ^ (prefixWord ++ tailWord_361031).sum := by decide
  have hdescent : baseEnd_361031 < baseStart_361031 := by decide
  rcases family_descends (prefixWord ++ tailWord_361031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361040 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 3]
def baseStart_361040 : Nat := 118140960795 + 361040 * 2 ^ 59
def prefixEnd_361040 : Nat := 4983230072969 + 3 ^ 40 * 361040 * 2
def baseEnd_361040 : Nat := 185387055499372663039613

theorem tailTrace_361040 : CollatzResearch.WordTrace tailWord_361040 prefixEnd_361040 185387055499372663039613 := by
  unfold tailWord_361040
  simp only [CollatzResearch.WordTrace]
  refine ⟨6584105306010607784024287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8778807074680810378699049 6584105306010607784024287)
  ·
    refine ⟨9876157959015911676036431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6584105306010607784024287 9876157959015911676036431)
    ·
      refine ⟨14814236938523867514054647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9876157959015911676036431 14814236938523867514054647)
      ·
        refine ⟨22221355407785801271081971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14814236938523867514054647 22221355407785801271081971)
        ·
          refine ⟨33332033111678701906622957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22221355407785801271081971 33332033111678701906622957)
          ·
            refine ⟨12499512416879513214983609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33332033111678701906622957 12499512416879513214983609)
            ·
              refine ⟨9374634312659634911237707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12499512416879513214983609 9374634312659634911237707)
              ·
                refine ⟨14061951468989452366856561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9374634312659634911237707 14061951468989452366856561)
                ·
                  refine ⟨10546463601742089275142421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14061951468989452366856561 10546463601742089275142421)
                  ·
                    refine ⟨494365481331660434772301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10546463601742089275142421 494365481331660434772301)
                    ·
                      refine ⟨185387055499372663039613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 494365481331660434772301 185387055499372663039613)
                      ·
                        rfl

theorem cell23_361040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 3].length) (baseStart_361040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361040 prefixEnd_361040 := by exact prefixLift 361040
  have htrace : WordTrace (prefixWord ++ tailWord_361040) baseStart_361040 baseEnd_361040 := by
    simpa [prefixWord, tailWord_361040, baseEnd_361040] using wordTrace_append hprefix tailTrace_361040
  have hstable : (prefixWord ++ tailWord_361040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361040).length < 2 ^ (prefixWord ++ tailWord_361040).sum := by decide
  have hdescent : baseEnd_361040 < baseStart_361040 := by decide
  rcases family_descends (prefixWord ++ tailWord_361040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361060 : List Nat := [2, 3, 1, 1, 2, 2, 3, 9]
def baseStart_361060 : Nat := 118140960795 + 361060 * 2 ^ 59
def prefixEnd_361060 : Nat := 4983230072969 + 3 ^ 40 * 361060 * 2
def baseEnd_361060 : Nat := 6866567596757873510723

theorem tailTrace_361060 : CollatzResearch.WordTrace tailWord_361060 prefixEnd_361060 6866567596757873510723 := by
  unfold tailWord_361060
  simp only [CollatzResearch.WordTrace]
  refine ⟨6584470035974379491888317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8779293381299172655851089 6584470035974379491888317)
  ·
    refine ⟨2469176263490392309458119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6584470035974379491888317 2469176263490392309458119)
    ·
      refine ⟨3703764395235588464187179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2469176263490392309458119 3703764395235588464187179)
      ·
        refine ⟨5555646592853382696280769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3703764395235588464187179 5555646592853382696280769)
        ·
          refine ⟨4166734944640037022210577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5555646592853382696280769 4166734944640037022210577)
          ·
            refine ⟨3125051208480027766657933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4166734944640037022210577 3125051208480027766657933)
            ·
              refine ⟨1171894203180010412496725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3125051208480027766657933 1171894203180010412496725)
              ·
                refine ⟨6866567596757873510723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1171894203180010412496725 6866567596757873510723)
                ·
                  rfl

theorem cell23_361060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 9].length) (baseStart_361060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361060 prefixEnd_361060 := by exact prefixLift 361060
  have htrace : WordTrace (prefixWord ++ tailWord_361060) baseStart_361060 baseEnd_361060 := by
    simpa [prefixWord, tailWord_361060, baseEnd_361060] using wordTrace_append hprefix tailTrace_361060
  have hstable : (prefixWord ++ tailWord_361060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361060).length < 2 ^ (prefixWord ++ tailWord_361060).sum := by decide
  have hdescent : baseEnd_361060 < baseStart_361060 := by decide
  rcases family_descends (prefixWord ++ tailWord_361060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361074 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_361074 : Nat := 118140960795 + 361074 * 2 ^ 59
def prefixEnd_361074 : Nat := 4983230072969 + 3 ^ 40 * 361074 * 2
def baseEnd_361074 : Nat := 185404513841625530014457

theorem tailTrace_361074 : CollatzResearch.WordTrace tailWord_361074 prefixEnd_361074 185404513841625530014457 := by
  unfold tailWord_361074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3292362673474509843696569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8779633795932026249857517 3292362673474509843696569)
  ·
    refine ⟨2469272005105882382772427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3292362673474509843696569 2469272005105882382772427)
    ·
      refine ⟨3703908007658823574158641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2469272005105882382772427 3703908007658823574158641)
      ·
        refine ⟨2777931005744117680618981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3703908007658823574158641 2777931005744117680618981)
        ·
          refine ⟨520862063577022065116059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2777931005744117680618981 520862063577022065116059)
          ·
            refine ⟨781293095365533097674089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520862063577022065116059 781293095365533097674089)
            ·
              refine ⟨585969821524149823255567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781293095365533097674089 585969821524149823255567)
              ·
                refine ⟨878954732286224734883351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585969821524149823255567 878954732286224734883351)
                ·
                  refine ⟨1318432098429337102325027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 878954732286224734883351 1318432098429337102325027)
                  ·
                    refine ⟨1977648147644005653487541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1318432098429337102325027 1977648147644005653487541)
                    ·
                      refine ⟨185404513841625530014457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1977648147644005653487541 185404513841625530014457)
                      ·
                        rfl

theorem cell23_361074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_361074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361074 prefixEnd_361074 := by exact prefixLift 361074
  have htrace : WordTrace (prefixWord ++ tailWord_361074) baseStart_361074 baseEnd_361074 := by
    simpa [prefixWord, tailWord_361074, baseEnd_361074] using wordTrace_append hprefix tailTrace_361074
  have hstable : (prefixWord ++ tailWord_361074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361074).length < 2 ^ (prefixWord ++ tailWord_361074).sum := by decide
  have hdescent : baseEnd_361074 < baseStart_361074 := by decide
  rcases family_descends (prefixWord ++ tailWord_361074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361097 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 2, 7, 2]
def baseStart_361097 : Nat := 118140960795 + 361097 * 2 ^ 59
def prefixEnd_361097 : Nat := 4983230072969 + 3 ^ 40 * 361097 * 2
def baseEnd_361097 : Nat := 185416323896678940026851

theorem tailTrace_361097 : CollatzResearch.WordTrace tailWord_361097 prefixEnd_361097 185416323896678940026851 := by
  unfold tailWord_361097
  simp only [CollatzResearch.WordTrace]
  refine ⟨13170289572814714302873545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8780193048543142868582363 13170289572814714302873545)
  ·
    refine ⟨9877717179611035727155159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13170289572814714302873545 9877717179611035727155159)
    ·
      refine ⟨14816575769416553590732739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9877717179611035727155159 14816575769416553590732739)
      ·
        refine ⟨22224863654124830386099109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14816575769416553590732739 22224863654124830386099109)
        ·
          refine ⟨4167161935148405697393583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22224863654124830386099109 4167161935148405697393583)
          ·
            refine ⟨6250742902722608546090375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4167161935148405697393583 6250742902722608546090375)
            ·
              refine ⟨9376114354083912819135563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6250742902722608546090375 9376114354083912819135563)
              ·
                refine ⟨14064171531125869228703345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9376114354083912819135563 14064171531125869228703345)
                ·
                  refine ⟨10548128648344401921527509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14064171531125869228703345 10548128648344401921527509)
                  ·
                    refine ⟨247221765195571920035801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10548128648344401921527509 247221765195571920035801)
                    ·
                      refine ⟨185416323896678940026851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 247221765195571920035801 185416323896678940026851)
                      ·
                        rfl

theorem cell23_361097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 7, 2].length) (baseStart_361097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361097 prefixEnd_361097 := by exact prefixLift 361097
  have htrace : WordTrace (prefixWord ++ tailWord_361097) baseStart_361097 baseEnd_361097 := by
    simpa [prefixWord, tailWord_361097, baseEnd_361097] using wordTrace_append hprefix tailTrace_361097
  have hstable : (prefixWord ++ tailWord_361097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361097).length < 2 ^ (prefixWord ++ tailWord_361097).sum := by decide
  have hdescent : baseEnd_361097 < baseStart_361097 := by decide
  rcases family_descends (prefixWord ++ tailWord_361097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361098 : List Nat := [3, 1, 2, 3, 3, 2, 2, 1, 2, 4]
def baseStart_361098 : Nat := 118140960795 + 361098 * 2 ^ 59
def prefixEnd_361098 : Nat := 4983230072969 + 3 ^ 40 * 361098 * 2
def baseEnd_361098 : Nat := 61805612459111145371449

theorem tailTrace_361098 : CollatzResearch.WordTrace tailWord_361098 prefixEnd_361098 61805612459111145371449 := by
  unfold tailWord_361098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3292581511452772868414987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8780217363874060982439965 3292581511452772868414987)
  ·
    refine ⟨4938872267179159302622481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3292581511452772868414987 4938872267179159302622481)
    ·
      refine ⟨3704154200384369476966861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4938872267179159302622481 3704154200384369476966861)
      ·
        refine ⟨1389057825144138553862573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3704154200384369476966861 1389057825144138553862573)
        ·
          refine ⟨520896684429051957698465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1389057825144138553862573 520896684429051957698465)
          ·
            refine ⟨390672513321788968273849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520896684429051957698465 390672513321788968273849)
            ·
              refine ⟨293004384991341726205387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390672513321788968273849 293004384991341726205387)
              ·
                refine ⟨439506577487012589308081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293004384991341726205387 439506577487012589308081)
                ·
                  refine ⟨329629933115259441981061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439506577487012589308081 329629933115259441981061)
                  ·
                    refine ⟨61805612459111145371449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 329629933115259441981061 61805612459111145371449)
                    ·
                      rfl

theorem cell23_361098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_361098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361098 prefixEnd_361098 := by exact prefixLift 361098
  have htrace : WordTrace (prefixWord ++ tailWord_361098) baseStart_361098 baseEnd_361098 := by
    simpa [prefixWord, tailWord_361098, baseEnd_361098] using wordTrace_append hprefix tailTrace_361098
  have hstable : (prefixWord ++ tailWord_361098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361098).length < 2 ^ (prefixWord ++ tailWord_361098).sum := by decide
  have hdescent : baseEnd_361098 < baseStart_361098 := by decide
  rcases family_descends (prefixWord ++ tailWord_361098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361100 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_361100 : Nat := 118140960795 + 361100 * 2 ^ 59
def prefixEnd_361100 : Nat := 4983230072969 + 3 ^ 40 * 361100 * 2
def baseEnd_361100 : Nat := 185417864338642428289337

theorem tailTrace_361100 : CollatzResearch.WordTrace tailWord_361100 prefixEnd_361100 185417864338642428289337 := by
  unfold tailWord_361100
  simp only [CollatzResearch.WordTrace]
  refine ⟨6585199495901922907616377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8780265994535897210155169 6585199495901922907616377)
  ·
    refine ⟨4938899621926442180712283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6585199495901922907616377 4938899621926442180712283)
    ·
      refine ⟨7408349432889663271068425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4938899621926442180712283 7408349432889663271068425)
      ·
        refine ⟨5556262074667247453301319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7408349432889663271068425 5556262074667247453301319)
        ·
          refine ⟨8334393112000871179951979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5556262074667247453301319 8334393112000871179951979)
          ·
            refine ⟨12501589668001306769927969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8334393112000871179951979 12501589668001306769927969)
            ·
              refine ⟨9376192251000980077445977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12501589668001306769927969 9376192251000980077445977)
              ·
                refine ⟨7032144188250735058084483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9376192251000980077445977 7032144188250735058084483)
                ·
                  refine ⟨10548216282376102587126725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7032144188250735058084483 10548216282376102587126725)
                  ·
                    refine ⟨1977790552945519235086261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10548216282376102587126725 1977790552945519235086261)
                    ·
                      refine ⟨185417864338642428289337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1977790552945519235086261 185417864338642428289337)
                      ·
                        rfl

theorem cell23_361100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_361100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361100 prefixEnd_361100 := by exact prefixLift 361100
  have htrace : WordTrace (prefixWord ++ tailWord_361100) baseStart_361100 baseEnd_361100 := by
    simpa [prefixWord, tailWord_361100, baseEnd_361100] using wordTrace_append hprefix tailTrace_361100
  have hstable : (prefixWord ++ tailWord_361100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361100).length < 2 ^ (prefixWord ++ tailWord_361100).sum := by decide
  have hdescent : baseEnd_361100 < baseStart_361100 := by decide
  rcases family_descends (prefixWord ++ tailWord_361100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361108 : List Nat := [2, 4, 2, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_361108 : Nat := 118140960795 + 361108 * 2 ^ 59
def prefixEnd_361108 : Nat := 4983230072969 + 3 ^ 40 * 361108 * 2
def baseEnd_361108 : Nat := 185421972183878396989301

theorem tailTrace_361108 : CollatzResearch.WordTrace tailWord_361108 prefixEnd_361108 185421972183878396989301 := by
  unfold tailWord_361108
  simp only [CollatzResearch.WordTrace]
  refine ⟨6585345387887431590761989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8780460517183242121015985 6585345387887431590761989)
  ·
    refine ⟨1234752260228893423267873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6585345387887431590761989 1234752260228893423267873)
    ·
      refine ⟨926064195171670067450905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1234752260228893423267873 926064195171670067450905)
      ·
        refine ⟨694548146378752550588179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 926064195171670067450905 694548146378752550588179)
        ·
          refine ⟨1041822219568128825882269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694548146378752550588179 1041822219568128825882269)
          ·
            refine ⟨390683332338048309705851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1041822219568128825882269 390683332338048309705851)
            ·
              refine ⟨586024998507072464558777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390683332338048309705851 586024998507072464558777)
              ·
                refine ⟨439518748880304348419083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586024998507072464558777 439518748880304348419083)
                ·
                  refine ⟨659278123320456522628625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439518748880304348419083 659278123320456522628625)
                  ·
                    refine ⟨494458592490342391971469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 659278123320456522628625 494458592490342391971469)
                    ·
                      refine ⟨185421972183878396989301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 494458592490342391971469 185421972183878396989301)
                      ·
                        rfl

theorem cell23_361108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_361108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361108 prefixEnd_361108 := by exact prefixLift 361108
  have htrace : WordTrace (prefixWord ++ tailWord_361108) baseStart_361108 baseEnd_361108 := by
    simpa [prefixWord, tailWord_361108, baseEnd_361108] using wordTrace_append hprefix tailTrace_361108
  have hstable : (prefixWord ++ tailWord_361108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361108).length < 2 ^ (prefixWord ++ tailWord_361108).sum := by decide
  have hdescent : baseEnd_361108 < baseStart_361108 := by decide
  rcases family_descends (prefixWord ++ tailWord_361108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361177 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 1, 5, 3]
def baseStart_361177 : Nat := 118140960795 + 361177 * 2 ^ 59
def prefixEnd_361177 : Nat := 4983230072969 + 3 ^ 40 * 361177 * 2
def baseEnd_361177 : Nat := 185457402349038627026483

theorem tailTrace_361177 : CollatzResearch.WordTrace tailWord_361177 prefixEnd_361177 185457402349038627026483 := by
  unfold tailWord_361177
  simp only [CollatzResearch.WordTrace]
  refine ⟨13173207412524887965785785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8782138275016591977190523 13173207412524887965785785)
  ·
    refine ⟨9879905559393665974339339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13173207412524887965785785 9879905559393665974339339)
    ·
      refine ⟨14819858339090498961509009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9879905559393665974339339 14819858339090498961509009)
      ·
        refine ⟨11114893754317874221131757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14819858339090498961509009 11114893754317874221131757)
        ·
          refine ⟨4168085157869202832924409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11114893754317874221131757 4168085157869202832924409)
          ·
            refine ⟨3126063868401902124693307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4168085157869202832924409 3126063868401902124693307)
            ·
              refine ⟨4689095802602853187039961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3126063868401902124693307 4689095802602853187039961)
              ·
                refine ⟨3516821851952139890279971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4689095802602853187039961 3516821851952139890279971)
                ·
                  refine ⟨5275232777928209835419957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3516821851952139890279971 5275232777928209835419957)
                  ·
                    refine ⟨494553072930769672070621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5275232777928209835419957 494553072930769672070621)
                    ·
                      refine ⟨185457402349038627026483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 494553072930769672070621 185457402349038627026483)
                      ·
                        rfl

theorem cell23_361177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_361177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361177 prefixEnd_361177 := by exact prefixLift 361177
  have htrace : WordTrace (prefixWord ++ tailWord_361177) baseStart_361177 baseEnd_361177 := by
    simpa [prefixWord, tailWord_361177, baseEnd_361177] using wordTrace_append hprefix tailTrace_361177
  have hstable : (prefixWord ++ tailWord_361177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361177).length < 2 ^ (prefixWord ++ tailWord_361177).sum := by decide
  have hdescent : baseEnd_361177 < baseStart_361177 := by decide
  rcases family_descends (prefixWord ++ tailWord_361177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361214 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_361214 : Nat := 118140960795 + 361214 * 2 ^ 59
def prefixEnd_361214 : Nat := 4983230072969 + 3 ^ 40 * 361214 * 2
def baseEnd_361214 : Nat := 61825467044418327421271

theorem tailTrace_361214 : CollatzResearch.WordTrace tailWord_361214 prefixEnd_361214 61825467044418327421271 := by
  unfold tailWord_361214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646819614173855410610337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8783037942260562189921797 1646819614173855410610337)
  ·
    refine ⟨1235114710630391557957753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1646819614173855410610337 1235114710630391557957753)
    ·
      refine ⟨926336032972793668468315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1235114710630391557957753 926336032972793668468315)
      ·
        refine ⟨1389504049459190502702473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926336032972793668468315 1389504049459190502702473)
        ·
          refine ⟨1042128037094392877026855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1389504049459190502702473 1042128037094392877026855)
          ·
            refine ⟨1563192055641589315540283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042128037094392877026855 1563192055641589315540283)
            ·
              refine ⟨2344788083462383973310425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563192055641589315540283 2344788083462383973310425)
              ·
                refine ⟨1758591062596787979982819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344788083462383973310425 1758591062596787979982819)
                ·
                  refine ⟨2637886593895181969974229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758591062596787979982819 2637886593895181969974229)
                  ·
                    refine ⟨61825467044418327421271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2637886593895181969974229 61825467044418327421271)
                    ·
                      rfl

theorem cell23_361214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_361214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361214 prefixEnd_361214 := by exact prefixLift 361214
  have htrace : WordTrace (prefixWord ++ tailWord_361214) baseStart_361214 baseEnd_361214 := by
    simpa [prefixWord, tailWord_361214, baseEnd_361214] using wordTrace_append hprefix tailTrace_361214
  have hstable : (prefixWord ++ tailWord_361214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361214).length < 2 ^ (prefixWord ++ tailWord_361214).sum := by decide
  have hdescent : baseEnd_361214 < baseStart_361214 := by decide
  rcases family_descends (prefixWord ++ tailWord_361214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361304 : List Nat := [2, 1, 2, 2, 1, 1, 1, 7, 1, 5]
def baseStart_361304 : Nat := 118140960795 + 361304 * 2 ^ 59
def prefixEnd_361304 : Nat := 4983230072969 + 3 ^ 40 * 361304 * 2
def baseEnd_361304 : Nat := 61840871464053210046133

theorem tailTrace_361304 : CollatzResearch.WordTrace tailWord_361304 prefixEnd_361304 61840871464053210046133 := by
  unfold tailWord_361304
  simp only [CollatzResearch.WordTrace]
  refine ⟨6588919741532394327829483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8785226322043192437105977 6588919741532394327829483)
  ·
    refine ⟨9883379612298591491744225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6588919741532394327829483 9883379612298591491744225)
    ·
      refine ⟨7412534709223943618808169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9883379612298591491744225 7412534709223943618808169)
      ·
        refine ⟨5559401031917957714106127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7412534709223943618808169 5559401031917957714106127)
        ·
          refine ⟨8339101547876936571159191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5559401031917957714106127 8339101547876936571159191)
          ·
            refine ⟨12508652321815404856738787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8339101547876936571159191 12508652321815404856738787)
            ·
              refine ⟨18762978482723107285108181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12508652321815404856738787 18762978482723107285108181)
              ·
                refine ⟨439757308188822826994723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18762978482723107285108181 439757308188822826994723)
                ·
                  refine ⟨659635962283234240492085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439757308188822826994723 659635962283234240492085)
                  ·
                    refine ⟨61840871464053210046133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 659635962283234240492085 61840871464053210046133)
                    ·
                      rfl

theorem cell23_361304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_361304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361304 prefixEnd_361304 := by exact prefixLift 361304
  have htrace : WordTrace (prefixWord ++ tailWord_361304) baseStart_361304 baseEnd_361304 := by
    simpa [prefixWord, tailWord_361304, baseEnd_361304] using wordTrace_append hprefix tailTrace_361304
  have hstable : (prefixWord ++ tailWord_361304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361304).length < 2 ^ (prefixWord ++ tailWord_361304).sum := by decide
  have hdescent : baseEnd_361304 < baseStart_361304 := by decide
  rcases family_descends (prefixWord ++ tailWord_361304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361307 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 4]
def baseStart_361307 : Nat := 118140960795 + 361307 * 2 ^ 59
def prefixEnd_361307 : Nat := 4983230072969 + 3 ^ 40 * 361307 * 2
def baseEnd_361307 : Nat := 185524154834123118400885

theorem tailTrace_361307 : CollatzResearch.WordTrace tailWord_361307 prefixEnd_361307 185524154834123118400885 := by
  unfold tailWord_361307
  simp only [CollatzResearch.WordTrace]
  refine ⟨13177948902053920168018175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8785299268035946778678783 13177948902053920168018175)
  ·
    refine ⟨19766923353080880252027263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13177948902053920168018175 19766923353080880252027263)
    ·
      refine ⟨29650385029621320378040895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19766923353080880252027263 29650385029621320378040895)
      ·
        refine ⟨44475577544431980567061343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29650385029621320378040895 44475577544431980567061343)
        ·
          refine ⟨66713366316647970850592015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44475577544431980567061343 66713366316647970850592015)
          ·
            refine ⟨100070049474971956275888023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66713366316647970850592015 100070049474971956275888023)
            ·
              refine ⟨150105074212457934413832035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100070049474971956275888023 150105074212457934413832035)
              ·
                refine ⟨225157611318686901620748053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150105074212457934413832035 225157611318686901620748053)
                ·
                  refine ⟨10554263030563448513472565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 225157611318686901620748053 10554263030563448513472565)
                  ·
                    refine ⟨989462159115323298138053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10554263030563448513472565 989462159115323298138053)
                    ·
                      refine ⟨185524154834123118400885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 989462159115323298138053 185524154834123118400885)
                      ·
                        rfl

theorem cell23_361307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 4].length) (baseStart_361307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361307 prefixEnd_361307 := by exact prefixLift 361307
  have htrace : WordTrace (prefixWord ++ tailWord_361307) baseStart_361307 baseEnd_361307 := by
    simpa [prefixWord, tailWord_361307, baseEnd_361307] using wordTrace_append hprefix tailTrace_361307
  have hstable : (prefixWord ++ tailWord_361307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361307).length < 2 ^ (prefixWord ++ tailWord_361307).sum := by decide
  have hdescent : baseEnd_361307 < baseStart_361307 := by decide
  rcases family_descends (prefixWord ++ tailWord_361307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361311 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 2, 3, 2]
def baseStart_361311 : Nat := 118140960795 + 361311 * 2 ^ 59
def prefixEnd_361311 : Nat := 4983230072969 + 3 ^ 40 * 361311 * 2
def baseEnd_361311 : Nat := 185526208756741102750867

theorem tailTrace_361311 : CollatzResearch.WordTrace tailWord_361311 prefixEnd_361311 185526208756741102750867 := by
  unfold tailWord_361311
  simp only [CollatzResearch.WordTrace]
  refine ⟨13178094794039428851163787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8785396529359619234109191 13178094794039428851163787)
  ·
    refine ⟨19767142191059143276745681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13178094794039428851163787 19767142191059143276745681)
    ·
      refine ⟨14825356643294357457559261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19767142191059143276745681 14825356643294357457559261)
      ·
        refine ⟨5559508741235384046584723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14825356643294357457559261 5559508741235384046584723)
        ·
          refine ⟨8339263111853076069877085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5559508741235384046584723 8339263111853076069877085)
          ·
            refine ⟨3127223666944903526203907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8339263111853076069877085 3127223666944903526203907)
            ·
              refine ⟨4690835500417355289305861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127223666944903526203907 4690835500417355289305861)
              ·
                refine ⟨879531656328254116744849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4690835500417355289305861 879531656328254116744849)
                ·
                  refine ⟨659648742246190587558637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 879531656328254116744849 659648742246190587558637)
                  ·
                    refine ⟨247368278342321470334489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 659648742246190587558637 247368278342321470334489)
                    ·
                      refine ⟨185526208756741102750867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 247368278342321470334489 185526208756741102750867)
                      ·
                        rfl

theorem cell23_361311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_361311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361311 prefixEnd_361311 := by exact prefixLift 361311
  have htrace : WordTrace (prefixWord ++ tailWord_361311) baseStart_361311 baseEnd_361311 := by
    simpa [prefixWord, tailWord_361311, baseEnd_361311] using wordTrace_append hprefix tailTrace_361311
  have hstable : (prefixWord ++ tailWord_361311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361311).length < 2 ^ (prefixWord ++ tailWord_361311).sum := by decide
  have hdescent : baseEnd_361311 < baseStart_361311 := by decide
  rcases family_descends (prefixWord ++ tailWord_361311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361324 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_361324 : Nat := 118140960795 + 361324 * 2 ^ 59
def prefixEnd_361324 : Nat := 4983230072969 + 3 ^ 40 * 361324 * 2
def baseEnd_361324 : Nat := 185532884005249551888307

theorem tailTrace_361324 : CollatzResearch.WordTrace tailWord_361324 prefixEnd_361324 185532884005249551888307 := by
  unfold tailWord_361324
  simp only [CollatzResearch.WordTrace]
  refine ⟨6589284471496166035693513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8785712628661554714258017 6589284471496166035693513)
  ·
    refine ⟨4941963353622124526770135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6589284471496166035693513 4941963353622124526770135)
    ·
      refine ⟨7412945030433186790155203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4941963353622124526770135 7412945030433186790155203)
      ·
        refine ⟨11119417545649780185232805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7412945030433186790155203 11119417545649780185232805)
        ·
          refine ⟨2084890789809333784731151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11119417545649780185232805 2084890789809333784731151)
          ·
            refine ⟨3127336184714000677096727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2084890789809333784731151 3127336184714000677096727)
            ·
              refine ⟨4691004277071001015645091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127336184714000677096727 4691004277071001015645091)
              ·
                refine ⟨7036506415606501523467637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4691004277071001015645091 7036506415606501523467637)
                ·
                  refine ⟨659672476463109517825091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7036506415606501523467637 659672476463109517825091)
                  ·
                    refine ⟨989508714694664276737637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 659672476463109517825091 989508714694664276737637)
                    ·
                      refine ⟨185532884005249551888307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 989508714694664276737637 185532884005249551888307)
                      ·
                        rfl

theorem cell23_361324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_361324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361324 prefixEnd_361324 := by exact prefixLift 361324
  have htrace : WordTrace (prefixWord ++ tailWord_361324) baseStart_361324 baseEnd_361324 := by
    simpa [prefixWord, tailWord_361324, baseEnd_361324] using wordTrace_append hprefix tailTrace_361324
  have hstable : (prefixWord ++ tailWord_361324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361324).length < 2 ^ (prefixWord ++ tailWord_361324).sum := by decide
  have hdescent : baseEnd_361324 < baseStart_361324 := by decide
  rcases family_descends (prefixWord ++ tailWord_361324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361364 : List Nat := [2, 4, 2, 1, 1, 1, 12]
def baseStart_361364 : Nat := 118140960795 + 361364 * 2 ^ 59
def prefixEnd_361364 : Nat := 4983230072969 + 3 ^ 40 * 361364 * 2
def baseEnd_361364 : Nat := 2290783002857153029483

theorem tailTrace_361364 : CollatzResearch.WordTrace tailWord_361364 prefixEnd_361364 2290783002857153029483 := by
  unfold tailWord_361364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6590013931423709451421573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8786685241898279268562097 6590013931423709451421573)
  ·
    refine ⟨1235627612141945522141545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6590013931423709451421573 1235627612141945522141545)
    ·
      refine ⟨926720709106459141606159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1235627612141945522141545 926720709106459141606159)
      ·
        refine ⟨1390081063659688712409239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926720709106459141606159 1390081063659688712409239)
        ·
          refine ⟨2085121595489533068613859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390081063659688712409239 2085121595489533068613859)
          ·
            refine ⟨3127682393234299602920789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085121595489533068613859 3127682393234299602920789)
            ·
              refine ⟨2290783002857153029483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 3127682393234299602920789 2290783002857153029483)
              ·
                rfl

theorem cell23_361364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 12].length) (baseStart_361364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361364 prefixEnd_361364 := by exact prefixLift 361364
  have htrace : WordTrace (prefixWord ++ tailWord_361364) baseStart_361364 baseEnd_361364 := by
    simpa [prefixWord, tailWord_361364, baseEnd_361364] using wordTrace_append hprefix tailTrace_361364
  have hstable : (prefixWord ++ tailWord_361364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361364).length < 2 ^ (prefixWord ++ tailWord_361364).sum := by decide
  have hdescent : baseEnd_361364 < baseStart_361364 := by decide
  rcases family_descends (prefixWord ++ tailWord_361364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361375 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 3, 2, 2]
def baseStart_361375 : Nat := 118140960795 + 361375 * 2 ^ 59
def prefixEnd_361375 : Nat := 4983230072969 + 3 ^ 40 * 361375 * 2
def baseEnd_361375 : Nat := 185559071518628852350573

theorem tailTrace_361375 : CollatzResearch.WordTrace tailWord_361375 prefixEnd_361375 185559071518628852350573 := by
  unfold tailWord_361375
  simp only [CollatzResearch.WordTrace]
  refine ⟨13180429065807567781493579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8786952710538378520995719 13180429065807567781493579)
  ·
    refine ⟨19770643598711351672240369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13180429065807567781493579 19770643598711351672240369)
    ·
      refine ⟨14827982699033513754180277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19770643598711351672240369 14827982699033513754180277)
      ·
        refine ⟨1390123378034391914454401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14827982699033513754180277 1390123378034391914454401)
        ·
          refine ⟨1042592533525793935840801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1390123378034391914454401 1042592533525793935840801)
          ·
            refine ⟨781944400144345451880601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1042592533525793935840801 781944400144345451880601)
            ·
              refine ⟨586458300108259088910451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781944400144345451880601 586458300108259088910451)
              ·
                refine ⟨879687450162388633365677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 586458300108259088910451 879687450162388633365677)
                ·
                  refine ⟨329882793810895737512129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879687450162388633365677 329882793810895737512129)
                  ·
                    refine ⟨247412095358171803134097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 329882793810895737512129 247412095358171803134097)
                    ·
                      refine ⟨185559071518628852350573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 247412095358171803134097 185559071518628852350573)
                      ·
                        rfl

theorem cell23_361375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_361375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361375 prefixEnd_361375 := by exact prefixLift 361375
  have htrace : WordTrace (prefixWord ++ tailWord_361375) baseStart_361375 baseEnd_361375 := by
    simpa [prefixWord, tailWord_361375, baseEnd_361375] using wordTrace_append hprefix tailTrace_361375
  have hstable : (prefixWord ++ tailWord_361375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361375).length < 2 ^ (prefixWord ++ tailWord_361375).sum := by decide
  have hdescent : baseEnd_361375 < baseStart_361375 := by decide
  rcases family_descends (prefixWord ++ tailWord_361375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361431 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 5, 4, 2]
def baseStart_361431 : Nat := 118140960795 + 361431 * 2 ^ 59
def prefixEnd_361431 : Nat := 4983230072969 + 3 ^ 40 * 361431 * 2
def baseEnd_361431 : Nat := 185587826435280633250315

theorem tailTrace_361431 : CollatzResearch.WordTrace tailWord_361431 prefixEnd_361431 185587826435280633250315 := by
  unfold tailWord_361431
  simp only [CollatzResearch.WordTrace]
  refine ⟨13182471553604689345532147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8788314369069792897021431 13182471553604689345532147)
  ·
    refine ⟨19773707330407034018298221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13182471553604689345532147 19773707330407034018298221)
    ·
      refine ⟨7415140248902637756861833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19773707330407034018298221 7415140248902637756861833)
      ·
        refine ⟨5561355186676978317646375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7415140248902637756861833 5561355186676978317646375)
        ·
          refine ⟨8342032780015467476469563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5561355186676978317646375 8342032780015467476469563)
          ·
            refine ⟨12513049170023201214704345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8342032780015467476469563 12513049170023201214704345)
            ·
              refine ⟨9384786877517400911028259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12513049170023201214704345 9384786877517400911028259)
              ·
                refine ⟨14077180316276101366542389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9384786877517400911028259 14077180316276101366542389)
                ·
                  refine ⟨1319735654650884503113349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14077180316276101366542389 1319735654650884503113349)
                  ·
                    refine ⟨247450435247040844333753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1319735654650884503113349 247450435247040844333753)
                    ·
                      refine ⟨185587826435280633250315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 247450435247040844333753 185587826435280633250315)
                      ·
                        rfl

theorem cell23_361431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_361431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361431 prefixEnd_361431 := by exact prefixLift 361431
  have htrace : WordTrace (prefixWord ++ tailWord_361431) baseStart_361431 baseEnd_361431 := by
    simpa [prefixWord, tailWord_361431, baseEnd_361431] using wordTrace_append hprefix tailTrace_361431
  have hstable : (prefixWord ++ tailWord_361431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361431).length < 2 ^ (prefixWord ++ tailWord_361431).sum := by decide
  have hdescent : baseEnd_361431 < baseStart_361431 := by decide
  rcases family_descends (prefixWord ++ tailWord_361431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361442 : List Nat := [3, 3, 3, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_361442 : Nat := 118140960795 + 361442 * 2 ^ 59
def prefixEnd_361442 : Nat := 4983230072969 + 3 ^ 40 * 361442 * 2
def baseEnd_361442 : Nat := 185593474722480090212765

theorem tailTrace_361442 : CollatzResearch.WordTrace tailWord_361442 prefixEnd_361442 185593474722480090212765 := by
  unfold tailWord_361442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295718189141209556045645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8788581837709892149455053 3295718189141209556045645)
  ·
    refine ⟨1235894320927953583517117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3295718189141209556045645 1235894320927953583517117)
    ·
      refine ⟨463460370347982593818919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1235894320927953583517117 463460370347982593818919)
      ·
        refine ⟨695190555521973890728379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463460370347982593818919 695190555521973890728379)
        ·
          refine ⟨1042785833282960836092569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695190555521973890728379 1042785833282960836092569)
          ·
            refine ⟨782089374962220627069427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1042785833282960836092569 782089374962220627069427)
            ·
              refine ⟨1173134062443330940604141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782089374962220627069427 1173134062443330940604141)
              ·
                refine ⟨439925273416249102726553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1173134062443330940604141 439925273416249102726553)
                ·
                  refine ⟨329943955062186827044915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439925273416249102726553 329943955062186827044915)
                  ·
                    refine ⟨494915932593280240567373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 329943955062186827044915 494915932593280240567373)
                    ·
                      refine ⟨185593474722480090212765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 494915932593280240567373 185593474722480090212765)
                      ·
                        rfl

theorem cell23_361442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_361442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361442 prefixEnd_361442 := by exact prefixLift 361442
  have htrace : WordTrace (prefixWord ++ tailWord_361442) baseStart_361442 baseEnd_361442 := by
    simpa [prefixWord, tailWord_361442, baseEnd_361442] using wordTrace_append hprefix tailTrace_361442
  have hstable : (prefixWord ++ tailWord_361442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361442).length < 2 ^ (prefixWord ++ tailWord_361442).sum := by decide
  have hdescent : baseEnd_361442 < baseStart_361442 := by decide
  rcases family_descends (prefixWord ++ tailWord_361442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361482 : List Nat := [3, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2]
def baseStart_361482 : Nat := 118140960795 + 361482 * 2 ^ 59
def prefixEnd_361482 : Nat := 4983230072969 + 3 ^ 40 * 361482 * 2
def baseEnd_361482 : Nat := 185614013948659933712581

theorem tailTrace_361482 : CollatzResearch.WordTrace tailWord_361482 prefixEnd_361482 185614013948659933712581 := by
  unfold tailWord_361482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3296082919104981263909675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8789554450946616703759133 3296082919104981263909675)
  ·
    refine ⟨4944124378657471895864513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3296082919104981263909675 4944124378657471895864513)
    ·
      refine ⟨3708093283993103921898385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4944124378657471895864513 3708093283993103921898385)
      ·
        refine ⟨2781069962994827941423789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3708093283993103921898385 2781069962994827941423789)
        ·
          refine ⟨1042901236123060478033921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2781069962994827941423789 1042901236123060478033921)
          ·
            refine ⟨782175927092295358525441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1042901236123060478033921 782175927092295358525441)
            ·
              refine ⟨586631945319221518894081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782175927092295358525441 586631945319221518894081)
              ·
                refine ⟨439973958989416139170561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586631945319221518894081 439973958989416139170561)
                ·
                  refine ⟨329980469242062104377921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439973958989416139170561 329980469242062104377921)
                  ·
                    refine ⟨247485351931546578283441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 329980469242062104377921 247485351931546578283441)
                    ·
                      refine ⟨185614013948659933712581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 247485351931546578283441 185614013948659933712581)
                      ·
                        rfl

theorem cell23_361482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_361482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361482 prefixEnd_361482 := by exact prefixLift 361482
  have htrace : WordTrace (prefixWord ++ tailWord_361482) baseStart_361482 baseEnd_361482 := by
    simpa [prefixWord, tailWord_361482, baseEnd_361482] using wordTrace_append hprefix tailTrace_361482
  have hstable : (prefixWord ++ tailWord_361482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361482).length < 2 ^ (prefixWord ++ tailWord_361482).sum := by decide
  have hdescent : baseEnd_361482 < baseStart_361482 := by decide
  rcases family_descends (prefixWord ++ tailWord_361482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361521 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_361521 : Nat := 118140960795 + 361521 * 2 ^ 59
def prefixEnd_361521 : Nat := 4983230072969 + 3 ^ 40 * 361521 * 2
def baseEnd_361521 : Nat := 185634039694185281124901

theorem tailTrace_361521 : CollatzResearch.WordTrace tailWord_361521 prefixEnd_361521 185634039694185281124901 := by
  unfold tailWord_361521
  simp only [CollatzResearch.WordTrace]
  refine ⟨13185754123278634716308417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8790502748852423144205611 13185754123278634716308417)
  ·
    refine ⟨9889315592458976037231313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13185754123278634716308417 9889315592458976037231313)
    ·
      refine ⟨7416986694344232027923485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9889315592458976037231313 7416986694344232027923485)
      ·
        refine ⟨2781370010379087010471307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7416986694344232027923485 2781370010379087010471307)
        ·
          refine ⟨4172055015568630515706961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2781370010379087010471307 4172055015568630515706961)
          ·
            refine ⟨3129041261676472886780221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4172055015568630515706961 3129041261676472886780221)
            ·
              refine ⟨1173390473128677332542583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3129041261676472886780221 1173390473128677332542583)
              ·
                refine ⟨1760085709693015998813875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173390473128677332542583 1760085709693015998813875)
                ·
                  refine ⟨2640128564539523998220813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760085709693015998813875 2640128564539523998220813)
                  ·
                    refine ⟨990048211702321499332805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2640128564539523998220813 990048211702321499332805)
                    ·
                      refine ⟨185634039694185281124901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 990048211702321499332805 185634039694185281124901)
                      ·
                        rfl

theorem cell23_361521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_361521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361521 prefixEnd_361521 := by exact prefixLift 361521
  have htrace : WordTrace (prefixWord ++ tailWord_361521) baseStart_361521 baseEnd_361521 := by
    simpa [prefixWord, tailWord_361521, baseEnd_361521] using wordTrace_append hprefix tailTrace_361521
  have hstable : (prefixWord ++ tailWord_361521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361521).length < 2 ^ (prefixWord ++ tailWord_361521).sum := by decide
  have hdescent : baseEnd_361521 < baseStart_361521 := by decide
  rcases family_descends (prefixWord ++ tailWord_361521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361571 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 3]
def baseStart_361571 : Nat := 118140960795 + 361571 * 2 ^ 59
def prefixEnd_361571 : Nat := 4983230072969 + 3 ^ 40 * 361571 * 2
def baseEnd_361571 : Nat := 185659713726910085499671

theorem tailTrace_361571 : CollatzResearch.WordTrace tailWord_361571 prefixEnd_361571 185659713726910085499671 := by
  unfold tailWord_361571
  simp only [CollatzResearch.WordTrace]
  refine ⟨13187577773097493255628567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8791718515398328837085711 13187577773097493255628567)
  ·
    refine ⟨19781366659646239883442851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13187577773097493255628567 19781366659646239883442851)
    ·
      refine ⟨29672049989469359825164277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19781366659646239883442851 29672049989469359825164277)
      ·
        refine ⟨2781754686512752483609151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29672049989469359825164277 2781754686512752483609151)
        ·
          refine ⟨4172632029769128725413727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2781754686512752483609151 4172632029769128725413727)
          ·
            refine ⟨6258948044653693088120591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4172632029769128725413727 6258948044653693088120591)
            ·
              refine ⟨9388422066980539632180887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6258948044653693088120591 9388422066980539632180887)
              ·
                refine ⟨14082633100470809448271331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9388422066980539632180887 14082633100470809448271331)
                ·
                  refine ⟨21123949650706214172406997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14082633100470809448271331 21123949650706214172406997)
                  ·
                    refine ⟨495092569938426894665789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21123949650706214172406997 495092569938426894665789)
                    ·
                      refine ⟨185659713726910085499671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 495092569938426894665789 185659713726910085499671)
                      ·
                        rfl

theorem cell23_361571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_361571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361571 prefixEnd_361571 := by exact prefixLift 361571
  have htrace : WordTrace (prefixWord ++ tailWord_361571) baseStart_361571 baseEnd_361571 := by
    simpa [prefixWord, tailWord_361571, baseEnd_361571] using wordTrace_append hprefix tailTrace_361571
  have hstable : (prefixWord ++ tailWord_361571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361571).length < 2 ^ (prefixWord ++ tailWord_361571).sum := by decide
  have hdescent : baseEnd_361571 < baseStart_361571 := by decide
  rcases family_descends (prefixWord ++ tailWord_361571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361582 : List Nat := [4, 1, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_361582 : Nat := 118140960795 + 361582 * 2 ^ 59
def prefixEnd_361582 : Nat := 4983230072969 + 3 ^ 40 * 361582 * 2
def baseEnd_361582 : Nat := 61888454004703180820707

theorem tailTrace_361582 : CollatzResearch.WordTrace tailWord_361582 prefixEnd_361582 61888454004703180820707 := by
  unfold tailWord_361582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648497372007205266784875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8791985984038428089519333 1648497372007205266784875)
  ·
    refine ⟨2472746058010807900177313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1648497372007205266784875 2472746058010807900177313)
    ·
      refine ⟨1854559543508105925132985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2472746058010807900177313 1854559543508105925132985)
      ·
        refine ⟨1390919657631079443849739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1854559543508105925132985 1390919657631079443849739)
        ·
          refine ⟨2086379486446619165774609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390919657631079443849739 2086379486446619165774609)
          ·
            refine ⟨1564784614834964374330957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2086379486446619165774609 1564784614834964374330957)
            ·
              refine ⟨586794230563111640374109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1564784614834964374330957 586794230563111640374109)
              ·
                refine ⟨220047836461166865140291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 586794230563111640374109 220047836461166865140291)
                ·
                  refine ⟨330071754691750297710437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220047836461166865140291 330071754691750297710437)
                  ·
                    refine ⟨61888454004703180820707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 330071754691750297710437 61888454004703180820707)
                    ·
                      rfl

theorem cell23_361582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_361582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361582 prefixEnd_361582 := by exact prefixLift 361582
  have htrace : WordTrace (prefixWord ++ tailWord_361582) baseStart_361582 baseEnd_361582 := by
    simpa [prefixWord, tailWord_361582, baseEnd_361582] using wordTrace_append hprefix tailTrace_361582
  have hstable : (prefixWord ++ tailWord_361582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361582).length < 2 ^ (prefixWord ++ tailWord_361582).sum := by decide
  have hdescent : baseEnd_361582 < baseStart_361582 := by decide
  rcases family_descends (prefixWord ++ tailWord_361582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361655 : List Nat := [1, 1, 3, 1, 4, 1, 4, 2, 2, 4]
def baseStart_361655 : Nat := 118140960795 + 361655 * 2 ^ 59
def prefixEnd_361655 : Nat := 4983230072969 + 3 ^ 40 * 361655 * 2
def baseEnd_361655 : Nat := 61900948700629252283095

theorem tailTrace_361655 : CollatzResearch.WordTrace tailWord_361655 prefixEnd_361655 61900948700629252283095 := by
  unfold tailWord_361655
  simp only [CollatzResearch.WordTrace]
  refine ⟨13190641504793175601686419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8793761003195450401124279 13190641504793175601686419)
  ·
    refine ⟨19785962257189763402529629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13190641504793175601686419 19785962257189763402529629)
    ·
      refine ⟨7419735846446161275948611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19785962257189763402529629 7419735846446161275948611)
      ·
        refine ⟨11129603769669241913922917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7419735846446161275948611 11129603769669241913922917)
        ·
          refine ⟨2086800706812982858860547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11129603769669241913922917 2086800706812982858860547)
          ·
            refine ⟨3130201060219474288290821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086800706812982858860547 3130201060219474288290821)
            ·
              refine ⟨586912698791151429054529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3130201060219474288290821 586912698791151429054529)
              ·
                refine ⟨440184524093363571790897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586912698791151429054529 440184524093363571790897)
                ·
                  refine ⟨330138393070022678843173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440184524093363571790897 330138393070022678843173)
                  ·
                    refine ⟨61900948700629252283095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 330138393070022678843173 61900948700629252283095)
                    ·
                      rfl

theorem cell23_361655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_361655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361655 prefixEnd_361655 := by exact prefixLift 361655
  have htrace : WordTrace (prefixWord ++ tailWord_361655) baseStart_361655 baseEnd_361655 := by
    simpa [prefixWord, tailWord_361655, baseEnd_361655] using wordTrace_append hprefix tailTrace_361655
  have hstable : (prefixWord ++ tailWord_361655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361655).length < 2 ^ (prefixWord ++ tailWord_361655).sum := by decide
  have hdescent : baseEnd_361655 < baseStart_361655 := by decide
  rcases family_descends (prefixWord ++ tailWord_361655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361671 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_361671 : Nat := 118140960795 + 361671 * 2 ^ 59
def prefixEnd_361671 : Nat := 4983230072969 + 3 ^ 40 * 361671 * 2
def baseEnd_361671 : Nat := 185711061792359694249211

theorem tailTrace_361671 : CollatzResearch.WordTrace tailWord_361671 prefixEnd_361671 185711061792359694249211 := by
  unfold tailWord_361671
  simp only [CollatzResearch.WordTrace]
  refine ⟨13191225072735210334268867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8794150048490140222845911 13191225072735210334268867)
  ·
    refine ⟨19786837609102815501403301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13191225072735210334268867 19786837609102815501403301)
    ·
      refine ⟨3710032051706777906513119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19786837609102815501403301 3710032051706777906513119)
      ·
        refine ⟨5565048077560166859769679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3710032051706777906513119 5565048077560166859769679)
        ·
          refine ⟨8347572116340250289654519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5565048077560166859769679 8347572116340250289654519)
          ·
            refine ⟨12521358174510375434481779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8347572116340250289654519 12521358174510375434481779)
            ·
              refine ⟨18782037261765563151722669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12521358174510375434481779 18782037261765563151722669)
              ·
                refine ⟨7043263973162086181896001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18782037261765563151722669 7043263973162086181896001)
                ·
                  refine ⟨5282447979871564636422001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7043263973162086181896001 5282447979871564636422001)
                  ·
                    refine ⟨3961835984903673477316501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5282447979871564636422001 3961835984903673477316501)
                    ·
                      refine ⟨185711061792359694249211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3961835984903673477316501 185711061792359694249211)
                      ·
                        rfl

theorem cell23_361671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_361671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361671 prefixEnd_361671 := by exact prefixLift 361671
  have htrace : WordTrace (prefixWord ++ tailWord_361671) baseStart_361671 baseEnd_361671 := by
    simpa [prefixWord, tailWord_361671, baseEnd_361671] using wordTrace_append hprefix tailTrace_361671
  have hstable : (prefixWord ++ tailWord_361671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361671).length < 2 ^ (prefixWord ++ tailWord_361671).sum := by decide
  have hdescent : baseEnd_361671 < baseStart_361671 := by decide
  rcases family_descends (prefixWord ++ tailWord_361671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361681 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 4, 7]
def baseStart_361681 : Nat := 118140960795 + 361681 * 2 ^ 59
def prefixEnd_361681 : Nat := 4983230072969 + 3 ^ 40 * 361681 * 2
def baseEnd_361681 : Nat := 61905398866301551708055

theorem tailTrace_361681 : CollatzResearch.WordTrace tailWord_361681 prefixEnd_361681 61905398866301551708055 := by
  unfold tailWord_361681
  simp only [CollatzResearch.WordTrace]
  refine ⟨13191589802698982042132897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8794393201799321361421931 13191589802698982042132897)
  ·
    refine ⟨9893692352024236531599673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13191589802698982042132897 9893692352024236531599673)
    ·
      refine ⟨7420269264018177398699755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9893692352024236531599673 7420269264018177398699755)
      ·
        refine ⟨11130403896027266098049633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7420269264018177398699755 11130403896027266098049633)
        ·
          refine ⟨8347802922020449573537225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11130403896027266098049633 8347802922020449573537225)
          ·
            refine ⟨6260852191515337180152919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8347802922020449573537225 6260852191515337180152919)
            ·
              refine ⟨9391278287273005770229379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6260852191515337180152919 9391278287273005770229379)
              ·
                refine ⟨14086917430909508655344069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9391278287273005770229379 14086917430909508655344069)
                ·
                  refine ⟨2641297018295532872877013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14086917430909508655344069 2641297018295532872877013)
                  ·
                    refine ⟨61905398866301551708055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2641297018295532872877013 61905398866301551708055)
                    ·
                      rfl

theorem cell23_361681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_361681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361681 prefixEnd_361681 := by exact prefixLift 361681
  have htrace : WordTrace (prefixWord ++ tailWord_361681) baseStart_361681 baseEnd_361681 := by
    simpa [prefixWord, tailWord_361681, baseEnd_361681] using wordTrace_append hprefix tailTrace_361681
  have hstable : (prefixWord ++ tailWord_361681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361681).length < 2 ^ (prefixWord ++ tailWord_361681).sum := by decide
  have hdescent : baseEnd_361681 < baseStart_361681 := by decide
  rcases family_descends (prefixWord ++ tailWord_361681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361685 : List Nat := [1, 3, 2, 4, 1, 2, 3, 7]
def baseStart_361685 : Nat := 118140960795 + 361685 * 2 ^ 59
def prefixEnd_361685 : Nat := 4983230072969 + 3 ^ 40 * 361685 * 2
def baseEnd_361685 : Nat := 6878453723019357017561

theorem tailTrace_361685 : CollatzResearch.WordTrace tailWord_361685 prefixEnd_361685 6878453723019357017561 := by
  unfold tailWord_361685
  simp only [CollatzResearch.WordTrace]
  refine ⟨13191735694684490725278509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8794490463122993816852339 13191735694684490725278509)
  ·
    refine ⟨4946900885506684021979441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13191735694684490725278509 4946900885506684021979441)
    ·
      refine ⟨3710175664130013016484581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4946900885506684021979441 3710175664130013016484581)
      ·
        refine ⟨695657937024377440590859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3710175664130013016484581 695657937024377440590859)
        ·
          refine ⟨1043486905536566160886289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695657937024377440590859 1043486905536566160886289)
          ·
            refine ⟨782615179152424620664717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1043486905536566160886289 782615179152424620664717)
            ·
              refine ⟨293480692182159232749269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 782615179152424620664717 293480692182159232749269)
              ·
                refine ⟨6878453723019357017561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 293480692182159232749269 6878453723019357017561)
                ·
                  rfl

theorem cell23_361685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 7].length) (baseStart_361685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361685 prefixEnd_361685 := by exact prefixLift 361685
  have htrace : WordTrace (prefixWord ++ tailWord_361685) baseStart_361685 baseEnd_361685 := by
    simpa [prefixWord, tailWord_361685, baseEnd_361685] using wordTrace_append hprefix tailTrace_361685
  have hstable : (prefixWord ++ tailWord_361685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361685).length < 2 ^ (prefixWord ++ tailWord_361685).sum := by decide
  have hdescent : baseEnd_361685 < baseStart_361685 := by decide
  rcases family_descends (prefixWord ++ tailWord_361685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361729 : List Nat := [1, 2, 4, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_361729 : Nat := 118140960795 + 361729 * 2 ^ 59
def prefixEnd_361729 : Nat := 4983230072969 + 3 ^ 40 * 361729 * 2
def baseEnd_361729 : Nat := 185740843670320467323945

theorem tailTrace_361729 : CollatzResearch.WordTrace tailWord_361729 prefixEnd_361729 185740843670320467323945 := by
  unfold tailWord_361729
  simp only [CollatzResearch.WordTrace]
  refine ⟨13193340506525086239880241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8795560337683390826586827 13193340506525086239880241)
  ·
    refine ⟨9895005379893814679910181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13193340506525086239880241 9895005379893814679910181)
    ·
      refine ⟨1855313508730090252483159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9895005379893814679910181 1855313508730090252483159)
      ·
        refine ⟨2782970263095135378724739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855313508730090252483159 2782970263095135378724739)
        ·
          refine ⟨4174455394642703068087109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782970263095135378724739 4174455394642703068087109)
          ·
            refine ⟨782710386495506825266333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4174455394642703068087109 782710386495506825266333)
            ·
              refine ⟨293516394935815059474875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 782710386495506825266333 293516394935815059474875)
              ·
                refine ⟨440274592403722589212313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293516394935815059474875 440274592403722589212313)
                ·
                  refine ⟨330205944302791941909235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440274592403722589212313 330205944302791941909235)
                  ·
                    refine ⟨495308916454187912863853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 330205944302791941909235 495308916454187912863853)
                    ·
                      refine ⟨185740843670320467323945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 495308916454187912863853 185740843670320467323945)
                      ·
                        rfl

theorem cell23_361729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_361729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361729 prefixEnd_361729 := by exact prefixLift 361729
  have htrace : WordTrace (prefixWord ++ tailWord_361729) baseStart_361729 baseEnd_361729 := by
    simpa [prefixWord, tailWord_361729, baseEnd_361729] using wordTrace_append hprefix tailTrace_361729
  have hstable : (prefixWord ++ tailWord_361729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361729).length < 2 ^ (prefixWord ++ tailWord_361729).sum := by decide
  have hdescent : baseEnd_361729 < baseStart_361729 := by decide
  rcases family_descends (prefixWord ++ tailWord_361729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361738 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_361738 : Nat := 118140960795 + 361738 * 2 ^ 59
def prefixEnd_361738 : Nat := 4983230072969 + 3 ^ 40 * 361738 * 2
def baseEnd_361738 : Nat := 185745464996210932111403

theorem tailTrace_361738 : CollatzResearch.WordTrace tailWord_361738 prefixEnd_361738 185745464996210932111403 := by
  unfold tailWord_361738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3298417190873120194239467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8795779175661653851305245 3298417190873120194239467)
  ·
    refine ⟨4947625786309680291359201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3298417190873120194239467 4947625786309680291359201)
    ·
      refine ⟨3710719339732260218519401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4947625786309680291359201 3710719339732260218519401)
      ·
        refine ⟨2783039504799195163889551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3710719339732260218519401 2783039504799195163889551)
        ·
          refine ⟨4174559257198792745834327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783039504799195163889551 4174559257198792745834327)
          ·
            refine ⟨6261838885798189118751491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174559257198792745834327 6261838885798189118751491)
            ·
              refine ⟨9392758328697283678127237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6261838885798189118751491 9392758328697283678127237)
              ·
                refine ⟨1761142186630740689648857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9392758328697283678127237 1761142186630740689648857)
                ·
                  refine ⟨1320856639973055517236643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1761142186630740689648857 1320856639973055517236643)
                  ·
                    refine ⟨1981284959959583275854965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1320856639973055517236643 1981284959959583275854965)
                    ·
                      refine ⟨185745464996210932111403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1981284959959583275854965 185745464996210932111403)
                      ·
                        rfl

theorem cell23_361738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_361738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361738 prefixEnd_361738 := by exact prefixLift 361738
  have htrace : WordTrace (prefixWord ++ tailWord_361738) baseStart_361738 baseEnd_361738 := by
    simpa [prefixWord, tailWord_361738, baseEnd_361738] using wordTrace_append hprefix tailTrace_361738
  have hstable : (prefixWord ++ tailWord_361738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361738).length < 2 ^ (prefixWord ++ tailWord_361738).sum := by decide
  have hdescent : baseEnd_361738 < baseStart_361738 := by decide
  rcases family_descends (prefixWord ++ tailWord_361738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361752 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 4, 2, 2]
def baseStart_361752 : Nat := 118140960795 + 361752 * 2 ^ 59
def prefixEnd_361752 : Nat := 4983230072969 + 3 ^ 40 * 361752 * 2
def baseEnd_361752 : Nat := 185752653725373877336339

theorem tailTrace_361752 : CollatzResearch.WordTrace tailWord_361752 prefixEnd_361752 185752653725373877336339 := by
  unfold tailWord_361752
  simp only [CollatzResearch.WordTrace]
  refine ⟨6597089692720880583983755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8796119590294507445311673 6597089692720880583983755)
  ·
    refine ⟨9895634539081320875975633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6597089692720880583983755 9895634539081320875975633)
    ·
      refine ⟨7421725904310990656981725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9895634539081320875975633 7421725904310990656981725)
      ·
        refine ⟨2783147214116621496368147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7421725904310990656981725 2783147214116621496368147)
        ·
          refine ⟨4174720821174932244552221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783147214116621496368147 4174720821174932244552221)
          ·
            refine ⟨1565520307940599591707083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4174720821174932244552221 1565520307940599591707083)
            ·
              refine ⟨2348280461910899387560625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565520307940599591707083 2348280461910899387560625)
              ·
                refine ⟨1761210346433174540670469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348280461910899387560625 1761210346433174540670469)
                ·
                  refine ⟨330226939956220226375713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1761210346433174540670469 330226939956220226375713)
                  ·
                    refine ⟨247670204967165169781785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 330226939956220226375713 247670204967165169781785)
                    ·
                      refine ⟨185752653725373877336339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 247670204967165169781785 185752653725373877336339)
                      ·
                        rfl

theorem cell23_361752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_361752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361752 prefixEnd_361752 := by exact prefixLift 361752
  have htrace : WordTrace (prefixWord ++ tailWord_361752) baseStart_361752 baseEnd_361752 := by
    simpa [prefixWord, tailWord_361752, baseEnd_361752] using wordTrace_append hprefix tailTrace_361752
  have hstable : (prefixWord ++ tailWord_361752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361752).length < 2 ^ (prefixWord ++ tailWord_361752).sum := by decide
  have hdescent : baseEnd_361752 < baseStart_361752 := by decide
  rcases family_descends (prefixWord ++ tailWord_361752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361825 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 3, 6, 2]
def baseStart_361825 : Nat := 118140960795 + 361825 * 2 ^ 59
def prefixEnd_361825 : Nat := 4983230072969 + 3 ^ 40 * 361825 * 2
def baseEnd_361825 : Nat := 185790137813152091723503

theorem tailTrace_361825 : CollatzResearch.WordTrace tailWord_361825 prefixEnd_361825 185790137813152091723503 := by
  unfold tailWord_361825
  simp only [CollatzResearch.WordTrace]
  refine ⟨13196841914177294635374929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8797894609451529756916619 13196841914177294635374929)
  ·
    refine ⟨9897631435632970976531197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13196841914177294635374929 9897631435632970976531197)
    ·
      refine ⟨3711611788362364116199199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9897631435632970976531197 3711611788362364116199199)
      ·
        refine ⟨5567417682543546174298799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3711611788362364116199199 5567417682543546174298799)
        ·
          refine ⟨8351126523815319261448199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567417682543546174298799 8351126523815319261448199)
          ·
            refine ⟨12526689785722978892172299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8351126523815319261448199 12526689785722978892172299)
            ·
              refine ⟨18790034678584468338258449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12526689785722978892172299 18790034678584468338258449)
              ·
                refine ⟨14092526008938351253693837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18790034678584468338258449 14092526008938351253693837)
                ·
                  refine ⟨5284697253351881720135189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14092526008938351253693837 5284697253351881720135189)
                  ·
                    refine ⟨247720183750869455631337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5284697253351881720135189 247720183750869455631337)
                    ·
                      refine ⟨185790137813152091723503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 247720183750869455631337 185790137813152091723503)
                      ·
                        rfl

theorem cell23_361825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_361825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361825 prefixEnd_361825 := by exact prefixLift 361825
  have htrace : WordTrace (prefixWord ++ tailWord_361825) baseStart_361825 baseEnd_361825 := by
    simpa [prefixWord, tailWord_361825, baseEnd_361825] using wordTrace_append hprefix tailTrace_361825
  have hstable : (prefixWord ++ tailWord_361825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361825).length < 2 ^ (prefixWord ++ tailWord_361825).sum := by decide
  have hdescent : baseEnd_361825 < baseStart_361825 := by decide
  rcases family_descends (prefixWord ++ tailWord_361825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361842 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 2, 4, 2]
def baseStart_361842 : Nat := 118140960795 + 361842 * 2 ^ 59
def prefixEnd_361842 : Nat := 4983230072969 + 3 ^ 40 * 361842 * 2
def baseEnd_361842 : Nat := 185798866984278525210925

theorem tailTrace_361842 : CollatzResearch.WordTrace tailWord_361842 prefixEnd_361842 185798866984278525210925 := by
  unfold tailWord_361842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3299365488778926634685945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8798307970077137692495853 3299365488778926634685945)
  ·
    refine ⟨2474524116584194976014459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3299365488778926634685945 2474524116584194976014459)
    ·
      refine ⟨3711786174876292464021689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2474524116584194976014459 3711786174876292464021689)
      ·
        refine ⟨2783839631157219348016267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3711786174876292464021689 2783839631157219348016267)
        ·
          refine ⟨4175759446735829022024401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783839631157219348016267 4175759446735829022024401)
          ·
            refine ⟨3131819585051871766518301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4175759446735829022024401 3131819585051871766518301)
            ·
              refine ⟨1174432344394451912444363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3131819585051871766518301 1174432344394451912444363)
              ·
                refine ⟨1761648516591677868666545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174432344394451912444363 1761648516591677868666545)
                ·
                  refine ⟨1321236387443758401499909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1761648516591677868666545 1321236387443758401499909)
                  ·
                    refine ⟨247731822645704700281233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1321236387443758401499909 247731822645704700281233)
                    ·
                      refine ⟨185798866984278525210925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 247731822645704700281233 185798866984278525210925)
                      ·
                        rfl

theorem cell23_361842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_361842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361842 prefixEnd_361842 := by exact prefixLift 361842
  have htrace : WordTrace (prefixWord ++ tailWord_361842) baseStart_361842 baseEnd_361842 := by
    simpa [prefixWord, tailWord_361842, baseEnd_361842] using wordTrace_append hprefix tailTrace_361842
  have hstable : (prefixWord ++ tailWord_361842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361842).length < 2 ^ (prefixWord ++ tailWord_361842).sum := by decide
  have hdescent : baseEnd_361842 < baseStart_361842 := by decide
  rcases family_descends (prefixWord ++ tailWord_361842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361885 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_361885 : Nat := 118140960795 + 361885 * 2 ^ 59
def prefixEnd_361885 : Nat := 4983230072969 + 3 ^ 40 * 361885 * 2
def baseEnd_361885 : Nat := 185820946652421856973227

theorem tailTrace_361885 : CollatzResearch.WordTrace tailWord_361885 prefixEnd_361885 185820946652421856973227 := by
  unfold tailWord_361885
  simp only [CollatzResearch.WordTrace]
  refine ⟨13199030293959924882559109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8799353529306616588372739 13199030293959924882559109)
  ·
    refine ⟨2474818180117485915479833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13199030293959924882559109 2474818180117485915479833)
    ·
      refine ⟨1856113635088114436609875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2474818180117485915479833 1856113635088114436609875)
      ·
        refine ⟨2784170452632171654914813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1856113635088114436609875 2784170452632171654914813)
        ·
          refine ⟨1044063919737064370593055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2784170452632171654914813 1044063919737064370593055)
          ·
            refine ⟨1566095879605596555889583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044063919737064370593055 1566095879605596555889583)
            ·
              refine ⟨2349143819408394833834375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566095879605596555889583 2349143819408394833834375)
              ·
                refine ⟨3523715729112592250751563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2349143819408394833834375 3523715729112592250751563)
                ·
                  refine ⟨5285573593668888376127345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523715729112592250751563 5285573593668888376127345)
                  ·
                    refine ⟨3964180195251666282095509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5285573593668888376127345 3964180195251666282095509)
                    ·
                      refine ⟨185820946652421856973227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3964180195251666282095509 185820946652421856973227)
                      ·
                        rfl

theorem cell23_361885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_361885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361885 prefixEnd_361885 := by exact prefixLift 361885
  have htrace : WordTrace (prefixWord ++ tailWord_361885) baseStart_361885 baseEnd_361885 := by
    simpa [prefixWord, tailWord_361885, baseEnd_361885] using wordTrace_append hprefix tailTrace_361885
  have hstable : (prefixWord ++ tailWord_361885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361885).length < 2 ^ (prefixWord ++ tailWord_361885).sum := by decide
  have hdescent : baseEnd_361885 < baseStart_361885 := by decide
  rcases family_descends (prefixWord ++ tailWord_361885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361886 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_361886 : Nat := 118140960795 + 361886 * 2 ^ 59
def prefixEnd_361886 : Nat := 4983230072969 + 3 ^ 40 * 361886 * 2
def baseEnd_361886 : Nat := 61940486711025451020241

theorem tailTrace_361886 : CollatzResearch.WordTrace tailWord_361886 prefixEnd_361886 61940486711025451020241 := by
  unfold tailWord_361886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649883345869537756668189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8799377844637534702230341 1649883345869537756668189)
  ·
    refine ⟨618706254701076658750571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1649883345869537756668189 618706254701076658750571)
    ·
      refine ⟨928059382051614988125857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618706254701076658750571 928059382051614988125857)
      ·
        refine ⟨696044536538711241094393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 928059382051614988125857 696044536538711241094393)
        ·
          refine ⟨522033402404033430820795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 696044536538711241094393 522033402404033430820795)
          ·
            refine ⟨783050103606050146231193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522033402404033430820795 783050103606050146231193)
            ·
              refine ⟨587287577704537609673395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783050103606050146231193 587287577704537609673395)
              ·
                refine ⟨880931366556806414510093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587287577704537609673395 880931366556806414510093)
                ·
                  refine ⟨330349262458802405441285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880931366556806414510093 330349262458802405441285)
                  ·
                    refine ⟨61940486711025451020241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 330349262458802405441285 61940486711025451020241)
                    ·
                      rfl

theorem cell23_361886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_361886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361886 prefixEnd_361886 := by exact prefixLift 361886
  have htrace : WordTrace (prefixWord ++ tailWord_361886) baseStart_361886 baseEnd_361886 := by
    simpa [prefixWord, tailWord_361886, baseEnd_361886] using wordTrace_append hprefix tailTrace_361886
  have hstable : (prefixWord ++ tailWord_361886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361886).length < 2 ^ (prefixWord ++ tailWord_361886).sum := by decide
  have hdescent : baseEnd_361886 < baseStart_361886 := by decide
  rcases family_descends (prefixWord ++ tailWord_361886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361909 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_361909 : Nat := 118140960795 + 361909 * 2 ^ 59
def prefixEnd_361909 : Nat := 4983230072969 + 3 ^ 40 * 361909 * 2
def baseEnd_361909 : Nat := 185833270188129763073117

theorem tailTrace_361909 : CollatzResearch.WordTrace tailWord_361909 prefixEnd_361909 185833270188129763073117 := by
  unfold tailWord_361909
  simp only [CollatzResearch.WordTrace]
  refine ⟨13199905645872976981432781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8799937097248651320955187 13199905645872976981432781)
  ·
    refine ⟨4949964617202366368037293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13199905645872976981432781 4949964617202366368037293)
    ·
      refine ⟨1856236731450887388013985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4949964617202366368037293 1856236731450887388013985)
      ·
        refine ⟨1392177548588165541010489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1856236731450887388013985 1392177548588165541010489)
        ·
          refine ⟨1044133161441124155757867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1392177548588165541010489 1044133161441124155757867)
          ·
            refine ⟨1566199742161686233636801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044133161441124155757867 1566199742161686233636801)
            ·
              refine ⟨1174649806621264675227601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1566199742161686233636801 1174649806621264675227601)
              ·
                refine ⟨880987354965948506420701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174649806621264675227601 880987354965948506420701)
                ·
                  refine ⟨330370258112230689907763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880987354965948506420701 330370258112230689907763)
                  ·
                    refine ⟨495555387168346034861645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 330370258112230689907763 495555387168346034861645)
                    ·
                      refine ⟨185833270188129763073117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 495555387168346034861645 185833270188129763073117)
                      ·
                        rfl

theorem cell23_361909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_361909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361909 prefixEnd_361909 := by exact prefixLift 361909
  have htrace : WordTrace (prefixWord ++ tailWord_361909) baseStart_361909 baseEnd_361909 := by
    simpa [prefixWord, tailWord_361909, baseEnd_361909] using wordTrace_append hprefix tailTrace_361909
  have hstable : (prefixWord ++ tailWord_361909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361909).length < 2 ^ (prefixWord ++ tailWord_361909).sum := by decide
  have hdescent : baseEnd_361909 < baseStart_361909 := by decide
  rcases family_descends (prefixWord ++ tailWord_361909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361935 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 5]
def baseStart_361935 : Nat := 118140960795 + 361935 * 2 ^ 59
def prefixEnd_361935 : Nat := 4983230072969 + 3 ^ 40 * 361935 * 2
def baseEnd_361935 : Nat := 185846620685146661347997

theorem tailTrace_361935 : CollatzResearch.WordTrace tailWord_361935 prefixEnd_361935 185846620685146661347997 := by
  unfold tailWord_361935
  simp only [CollatzResearch.WordTrace]
  refine ⟨13200853943778783421879259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8800569295852522281252839 13200853943778783421879259)
  ·
    refine ⟨19801280915668175132818889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13200853943778783421879259 19801280915668175132818889)
    ·
      refine ⟨14850960686751131349614167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19801280915668175132818889 14850960686751131349614167)
      ·
        refine ⟨22276441030126697024421251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14850960686751131349614167 22276441030126697024421251)
        ·
          refine ⟨33414661545190045536631877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22276441030126697024421251 33414661545190045536631877)
          ·
            refine ⟨6265249039723133538118477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33414661545190045536631877 6265249039723133538118477)
            ·
              refine ⟨2349468389896175076794429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6265249039723133538118477 2349468389896175076794429)
              ·
                refine ⟨881050646211065653797911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2349468389896175076794429 881050646211065653797911)
                ·
                  refine ⟨1321575969316598480696867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881050646211065653797911 1321575969316598480696867)
                  ·
                    refine ⟨1982363953974897721045301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1321575969316598480696867 1982363953974897721045301)
                    ·
                      refine ⟨185846620685146661347997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1982363953974897721045301 185846620685146661347997)
                      ·
                        rfl

theorem cell23_361935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_361935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361935 prefixEnd_361935 := by exact prefixLift 361935
  have htrace : WordTrace (prefixWord ++ tailWord_361935) baseStart_361935 baseEnd_361935 := by
    simpa [prefixWord, tailWord_361935, baseEnd_361935] using wordTrace_append hprefix tailTrace_361935
  have hstable : (prefixWord ++ tailWord_361935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361935).length < 2 ^ (prefixWord ++ tailWord_361935).sum := by decide
  have hdescent : baseEnd_361935 < baseStart_361935 := by decide
  rcases family_descends (prefixWord ++ tailWord_361935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361945 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 6]
def baseStart_361945 : Nat := 118140960795 + 361945 * 2 ^ 59
def prefixEnd_361945 : Nat := 4983230072969 + 3 ^ 40 * 361945 * 2
def baseEnd_361945 : Nat := 185851755491691622222951

theorem tailTrace_361945 : CollatzResearch.WordTrace tailWord_361945 prefixEnd_361945 185851755491691622222951 := by
  unfold tailWord_361945
  simp only [CollatzResearch.WordTrace]
  refine ⟨13201218673742555129743289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8800812449161703419828859 13201218673742555129743289)
  ·
    refine ⟨9900914005306916347307467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13201218673742555129743289 9900914005306916347307467)
    ·
      refine ⟨14851371007960374520961201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9900914005306916347307467 14851371007960374520961201)
      ·
        refine ⟨11138528255970280890720901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14851371007960374520961201 11138528255970280890720901)
        ·
          refine ⟨2088474047994427667010169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11138528255970280890720901 2088474047994427667010169)
          ·
            refine ⟨1566355535995820750257627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2088474047994427667010169 1566355535995820750257627)
            ·
              refine ⟨2349533303993731125386441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566355535995820750257627 2349533303993731125386441)
              ·
                refine ⟨1762149977995298344039831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2349533303993731125386441 1762149977995298344039831)
                ·
                  refine ⟨2643224966992947516059747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762149977995298344039831 2643224966992947516059747)
                  ·
                    refine ⟨3964837450489421274089621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2643224966992947516059747 3964837450489421274089621)
                    ·
                      refine ⟨185851755491691622222951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3964837450489421274089621 185851755491691622222951)
                      ·
                        rfl

theorem cell23_361945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_361945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361945 prefixEnd_361945 := by exact prefixLift 361945
  have htrace : WordTrace (prefixWord ++ tailWord_361945) baseStart_361945 baseEnd_361945 := by
    simpa [prefixWord, tailWord_361945, baseEnd_361945] using wordTrace_append hprefix tailTrace_361945
  have hstable : (prefixWord ++ tailWord_361945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361945).length < 2 ^ (prefixWord ++ tailWord_361945).sum := by decide
  have hdescent : baseEnd_361945 < baseStart_361945 := by decide
  rcases family_descends (prefixWord ++ tailWord_361945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361955 : List Nat := [1, 1, 1, 6, 2, 1, 1, 10]
def baseStart_361955 : Nat := 118140960795 + 361955 * 2 ^ 59
def prefixEnd_361955 : Nat := 4983230072969 + 3 ^ 40 * 361955 * 2
def baseEnd_361955 : Nat := 6883588529564317892515

theorem tailTrace_361955 : CollatzResearch.WordTrace tailWord_361955 prefixEnd_361955 6883588529564317892515 := by
  unfold tailWord_361955
  simp only [CollatzResearch.WordTrace]
  refine ⟨13201583403706326837607319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8801055602470884558404879 13201583403706326837607319)
  ·
    refine ⟨19802375105559490256410979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13201583403706326837607319 19802375105559490256410979)
    ·
      refine ⟨29703562658339235384616469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19802375105559490256410979 29703562658339235384616469)
      ·
        refine ⟨1392354499609651658653897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29703562658339235384616469 1392354499609651658653897)
        ·
          refine ⟨1044265874707238743990423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1392354499609651658653897 1044265874707238743990423)
          ·
            refine ⟨1566398812060858115985635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044265874707238743990423 1566398812060858115985635)
            ·
              refine ⟨2349598218091287173978453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566398812060858115985635 2349598218091287173978453)
              ·
                refine ⟨6883588529564317892515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2349598218091287173978453 6883588529564317892515)
                ·
                  rfl

theorem cell23_361955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 10].length) (baseStart_361955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361955 prefixEnd_361955 := by exact prefixLift 361955
  have htrace : WordTrace (prefixWord ++ tailWord_361955) baseStart_361955 baseEnd_361955 := by
    simpa [prefixWord, tailWord_361955, baseEnd_361955] using wordTrace_append hprefix tailTrace_361955
  have hstable : (prefixWord ++ tailWord_361955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361955).length < 2 ^ (prefixWord ++ tailWord_361955).sum := by decide
  have hdescent : baseEnd_361955 < baseStart_361955 := by decide
  rcases family_descends (prefixWord ++ tailWord_361955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361959 : List Nat := [1, 1, 5, 2, 1, 3, 1, 3, 2, 4]
def baseStart_361959 : Nat := 118140960795 + 361959 * 2 ^ 59
def prefixEnd_361959 : Nat := 4983230072969 + 3 ^ 40 * 361959 * 2
def baseEnd_361959 : Nat := 61952981406951522482629

theorem tailTrace_361959 : CollatzResearch.WordTrace tailWord_361959 prefixEnd_361959 61952981406951522482629 := by
  unfold tailWord_361959
  simp only [CollatzResearch.WordTrace]
  refine ⟨13201729295691835520752931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8801152863794557013835287 13201729295691835520752931)
  ·
    refine ⟨19802593943537753281129397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13201729295691835520752931 19802593943537753281129397)
    ·
      refine ⟨1856493182206664370105881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19802593943537753281129397 1856493182206664370105881)
      ·
        refine ⟨1392369886654998277579411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1856493182206664370105881 1392369886654998277579411)
        ·
          refine ⟨2088554829982497416369117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392369886654998277579411 2088554829982497416369117)
          ·
            refine ⟨783208061243436531138419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2088554829982497416369117 783208061243436531138419)
            ·
              refine ⟨1174812091865154796707629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783208061243436531138419 1174812091865154796707629)
              ·
                refine ⟨440554534449433048765361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1174812091865154796707629 440554534449433048765361)
                ·
                  refine ⟨330415900837074786574021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440554534449433048765361 330415900837074786574021)
                  ·
                    refine ⟨61952981406951522482629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 330415900837074786574021 61952981406951522482629)
                    ·
                      rfl

theorem cell23_361959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_361959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361959 prefixEnd_361959 := by exact prefixLift 361959
  have htrace : WordTrace (prefixWord ++ tailWord_361959) baseStart_361959 baseEnd_361959 := by
    simpa [prefixWord, tailWord_361959, baseEnd_361959] using wordTrace_append hprefix tailTrace_361959
  have hstable : (prefixWord ++ tailWord_361959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361959).length < 2 ^ (prefixWord ++ tailWord_361959).sum := by decide
  have hdescent : baseEnd_361959 < baseStart_361959 := by decide
  rcases family_descends (prefixWord ++ tailWord_361959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361969 : List Nat := [1, 2, 2, 2, 3, 2, 3, 2, 1, 2, 3]
def baseStart_361969 : Nat := 118140960795 + 361969 * 2 ^ 59
def prefixEnd_361969 : Nat := 4983230072969 + 3 ^ 40 * 361969 * 2
def baseEnd_361969 : Nat := 185864079027399528322841

theorem tailTrace_361969 : CollatzResearch.WordTrace tailWord_361969 prefixEnd_361969 185864079027399528322841 := by
  unfold tailWord_361969
  simp only [CollatzResearch.WordTrace]
  refine ⟨13202094025655607228616961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8801396017103738152411307 13202094025655607228616961)
  ·
    refine ⟨9901570519241705421462721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13202094025655607228616961 9901570519241705421462721)
    ·
      refine ⟨7426177889431279066097041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9901570519241705421462721 7426177889431279066097041)
      ·
        refine ⟨5569633417073459299572781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7426177889431279066097041 5569633417073459299572781)
        ·
          refine ⟨2088612531402547237339793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5569633417073459299572781 2088612531402547237339793)
          ·
            refine ⟨1566459398551910428004845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2088612531402547237339793 1566459398551910428004845)
            ·
              refine ⟨587422274456966410501817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1566459398551910428004845 587422274456966410501817)
              ·
                refine ⟨440566705842724807876363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587422274456966410501817 440566705842724807876363)
                ·
                  refine ⟨660850058764087211814545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440566705842724807876363 660850058764087211814545)
                  ·
                    refine ⟨495637544073065408860909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 660850058764087211814545 495637544073065408860909)
                    ·
                      refine ⟨185864079027399528322841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 495637544073065408860909 185864079027399528322841)
                      ·
                        rfl

theorem cell23_361969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_361969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361969 prefixEnd_361969 := by exact prefixLift 361969
  have htrace : WordTrace (prefixWord ++ tailWord_361969) baseStart_361969 baseEnd_361969 := by
    simpa [prefixWord, tailWord_361969, baseEnd_361969] using wordTrace_append hprefix tailTrace_361969
  have hstable : (prefixWord ++ tailWord_361969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361969).length < 2 ^ (prefixWord ++ tailWord_361969).sum := by decide
  have hdescent : baseEnd_361969 < baseStart_361969 := by decide
  rcases family_descends (prefixWord ++ tailWord_361969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361986 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_361986 : Nat := 118140960795 + 361986 * 2 ^ 59
def prefixEnd_361986 : Nat := 4983230072969 + 3 ^ 40 * 361986 * 2
def baseEnd_361986 : Nat := 185872808198525961810263

theorem tailTrace_361986 : CollatzResearch.WordTrace tailWord_361986 prefixEnd_361986 185872808198525961810263 := by
  unfold tailWord_361986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3300678516648504782996453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8801809377729346087990541 3300678516648504782996453)
  ·
    refine ⟨618877221871594646811835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3300678516648504782996453 618877221871594646811835)
    ·
      refine ⟨928315832807391970217753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618877221871594646811835 928315832807391970217753)
      ·
        refine ⟨696236874605543977663315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 928315832807391970217753 696236874605543977663315)
        ·
          refine ⟨1044355311908315966494973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696236874605543977663315 1044355311908315966494973)
          ·
            refine ⟨391633241965618487435615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1044355311908315966494973 391633241965618487435615)
            ·
              refine ⟨587449862948427731153423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391633241965618487435615 587449862948427731153423)
              ·
                refine ⟨881174794422641596730135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587449862948427731153423 881174794422641596730135)
                ·
                  refine ⟨1321762191633962395095203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881174794422641596730135 1321762191633962395095203)
                  ·
                    refine ⟨1982643287450943592642805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1321762191633962395095203 1982643287450943592642805)
                    ·
                      refine ⟨185872808198525961810263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1982643287450943592642805 185872808198525961810263)
                      ·
                        rfl

theorem cell23_361986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_361986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_361986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_361986 prefixEnd_361986 := by exact prefixLift 361986
  have htrace : WordTrace (prefixWord ++ tailWord_361986) baseStart_361986 baseEnd_361986 := by
    simpa [prefixWord, tailWord_361986, baseEnd_361986] using wordTrace_append hprefix tailTrace_361986
  have hstable : (prefixWord ++ tailWord_361986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361986).length < 2 ^ (prefixWord ++ tailWord_361986).sum := by decide
  have hdescent : baseEnd_361986 < baseStart_361986 := by decide
  rcases family_descends (prefixWord ++ tailWord_361986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362015 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 1, 8]
def baseStart_362015 : Nat := 118140960795 + 362015 * 2 ^ 59
def prefixEnd_362015 : Nat := 4983230072969 + 3 ^ 40 * 362015 * 2
def baseEnd_362015 : Nat := 61962566379168782782543

theorem tailTrace_362015 : CollatzResearch.WordTrace tailWord_362015 prefixEnd_362015 61962566379168782782543 := by
  unfold tailWord_362015
  simp only [CollatzResearch.WordTrace]
  refine ⟨13203771783488957084791499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8802514522325971389860999 13203771783488957084791499)
  ·
    refine ⟨19805657675233435627187249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13203771783488957084791499 19805657675233435627187249)
    ·
      refine ⟨14854243256425076720390437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19805657675233435627187249 14854243256425076720390437)
      ·
        refine ⟨2785170610579701885073207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14854243256425076720390437 2785170610579701885073207)
        ·
          refine ⟨4177755915869552827609811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785170610579701885073207 4177755915869552827609811)
          ·
            refine ⟨6266633873804329241414717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4177755915869552827609811 6266633873804329241414717)
            ·
              refine ⟨2349987702676623465530519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6266633873804329241414717 2349987702676623465530519)
              ·
                refine ⟨3524981554014935198295779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2349987702676623465530519 3524981554014935198295779)
                ·
                  refine ⟨5287472331022402797443669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524981554014935198295779 5287472331022402797443669)
                  ·
                    refine ⟨61962566379168782782543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5287472331022402797443669 61962566379168782782543)
                    ·
                      rfl

theorem cell23_362015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_362015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362015 prefixEnd_362015 := by exact prefixLift 362015
  have htrace : WordTrace (prefixWord ++ tailWord_362015) baseStart_362015 baseEnd_362015 := by
    simpa [prefixWord, tailWord_362015, baseEnd_362015] using wordTrace_append hprefix tailTrace_362015
  have hstable : (prefixWord ++ tailWord_362015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362015).length < 2 ^ (prefixWord ++ tailWord_362015).sum := by decide
  have hdescent : baseEnd_362015 < baseStart_362015 := by decide
  rcases family_descends (prefixWord ++ tailWord_362015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362016 : List Nat := [2, 1, 1, 6, 1, 1, 2, 3, 2, 1, 3]
def baseStart_362016 : Nat := 118140960795 + 362016 * 2 ^ 59
def prefixEnd_362016 : Nat := 4983230072969 + 3 ^ 40 * 362016 * 2
def baseEnd_362016 : Nat := 185888212618160844435125

theorem tailTrace_362016 : CollatzResearch.WordTrace tailWord_362016 prefixEnd_362016 185888212618160844435125 := by
  unfold tailWord_362016
  simp only [CollatzResearch.WordTrace]
  refine ⟨6601904128242667127788951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8802538837656889503718601 6601904128242667127788951)
  ·
    refine ⟨9902856192364000691683427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6601904128242667127788951 9902856192364000691683427)
    ·
      refine ⟨14854284288546001037525141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9902856192364000691683427 14854284288546001037525141)
      ·
        refine ⟨696294576025593798633991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14854284288546001037525141 696294576025593798633991)
        ·
          refine ⟨1044441864038390697950987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696294576025593798633991 1044441864038390697950987)
          ·
            refine ⟨1566662796057586046926481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044441864038390697950987 1566662796057586046926481)
            ·
              refine ⟨1174997097043189535194861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1566662796057586046926481 1174997097043189535194861)
              ·
                refine ⟨440623911391196075698073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1174997097043189535194861 440623911391196075698073)
                ·
                  refine ⟨330467933543397056773555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440623911391196075698073 330467933543397056773555)
                  ·
                    refine ⟨495701900315095585160333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 330467933543397056773555 495701900315095585160333)
                    ·
                      refine ⟨185888212618160844435125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 495701900315095585160333 185888212618160844435125)
                      ·
                        rfl

theorem cell23_362016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_362016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362016 prefixEnd_362016 := by exact prefixLift 362016
  have htrace : WordTrace (prefixWord ++ tailWord_362016) baseStart_362016 baseEnd_362016 := by
    simpa [prefixWord, tailWord_362016, baseEnd_362016] using wordTrace_append hprefix tailTrace_362016
  have hstable : (prefixWord ++ tailWord_362016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362016).length < 2 ^ (prefixWord ++ tailWord_362016).sum := by decide
  have hdescent : baseEnd_362016 < baseStart_362016 := by decide
  rcases family_descends (prefixWord ++ tailWord_362016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362026 : List Nat := [3, 1, 4, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_362026 : Nat := 118140960795 + 362026 * 2 ^ 59
def prefixEnd_362026 : Nat := 4983230072969 + 3 ^ 40 * 362026 * 2
def baseEnd_362026 : Nat := 185893347424705805310079

theorem tailTrace_362026 : CollatzResearch.WordTrace tailWord_362026 prefixEnd_362026 185893347424705805310079 := by
  unfold tailWord_362026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3301043246612276490860483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8802781990966070642294621 3301043246612276490860483)
  ·
    refine ⟨4951564869918414736290725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3301043246612276490860483 4951564869918414736290725)
    ·
      refine ⟨928418413109702763054511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4951564869918414736290725 928418413109702763054511)
      ·
        refine ⟨1392627619664554144581767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 928418413109702763054511 1392627619664554144581767)
        ·
          refine ⟨2088941429496831216872651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392627619664554144581767 2088941429496831216872651)
          ·
            refine ⟨3133412144245246825308977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088941429496831216872651 3133412144245246825308977)
            ·
              refine ⟨2350059108183935118981733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3133412144245246825308977 2350059108183935118981733)
              ·
                refine ⟨440636082784487834809075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2350059108183935118981733 440636082784487834809075)
                ·
                  refine ⟨660954124176731752213613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440636082784487834809075 660954124176731752213613)
                  ·
                    refine ⟨247857796566274407080105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 660954124176731752213613 247857796566274407080105)
                    ·
                      refine ⟨185893347424705805310079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 247857796566274407080105 185893347424705805310079)
                      ·
                        rfl

theorem cell23_362026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_362026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362026 prefixEnd_362026 := by exact prefixLift 362026
  have htrace : WordTrace (prefixWord ++ tailWord_362026) baseStart_362026 baseEnd_362026 := by
    simpa [prefixWord, tailWord_362026, baseEnd_362026] using wordTrace_append hprefix tailTrace_362026
  have hstable : (prefixWord ++ tailWord_362026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362026).length < 2 ^ (prefixWord ++ tailWord_362026).sum := by decide
  have hdescent : baseEnd_362026 < baseStart_362026 := by decide
  rcases family_descends (prefixWord ++ tailWord_362026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362039 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 1, 4, 2]
def baseStart_362039 : Nat := 118140960795 + 362039 * 2 ^ 59
def prefixEnd_362039 : Nat := 4983230072969 + 3 ^ 40 * 362039 * 2
def baseEnd_362039 : Nat := 185900022673214254447519

theorem tailTrace_362039 : CollatzResearch.WordTrace tailWord_362039 prefixEnd_362039 185900022673214254447519 := by
  unfold tailWord_362039
  simp only [CollatzResearch.WordTrace]
  refine ⟨13204647135402009183665171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8803098090268006122443447 13204647135402009183665171)
  ·
    refine ⟨19806970703103013775497757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13204647135402009183665171 19806970703103013775497757)
    ·
      refine ⟨7427614013663630165811659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19806970703103013775497757 7427614013663630165811659)
      ·
        refine ⟨11141421020495445248717489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7427614013663630165811659 11141421020495445248717489)
        ·
          refine ⟨8356065765371583936538117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11141421020495445248717489 8356065765371583936538117)
          ·
            refine ⟨1566762331007171988100897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8356065765371583936538117 1566762331007171988100897)
            ·
              refine ⟨1175071748255378991075673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1566762331007171988100897 1175071748255378991075673)
              ·
                refine ⟨881303811191534243306755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175071748255378991075673 881303811191534243306755)
                ·
                  refine ⟨1321955716787301364960133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881303811191534243306755 1321955716787301364960133)
                  ·
                    refine ⟨247866696897619005930025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1321955716787301364960133 247866696897619005930025)
                    ·
                      refine ⟨185900022673214254447519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 247866696897619005930025 185900022673214254447519)
                      ·
                        rfl

theorem cell23_362039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 4, 2].length) (baseStart_362039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362039 prefixEnd_362039 := by exact prefixLift 362039
  have htrace : WordTrace (prefixWord ++ tailWord_362039) baseStart_362039 baseEnd_362039 := by
    simpa [prefixWord, tailWord_362039, baseEnd_362039] using wordTrace_append hprefix tailTrace_362039
  have hstable : (prefixWord ++ tailWord_362039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362039).length < 2 ^ (prefixWord ++ tailWord_362039).sum := by decide
  have hdescent : baseEnd_362039 < baseStart_362039 := by decide
  rcases family_descends (prefixWord ++ tailWord_362039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362092 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 2, 5]
def baseStart_362092 : Nat := 118140960795 + 362092 * 2 ^ 59
def prefixEnd_362092 : Nat := 4983230072969 + 3 ^ 40 * 362092 * 2
def baseEnd_362092 : Nat := 61975745715967515694925

theorem tailTrace_362092 : CollatzResearch.WordTrace tailWord_362092 prefixEnd_362092 61975745715967515694925 := by
  unfold tailWord_362092
  simp only [CollatzResearch.WordTrace]
  refine ⟨6603290102104999617672265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8804386802806666156896353 6603290102104999617672265)
  ·
    refine ⟨4952467576578749713254199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6603290102104999617672265 4952467576578749713254199)
    ·
      refine ⟨7428701364868124569881299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4952467576578749713254199 7428701364868124569881299)
      ·
        refine ⟨11143052047302186854821949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7428701364868124569881299 11143052047302186854821949)
        ·
          refine ⟨4178644517738320070558231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11143052047302186854821949 4178644517738320070558231)
          ·
            refine ⟨6267966776607480105837347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178644517738320070558231 6267966776607480105837347)
            ·
              refine ⟨9401950164911220158756021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6267966776607480105837347 9401950164911220158756021)
              ·
                refine ⟨881432827960426889883377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9401950164911220158756021 881432827960426889883377)
                ·
                  refine ⟨661074620970320167412533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 881432827960426889883377 661074620970320167412533)
                  ·
                    refine ⟨61975745715967515694925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 661074620970320167412533 61975745715967515694925)
                    ·
                      rfl

theorem cell23_362092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_362092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362092 prefixEnd_362092 := by exact prefixLift 362092
  have htrace : WordTrace (prefixWord ++ tailWord_362092) baseStart_362092 baseEnd_362092 := by
    simpa [prefixWord, tailWord_362092, baseEnd_362092] using wordTrace_append hprefix tailTrace_362092
  have hstable : (prefixWord ++ tailWord_362092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362092).length < 2 ^ (prefixWord ++ tailWord_362092).sum := by decide
  have hdescent : baseEnd_362092 < baseStart_362092 := by decide
  rcases family_descends (prefixWord ++ tailWord_362092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362096 : List Nat := [2, 1, 1, 1, 6, 3, 1, 3, 5]
def baseStart_362096 : Nat := 118140960795 + 362096 * 2 ^ 59
def prefixEnd_362096 : Nat := 4983230072969 + 3 ^ 40 * 362096 * 2
def baseEnd_362096 : Nat := 20658810118946725714973

theorem tailTrace_362096 : CollatzResearch.WordTrace tailWord_362096 prefixEnd_362096 20658810118946725714973 := by
  unfold tailWord_362096
  simp only [CollatzResearch.WordTrace]
  refine ⟨6603363048097753959245071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8804484064130338612326761 6603363048097753959245071)
  ·
    refine ⟨9905044572146630938867607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6603363048097753959245071 9905044572146630938867607)
    ·
      refine ⟨14857566858219946408301411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9905044572146630938867607 14857566858219946408301411)
      ·
        refine ⟨22286350287329919612452117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14857566858219946408301411 22286350287329919612452117)
        ·
          refine ⟨1044672669718589981833693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22286350287329919612452117 1044672669718589981833693)
          ·
            refine ⟨391752251144471243187635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1044672669718589981833693 391752251144471243187635)
            ·
              refine ⟨587628376716706864781453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391752251144471243187635 587628376716706864781453)
              ·
                refine ⟨220360641268765074293045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 587628376716706864781453 220360641268765074293045)
                ·
                  refine ⟨20658810118946725714973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 220360641268765074293045 20658810118946725714973)
                  ·
                    rfl

theorem cell23_362096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 5].length) (baseStart_362096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362096 prefixEnd_362096 := by exact prefixLift 362096
  have htrace : WordTrace (prefixWord ++ tailWord_362096) baseStart_362096 baseEnd_362096 := by
    simpa [prefixWord, tailWord_362096, baseEnd_362096] using wordTrace_append hprefix tailTrace_362096
  have hstable : (prefixWord ++ tailWord_362096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362096).length < 2 ^ (prefixWord ++ tailWord_362096).sum := by decide
  have hdescent : baseEnd_362096 < baseStart_362096 := by decide
  rcases family_descends (prefixWord ++ tailWord_362096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362109 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_362109 : Nat := 118140960795 + 362109 * 2 ^ 59
def prefixEnd_362109 : Nat := 4983230072969 + 3 ^ 40 * 362109 * 2
def baseEnd_362109 : Nat := 61978655439676326857399

theorem tailTrace_362109 : CollatzResearch.WordTrace tailWord_362109 prefixEnd_362109 61978655439676326857399 := by
  unfold tailWord_362109
  simp only [CollatzResearch.WordTrace]
  refine ⟨13207200245148411138713381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8804800163432274092475587 13207200245148411138713381)
  ·
    refine ⟨2476350045965327088508759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13207200245148411138713381 2476350045965327088508759)
    ·
      refine ⟨3714525068947990632763139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2476350045965327088508759 3714525068947990632763139)
      ·
        refine ⟨5571787603421985949144709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3714525068947990632763139 5571787603421985949144709)
        ·
          refine ⟨1044710175641622365464633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5571787603421985949144709 1044710175641622365464633)
          ·
            refine ⟨783532631731216774098475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1044710175641622365464633 783532631731216774098475)
            ·
              refine ⟨1175298947596825161147713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783532631731216774098475 1175298947596825161147713)
              ·
                refine ⟨881474210697618870860785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175298947596825161147713 881474210697618870860785)
                ·
                  refine ⟨661105658023214153145589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 881474210697618870860785 661105658023214153145589)
                  ·
                    refine ⟨61978655439676326857399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 661105658023214153145589 61978655439676326857399)
                    ·
                      rfl

theorem cell23_362109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_362109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362109 prefixEnd_362109 := by exact prefixLift 362109
  have htrace : WordTrace (prefixWord ++ tailWord_362109) baseStart_362109 baseEnd_362109 := by
    simpa [prefixWord, tailWord_362109, baseEnd_362109] using wordTrace_append hprefix tailTrace_362109
  have hstable : (prefixWord ++ tailWord_362109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362109).length < 2 ^ (prefixWord ++ tailWord_362109).sum := by decide
  have hdescent : baseEnd_362109 < baseStart_362109 := by decide
  rcases family_descends (prefixWord ++ tailWord_362109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362149 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 2, 2, 3]
def baseStart_362149 : Nat := 118140960795 + 362149 * 2 ^ 59
def prefixEnd_362149 : Nat := 4983230072969 + 3 ^ 40 * 362149 * 2
def baseEnd_362149 : Nat := 185956505545208824072013

theorem tailTrace_362149 : CollatzResearch.WordTrace tailWord_362149 prefixEnd_362149 185956505545208824072013 := by
  unfold tailWord_362149
  simp only [CollatzResearch.WordTrace]
  refine ⟨13208659165003497970169501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8805772776668998646779667 13208659165003497970169501)
  ·
    refine ⟨4953247186876311738813563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13208659165003497970169501 4953247186876311738813563)
    ·
      refine ⟨7429870780314467608220345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4953247186876311738813563 7429870780314467608220345)
      ·
        refine ⟨5572403085235850706165259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7429870780314467608220345 5572403085235850706165259)
        ·
          refine ⟨8358604627853776059247889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5572403085235850706165259 8358604627853776059247889)
          ·
            refine ⟨6268953470890332044435917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8358604627853776059247889 6268953470890332044435917)
            ·
              refine ⟨2350857551583874516663469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6268953470890332044435917 2350857551583874516663469)
              ·
                refine ⟨881571581843952943748801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2350857551583874516663469 881571581843952943748801)
                ·
                  refine ⟨661178686382964707811601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 881571581843952943748801 661178686382964707811601)
                  ·
                    refine ⟨495884014787223530858701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 661178686382964707811601 495884014787223530858701)
                    ·
                      refine ⟨185956505545208824072013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 495884014787223530858701 185956505545208824072013)
                      ·
                        rfl

theorem cell23_362149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_362149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362149 prefixEnd_362149 := by exact prefixLift 362149
  have htrace : WordTrace (prefixWord ++ tailWord_362149) baseStart_362149 baseEnd_362149 := by
    simpa [prefixWord, tailWord_362149, baseEnd_362149] using wordTrace_append hprefix tailTrace_362149
  have hstable : (prefixWord ++ tailWord_362149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362149).length < 2 ^ (prefixWord ++ tailWord_362149).sum := by decide
  have hdescent : baseEnd_362149 < baseStart_362149 := by decide
  rcases family_descends (prefixWord ++ tailWord_362149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362179 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 9, 1, 3]
def baseStart_362179 : Nat := 118140960795 + 362179 * 2 ^ 59
def prefixEnd_362179 : Nat := 4983230072969 + 3 ^ 40 * 362179 * 2
def baseEnd_362179 : Nat := 185971909964843706696875

theorem tailTrace_362179 : CollatzResearch.WordTrace tailWord_362179 prefixEnd_362179 185971909964843706696875 := by
  unfold tailWord_362179
  simp only [CollatzResearch.WordTrace]
  refine ⟨13209753354894813093761591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8806502236596542062507727 13209753354894813093761591)
  ·
    refine ⟨19814630032342219640642387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13209753354894813093761591 19814630032342219640642387)
    ·
      refine ⟨29721945048513329460963581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19814630032342219640642387 29721945048513329460963581)
      ·
        refine ⟨11145729393192498547861343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29721945048513329460963581 11145729393192498547861343)
        ·
          refine ⟨16718594089788747821792015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11145729393192498547861343 16718594089788747821792015)
          ·
            refine ⟨25077891134683121732688023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16718594089788747821792015 25077891134683121732688023)
            ·
              refine ⟨37616836702024682599032035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25077891134683121732688023 37616836702024682599032035)
              ·
                refine ⟨56425255053037023898548053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37616836702024682599032035 56425255053037023898548053)
                ·
                  refine ⟨330616728826388811905555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56425255053037023898548053 330616728826388811905555)
                  ·
                    refine ⟨495925093239583217858333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 330616728826388811905555 495925093239583217858333)
                    ·
                      refine ⟨185971909964843706696875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 495925093239583217858333 185971909964843706696875)
                      ·
                        rfl

theorem cell23_362179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_362179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362179 prefixEnd_362179 := by exact prefixLift 362179
  have htrace : WordTrace (prefixWord ++ tailWord_362179) baseStart_362179 baseEnd_362179 := by
    simpa [prefixWord, tailWord_362179, baseEnd_362179] using wordTrace_append hprefix tailTrace_362179
  have hstable : (prefixWord ++ tailWord_362179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362179).length < 2 ^ (prefixWord ++ tailWord_362179).sum := by decide
  have hdescent : baseEnd_362179 < baseStart_362179 := by decide
  rcases family_descends (prefixWord ++ tailWord_362179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362199 : List Nat := [1, 1, 3, 2, 1, 3, 2, 4, 1, 5]
def baseStart_362199 : Nat := 118140960795 + 362199 * 2 ^ 59
def prefixEnd_362199 : Nat := 4983230072969 + 3 ^ 40 * 362199 * 2
def baseEnd_362199 : Nat := 61994059859311209482261

theorem tailTrace_362199 : CollatzResearch.WordTrace tailWord_362199 prefixEnd_362199 61994059859311209482261 := by
  unfold tailWord_362199
  simp only [CollatzResearch.WordTrace]
  refine ⟨13210482814822356509489651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8806988543214904339659767 13210482814822356509489651)
  ·
    refine ⟨19815724222233534764234477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13210482814822356509489651 19815724222233534764234477)
    ·
      refine ⟨7430896583337575536587929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19815724222233534764234477 7430896583337575536587929)
      ·
        refine ⟨5573172437503181652440947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7430896583337575536587929 5573172437503181652440947)
        ·
          refine ⟨8359758656254772478661421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5573172437503181652440947 8359758656254772478661421)
          ·
            refine ⟨3134909496095539679498033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8359758656254772478661421 3134909496095539679498033)
            ·
              refine ⟨2351182122071654759623525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134909496095539679498033 2351182122071654759623525)
              ·
                refine ⟨440846647888435267429411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2351182122071654759623525 440846647888435267429411)
                ·
                  refine ⟨661269971832652901144117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440846647888435267429411 661269971832652901144117)
                  ·
                    refine ⟨61994059859311209482261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 661269971832652901144117 61994059859311209482261)
                    ·
                      rfl

theorem cell23_362199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_362199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362199 prefixEnd_362199 := by exact prefixLift 362199
  have htrace : WordTrace (prefixWord ++ tailWord_362199) baseStart_362199 baseEnd_362199 := by
    simpa [prefixWord, tailWord_362199, baseEnd_362199] using wordTrace_append hprefix tailTrace_362199
  have hstable : (prefixWord ++ tailWord_362199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362199).length < 2 ^ (prefixWord ++ tailWord_362199).sum := by decide
  have hdescent : baseEnd_362199 < baseStart_362199 := by decide
  rcases family_descends (prefixWord ++ tailWord_362199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362216 : List Nat := [2, 1, 4, 1, 3, 2, 1, 3, 1, 5]
def baseStart_362216 : Nat := 118140960795 + 362216 * 2 ^ 59
def prefixEnd_362216 : Nat := 4983230072969 + 3 ^ 40 * 362216 * 2
def baseEnd_362216 : Nat := 61996969583020020644735

theorem tailTrace_362216 : CollatzResearch.WordTrace tailWord_362216 prefixEnd_362216 61996969583020020644735 := by
  unfold tailWord_362216
  simp only [CollatzResearch.WordTrace]
  refine ⟨6605551427880384206429251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8807401903840512275239001 6605551427880384206429251)
  ·
    refine ⟨9908327141820576309643877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6605551427880384206429251 9908327141820576309643877)
    ·
      refine ⟨1857811339091358058058227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9908327141820576309643877 1857811339091358058058227)
      ·
        refine ⟨2786717008637037087087341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857811339091358058058227 2786717008637037087087341)
        ·
          refine ⟨1045018878238888907657753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2786717008637037087087341 1045018878238888907657753)
          ·
            refine ⟨783764158679166680743315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1045018878238888907657753 783764158679166680743315)
            ·
              refine ⟨1175646238018750021114973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783764158679166680743315 1175646238018750021114973)
              ·
                refine ⟨440867339257031257918115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1175646238018750021114973 440867339257031257918115)
                ·
                  refine ⟨661301008885546886877173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440867339257031257918115 661301008885546886877173)
                  ·
                    refine ⟨61996969583020020644735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 661301008885546886877173 61996969583020020644735)
                    ·
                      rfl

theorem cell23_362216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_362216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362216 prefixEnd_362216 := by exact prefixLift 362216
  have htrace : WordTrace (prefixWord ++ tailWord_362216) baseStart_362216 baseEnd_362216 := by
    simpa [prefixWord, tailWord_362216, baseEnd_362216] using wordTrace_append hprefix tailTrace_362216
  have hstable : (prefixWord ++ tailWord_362216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362216).length < 2 ^ (prefixWord ++ tailWord_362216).sum := by decide
  have hdescent : baseEnd_362216 < baseStart_362216 := by decide
  rcases family_descends (prefixWord ++ tailWord_362216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362230 : List Nat := [5, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_362230 : Nat := 118140960795 + 362230 * 2 ^ 59
def prefixEnd_362230 : Nat := 4983230072969 + 3 ^ 40 * 362230 * 2
def baseEnd_362230 : Nat := 185998097478223007159141

theorem tailTrace_362230 : CollatzResearch.WordTrace tailWord_362230 prefixEnd_362230 185998097478223007159141 := by
  unfold tailWord_362230
  simp only [CollatzResearch.WordTrace]
  refine ⟨825725842356878050241759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8807742318473365869245429 825725842356878050241759)
  ·
    refine ⟨1238588763535317075362639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 825725842356878050241759 1238588763535317075362639)
    ·
      refine ⟨1857883145302975613043959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1238588763535317075362639 1857883145302975613043959)
      ·
        refine ⟨2786824717954463419565939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857883145302975613043959 2786824717954463419565939)
        ·
          refine ⟨4180237076931695129348909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786824717954463419565939 4180237076931695129348909)
          ·
            refine ⟨1567588903849385673505841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4180237076931695129348909 1567588903849385673505841)
            ·
              refine ⟨1175691677887039255129381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1567588903849385673505841 1175691677887039255129381)
              ·
                refine ⟨220442189603819860336759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1175691677887039255129381 220442189603819860336759)
                ·
                  refine ⟨330663284405729790505139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220442189603819860336759 330663284405729790505139)
                  ·
                    refine ⟨495994926608594685757709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 330663284405729790505139 495994926608594685757709)
                    ·
                      refine ⟨185998097478223007159141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 495994926608594685757709 185998097478223007159141)
                      ·
                        rfl

theorem cell23_362230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_362230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362230 prefixEnd_362230 := by exact prefixLift 362230
  have htrace : WordTrace (prefixWord ++ tailWord_362230) baseStart_362230 baseEnd_362230 := by
    simpa [prefixWord, tailWord_362230, baseEnd_362230] using wordTrace_append hprefix tailTrace_362230
  have hstable : (prefixWord ++ tailWord_362230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362230).length < 2 ^ (prefixWord ++ tailWord_362230).sum := by decide
  have hdescent : baseEnd_362230 < baseStart_362230 := by decide
  rcases family_descends (prefixWord ++ tailWord_362230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362239 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 3]
def baseStart_362239 : Nat := 118140960795 + 362239 * 2 ^ 59
def prefixEnd_362239 : Nat := 4983230072969 + 3 ^ 40 * 362239 * 2
def baseEnd_362239 : Nat := 186002718804113471946599

theorem tailTrace_362239 : CollatzResearch.WordTrace tailWord_362239 prefixEnd_362239 186002718804113471946599 := by
  unfold tailWord_362239
  simp only [CollatzResearch.WordTrace]
  refine ⟨13211941734677443340945771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8807961156451628893963847 13211941734677443340945771)
  ·
    refine ⟨19817912602016165011418657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13211941734677443340945771 19817912602016165011418657)
    ·
      refine ⟨14863434451512123758563993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19817912602016165011418657 14863434451512123758563993)
      ·
        refine ⟨11147575838634092818922995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14863434451512123758563993 11147575838634092818922995)
        ·
          refine ⟨16721363757951139228384493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11147575838634092818922995 16721363757951139228384493)
          ·
            refine ⟨6270511409231677210644185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16721363757951139228384493 6270511409231677210644185)
            ·
              refine ⟨4702883556923757907983139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6270511409231677210644185 4702883556923757907983139)
              ·
                refine ⟨7054325335385636861974709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4702883556923757907983139 7054325335385636861974709)
                ·
                  refine ⟨661343000192403455810129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7054325335385636861974709 661343000192403455810129)
                  ·
                    refine ⟨496007250144302591857597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 661343000192403455810129 496007250144302591857597)
                    ·
                      refine ⟨186002718804113471946599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 496007250144302591857597 186002718804113471946599)
                      ·
                        rfl

theorem cell23_362239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_362239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362239 prefixEnd_362239 := by exact prefixLift 362239
  have htrace : WordTrace (prefixWord ++ tailWord_362239) baseStart_362239 baseEnd_362239 := by
    simpa [prefixWord, tailWord_362239, baseEnd_362239] using wordTrace_append hprefix tailTrace_362239
  have hstable : (prefixWord ++ tailWord_362239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362239).length < 2 ^ (prefixWord ++ tailWord_362239).sum := by decide
  have hdescent : baseEnd_362239 < baseStart_362239 := by decide
  rcases family_descends (prefixWord ++ tailWord_362239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362297 : List Nat := [1, 2, 1, 7, 1, 2, 2, 1, 2, 4]
def baseStart_362297 : Nat := 118140960795 + 362297 * 2 ^ 59
def prefixEnd_362297 : Nat := 4983230072969 + 3 ^ 40 * 362297 * 2
def baseEnd_362297 : Nat := 62010833560691415007111

theorem tailTrace_362297 : CollatzResearch.WordTrace tailWord_362297 prefixEnd_362297 62010833560691415007111 := by
  unfold tailWord_362297
  simp only [CollatzResearch.WordTrace]
  refine ⟨13214057168467319246557145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8809371445644879497704763 13214057168467319246557145)
  ·
    refine ⟨9910542876350489434917859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13214057168467319246557145 9910542876350489434917859)
    ·
      refine ⟨14865814314525734152376789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9910542876350489434917859 14865814314525734152376789)
      ·
        refine ⟨348417522996696894196331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 14865814314525734152376789 348417522996696894196331)
        ·
          refine ⟨522626284495045341294497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348417522996696894196331 522626284495045341294497)
          ·
            refine ⟨391969713371284005970873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522626284495045341294497 391969713371284005970873)
            ·
              refine ⟨293977285028463004478155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391969713371284005970873 293977285028463004478155)
              ·
                refine ⟨440965927542694506717233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293977285028463004478155 440965927542694506717233)
                ·
                  refine ⟨330724445657020880037925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440965927542694506717233 330724445657020880037925)
                  ·
                    refine ⟨62010833560691415007111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 330724445657020880037925 62010833560691415007111)
                    ·
                      rfl

theorem cell23_362297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 2, 4].length) (baseStart_362297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362297 prefixEnd_362297 := by exact prefixLift 362297
  have htrace : WordTrace (prefixWord ++ tailWord_362297) baseStart_362297 baseEnd_362297 := by
    simpa [prefixWord, tailWord_362297, baseEnd_362297] using wordTrace_append hprefix tailTrace_362297
  have hstable : (prefixWord ++ tailWord_362297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362297).length < 2 ^ (prefixWord ++ tailWord_362297).sum := by decide
  have hdescent : baseEnd_362297 < baseStart_362297 := by decide
  rcases family_descends (prefixWord ++ tailWord_362297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362329 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 5]
def baseStart_362329 : Nat := 118140960795 + 362329 * 2 ^ 59
def prefixEnd_362329 : Nat := 4983230072969 + 3 ^ 40 * 362329 * 2
def baseEnd_362329 : Nat := 186048932063018119821185

theorem tailTrace_362329 : CollatzResearch.WordTrace tailWord_362329 prefixEnd_362329 186048932063018119821185 := by
  unfold tailWord_362329
  simp only [CollatzResearch.WordTrace]
  refine ⟨13215224304351388711722041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8810149536234259141148027 13215224304351388711722041)
  ·
    refine ⟨9911418228263541533791531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13215224304351388711722041 9911418228263541533791531)
    ·
      refine ⟨14867127342395312300687297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9911418228263541533791531 14867127342395312300687297)
      ·
        refine ⟨11150345506796484225515473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14867127342395312300687297 11150345506796484225515473)
        ·
          refine ⟨8362759130097363169136605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11150345506796484225515473 8362759130097363169136605)
          ·
            refine ⟨3136034673786511188426227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8362759130097363169136605 3136034673786511188426227)
            ·
              refine ⟨4704052010679766782639341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136034673786511188426227 4704052010679766782639341)
              ·
                refine ⟨1764019504004912543489753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4704052010679766782639341 1764019504004912543489753)
                ·
                  refine ⟨1323014628003684407617315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1764019504004912543489753 1323014628003684407617315)
                  ·
                    refine ⟨1984521942005526611425973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1323014628003684407617315 1984521942005526611425973)
                    ·
                      refine ⟨186048932063018119821185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1984521942005526611425973 186048932063018119821185)
                      ·
                        rfl

theorem cell23_362329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_362329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362329 prefixEnd_362329 := by exact prefixLift 362329
  have htrace : WordTrace (prefixWord ++ tailWord_362329) baseStart_362329 baseEnd_362329 := by
    simpa [prefixWord, tailWord_362329, baseEnd_362329] using wordTrace_append hprefix tailTrace_362329
  have hstable : (prefixWord ++ tailWord_362329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362329).length < 2 ^ (prefixWord ++ tailWord_362329).sum := by decide
  have hdescent : baseEnd_362329 < baseStart_362329 := by decide
  rcases family_descends (prefixWord ++ tailWord_362329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362330 : List Nat := [3, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2]
def baseStart_362330 : Nat := 118140960795 + 362330 * 2 ^ 59
def prefixEnd_362330 : Nat := 4983230072969 + 3 ^ 40 * 362330 * 2
def baseEnd_362330 : Nat := 186049445543672615908681

theorem tailTrace_362330 : CollatzResearch.WordTrace tailWord_362330 prefixEnd_362330 186049445543672615908681 := by
  unfold tailWord_362330
  simp only [CollatzResearch.WordTrace]
  refine ⟨3303815194336941470627111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8810173851565177255005629 3303815194336941470627111)
  ·
    refine ⟨4955722791505412205940667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3303815194336941470627111 4955722791505412205940667)
    ·
      refine ⟨7433584187258118308911001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4955722791505412205940667 7433584187258118308911001)
      ·
        refine ⟨5575188140443588731683251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7433584187258118308911001 5575188140443588731683251)
        ·
          refine ⟨8362782210665383097524877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5575188140443588731683251 8362782210665383097524877)
          ·
            refine ⟨3136043328999518661571829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8362782210665383097524877 3136043328999518661571829)
            ·
              refine ⟨294004062093704874522359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3136043328999518661571829 294004062093704874522359)
              ·
                refine ⟨441006093140557311783539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294004062093704874522359 441006093140557311783539)
                ·
                  refine ⟨661509139710835967675309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441006093140557311783539 661509139710835967675309)
                  ·
                    refine ⟨248065927391563487878241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661509139710835967675309 248065927391563487878241)
                    ·
                      refine ⟨186049445543672615908681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 248065927391563487878241 186049445543672615908681)
                      ·
                        rfl

theorem cell23_362330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_362330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362330 prefixEnd_362330 := by exact prefixLift 362330
  have htrace : WordTrace (prefixWord ++ tailWord_362330) baseStart_362330 baseEnd_362330 := by
    simpa [prefixWord, tailWord_362330, baseEnd_362330] using wordTrace_append hprefix tailTrace_362330
  have hstable : (prefixWord ++ tailWord_362330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362330).length < 2 ^ (prefixWord ++ tailWord_362330).sum := by decide
  have hdescent : baseEnd_362330 < baseStart_362330 := by decide
  rcases family_descends (prefixWord ++ tailWord_362330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362426 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 5, 4]
def baseStart_362426 : Nat := 118140960795 + 362426 * 2 ^ 59
def prefixEnd_362426 : Nat := 4983230072969 + 3 ^ 40 * 362426 * 2
def baseEnd_362426 : Nat := 62032913228834746769413

theorem tailTrace_362426 : CollatzResearch.WordTrace tailWord_362426 prefixEnd_362426 62032913228834746769413 := by
  unfold tailWord_362426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3304690546249993569500783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8812508123333316185335421 3304690546249993569500783)
  ·
    refine ⟨4957035819374990354251175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3304690546249993569500783 4957035819374990354251175)
    ·
      refine ⟨7435553729062485531376763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4957035819374990354251175 7435553729062485531376763)
      ·
        refine ⟨11153330593593728297065145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7435553729062485531376763 11153330593593728297065145)
        ·
          refine ⟨8364997945195296222798859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11153330593593728297065145 8364997945195296222798859)
          ·
            refine ⟨12547496917792944334198289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8364997945195296222798859 12547496917792944334198289)
            ·
              refine ⟨9410622688344708250648717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12547496917792944334198289 9410622688344708250648717)
              ·
                refine ⟨3528983508129265593993269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9410622688344708250648717 3528983508129265593993269)
                ·
                  refine ⟨330842203887118649436869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3528983508129265593993269 330842203887118649436869)
                  ·
                    refine ⟨62032913228834746769413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 330842203887118649436869 62032913228834746769413)
                    ·
                      rfl

theorem cell23_362426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_362426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362426 prefixEnd_362426 := by exact prefixLift 362426
  have htrace : WordTrace (prefixWord ++ tailWord_362426) baseStart_362426 baseEnd_362426 := by
    simpa [prefixWord, tailWord_362426, baseEnd_362426] using wordTrace_append hprefix tailTrace_362426
  have hstable : (prefixWord ++ tailWord_362426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362426).length < 2 ^ (prefixWord ++ tailWord_362426).sum := by decide
  have hdescent : baseEnd_362426 < baseStart_362426 := by decide
  rcases family_descends (prefixWord ++ tailWord_362426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362450 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_362450 : Nat := 118140960795 + 362450 * 2 ^ 59
def prefixEnd_362450 : Nat := 4983230072969 + 3 ^ 40 * 362450 * 2
def baseEnd_362450 : Nat := 186111063222212146408129

theorem tailTrace_362450 : CollatzResearch.WordTrace tailWord_362450 prefixEnd_362450 186111063222212146408129 := by
  unfold tailWord_362450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3304909384228256594219201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8813091691275350917917869 3304909384228256594219201)
  ·
    refine ⟨2478682038171192445664401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3304909384228256594219201 2478682038171192445664401)
    ·
      refine ⟨1859011528628394334248301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2478682038171192445664401 1859011528628394334248301)
      ·
        refine ⟨697129323235647875343113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1859011528628394334248301 697129323235647875343113)
        ·
          refine ⟨522846992426735906507335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697129323235647875343113 522846992426735906507335)
          ·
            refine ⟨784270488640103859761003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522846992426735906507335 784270488640103859761003)
            ·
              refine ⟨1176405732960155789641505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784270488640103859761003 1176405732960155789641505)
              ·
                refine ⟨882304299720116842231129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1176405732960155789641505 882304299720116842231129)
                ·
                  refine ⟨661728224790087631673347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 882304299720116842231129 661728224790087631673347)
                  ·
                    refine ⟨992592337185131447510021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 661728224790087631673347 992592337185131447510021)
                    ·
                      refine ⟨186111063222212146408129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 992592337185131447510021 186111063222212146408129)
                      ·
                        rfl

theorem cell23_362450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_362450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362450 prefixEnd_362450 := by exact prefixLift 362450
  have htrace : WordTrace (prefixWord ++ tailWord_362450) baseStart_362450 baseEnd_362450 := by
    simpa [prefixWord, tailWord_362450, baseEnd_362450] using wordTrace_append hprefix tailTrace_362450
  have hstable : (prefixWord ++ tailWord_362450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362450).length < 2 ^ (prefixWord ++ tailWord_362450).sum := by decide
  have hdescent : baseEnd_362450 < baseStart_362450 := by decide
  rcases family_descends (prefixWord ++ tailWord_362450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362453 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_362453 : Nat := 118140960795 + 362453 * 2 ^ 59
def prefixEnd_362453 : Nat := 4983230072969 + 3 ^ 40 * 362453 * 2
def baseEnd_362453 : Nat := 186112603664175634670615

theorem tailTrace_362453 : CollatzResearch.WordTrace tailWord_362453 prefixEnd_362453 186112603664175634670615 := by
  unfold tailWord_362453
  simp only [CollatzResearch.WordTrace]
  refine ⟨13219746955902157889236013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8813164637268105259490675 13219746955902157889236013)
  ·
    refine ⟨4957405108463309208463505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13219746955902157889236013 4957405108463309208463505)
    ·
      refine ⟨3718053831347481906347629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4957405108463309208463505 3718053831347481906347629)
      ·
        refine ⟨1394270186755305714880361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3718053831347481906347629 1394270186755305714880361)
        ·
          refine ⟨1045702640066479286160271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1394270186755305714880361 1045702640066479286160271)
          ·
            refine ⟨1568553960099718929240407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045702640066479286160271 1568553960099718929240407)
            ·
              refine ⟨2352830940149578393860611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568553960099718929240407 2352830940149578393860611)
              ·
                refine ⟨3529246410224367590790917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352830940149578393860611 3529246410224367590790917)
                ·
                  refine ⟨661733701917068923273297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3529246410224367590790917 661733701917068923273297)
                  ·
                    refine ⟨496300276437801692454973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 661733701917068923273297 496300276437801692454973)
                    ·
                      refine ⟨186112603664175634670615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 496300276437801692454973 186112603664175634670615)
                      ·
                        rfl

theorem cell23_362453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_362453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362453 prefixEnd_362453 := by exact prefixLift 362453
  have htrace : WordTrace (prefixWord ++ tailWord_362453) baseStart_362453 baseEnd_362453 := by
    simpa [prefixWord, tailWord_362453, baseEnd_362453] using wordTrace_append hprefix tailTrace_362453
  have hstable : (prefixWord ++ tailWord_362453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362453).length < 2 ^ (prefixWord ++ tailWord_362453).sum := by decide
  have hdescent : baseEnd_362453 < baseStart_362453 := by decide
  rcases family_descends (prefixWord ++ tailWord_362453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362456 : List Nat := [2, 1, 2, 2, 2, 2, 2, 4, 6]
def baseStart_362456 : Nat := 118140960795 + 362456 * 2 ^ 59
def prefixEnd_362456 : Nat := 4983230072969 + 3 ^ 40 * 362456 * 2
def baseEnd_362456 : Nat := 20679349345126569214789

theorem tailTrace_362456 : CollatzResearch.WordTrace tailWord_362456 prefixEnd_362456 20679349345126569214789 := by
  unfold tailWord_362456
  simp only [CollatzResearch.WordTrace]
  refine ⟨6609928187445644700797611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8813237583260859601063481 6609928187445644700797611)
  ·
    refine ⟨9914892281168467051196417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6609928187445644700797611 9914892281168467051196417)
    ·
      refine ⟨7436169210876350288397313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9914892281168467051196417 7436169210876350288397313)
      ·
        refine ⟨5577126908157262716297985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7436169210876350288397313 5577126908157262716297985)
        ·
          refine ⟨4182845181117947037223489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5577126908157262716297985 4182845181117947037223489)
          ·
            refine ⟨3137133885838460277917617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4182845181117947037223489 3137133885838460277917617)
            ·
              refine ⟨2352850414378845208438213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3137133885838460277917617 2352850414378845208438213)
              ·
                refine ⟨441159452696033476582165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2352850414378845208438213 441159452696033476582165)
                ·
                  refine ⟨20679349345126569214789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 441159452696033476582165 20679349345126569214789)
                  ·
                    rfl

theorem cell23_362456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 6].length) (baseStart_362456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362456 prefixEnd_362456 := by exact prefixLift 362456
  have htrace : WordTrace (prefixWord ++ tailWord_362456) baseStart_362456 baseEnd_362456 := by
    simpa [prefixWord, tailWord_362456, baseEnd_362456] using wordTrace_append hprefix tailTrace_362456
  have hstable : (prefixWord ++ tailWord_362456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362456).length < 2 ^ (prefixWord ++ tailWord_362456).sum := by decide
  have hdescent : baseEnd_362456 < baseStart_362456 := by decide
  rcases family_descends (prefixWord ++ tailWord_362456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362483 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 3, 1, 3]
def baseStart_362483 : Nat := 118140960795 + 362483 * 2 ^ 59
def prefixEnd_362483 : Nat := 4983230072969 + 3 ^ 40 * 362483 * 2
def baseEnd_362483 : Nat := 186128008083810517295477

theorem tailTrace_362483 : CollatzResearch.WordTrace tailWord_362483 prefixEnd_362483 186128008083810517295477 := by
  unfold tailWord_362483
  simp only [CollatzResearch.WordTrace]
  refine ⟨13220841145793473012828103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8813894097195648675218735 13220841145793473012828103)
  ·
    refine ⟨19831261718690209519242155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13220841145793473012828103 19831261718690209519242155)
    ·
      refine ⟨29746892578035314278863233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19831261718690209519242155 29746892578035314278863233)
      ·
        refine ⟨22310169433526485709147425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29746892578035314278863233 22310169433526485709147425)
        ·
          refine ⟨16732627075144864281860569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22310169433526485709147425 16732627075144864281860569)
          ·
            refine ⟨12549470306358648211395427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16732627075144864281860569 12549470306358648211395427)
            ·
              refine ⟨18824205459537972317093141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12549470306358648211395427 18824205459537972317093141)
              ·
                refine ⟨882384630915842452363741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18824205459537972317093141 882384630915842452363741)
                ·
                  refine ⟨330894236593440919636403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882384630915842452363741 330894236593440919636403)
                  ·
                    refine ⟨496341354890161379454605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 330894236593440919636403 496341354890161379454605)
                    ·
                      refine ⟨186128008083810517295477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 496341354890161379454605 186128008083810517295477)
                      ·
                        rfl

theorem cell23_362483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 1, 3].length) (baseStart_362483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362483 prefixEnd_362483 := by exact prefixLift 362483
  have htrace : WordTrace (prefixWord ++ tailWord_362483) baseStart_362483 baseEnd_362483 := by
    simpa [prefixWord, tailWord_362483, baseEnd_362483] using wordTrace_append hprefix tailTrace_362483
  have hstable : (prefixWord ++ tailWord_362483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362483).length < 2 ^ (prefixWord ++ tailWord_362483).sum := by decide
  have hdescent : baseEnd_362483 < baseStart_362483 := by decide
  rcases family_descends (prefixWord ++ tailWord_362483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362493 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 1, 5, 2]
def baseStart_362493 : Nat := 118140960795 + 362493 * 2 ^ 59
def prefixEnd_362493 : Nat := 4983230072969 + 3 ^ 40 * 362493 * 2
def baseEnd_362493 : Nat := 186133142890355478170431

theorem tailTrace_362493 : CollatzResearch.WordTrace tailWord_362493 prefixEnd_362493 186133142890355478170431 := by
  unfold tailWord_362493
  simp only [CollatzResearch.WordTrace]
  refine ⟨13221205875757244720692133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8814137250504829813794755 13221205875757244720692133)
  ·
    refine ⟨2478976101704483385129775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13221205875757244720692133 2478976101704483385129775)
    ·
      refine ⟨3718464152556725077694663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2478976101704483385129775 3718464152556725077694663)
      ·
        refine ⟨5577696228835087616541995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3718464152556725077694663 5577696228835087616541995)
        ·
          refine ⟨8366544343252631424812993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5577696228835087616541995 8366544343252631424812993)
          ·
            refine ⟨6274908257439473568609745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8366544343252631424812993 6274908257439473568609745)
            ·
              refine ⟨4706181193079605176457309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6274908257439473568609745 4706181193079605176457309)
              ·
                refine ⟨1764817947404851941171491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4706181193079605176457309 1764817947404851941171491)
                ·
                  refine ⟨2647226921107277911757237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764817947404851941171491 2647226921107277911757237)
                  ·
                    refine ⟨248177523853807304227241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2647226921107277911757237 248177523853807304227241)
                    ·
                      refine ⟨186133142890355478170431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 248177523853807304227241 186133142890355478170431)
                      ·
                        rfl

theorem cell23_362493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_362493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362493 prefixEnd_362493 := by exact prefixLift 362493
  have htrace : WordTrace (prefixWord ++ tailWord_362493) baseStart_362493 baseEnd_362493 := by
    simpa [prefixWord, tailWord_362493, baseEnd_362493] using wordTrace_append hprefix tailTrace_362493
  have hstable : (prefixWord ++ tailWord_362493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362493).length < 2 ^ (prefixWord ++ tailWord_362493).sum := by decide
  have hdescent : baseEnd_362493 < baseStart_362493 := by decide
  rcases family_descends (prefixWord ++ tailWord_362493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362510 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2]
def baseStart_362510 : Nat := 118140960795 + 362510 * 2 ^ 59
def prefixEnd_362510 : Nat := 4983230072969 + 3 ^ 40 * 362510 * 2
def baseEnd_362510 : Nat := 186141872061481911657853

theorem tailTrace_362510 : CollatzResearch.WordTrace tailWord_362510 prefixEnd_362510 186141872061481911657853 := by
  unfold tailWord_362510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652728239586957078007623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8814550611130437749373989 1652728239586957078007623)
  ·
    refine ⟨2479092359380435617011435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1652728239586957078007623 2479092359380435617011435)
    ·
      refine ⟨3718638539070653425517153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2479092359380435617011435 3718638539070653425517153)
      ·
        refine ⟨2788978904302990069137865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3718638539070653425517153 2788978904302990069137865)
        ·
          refine ⟨2091734178227242551853399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2788978904302990069137865 2091734178227242551853399)
          ·
            refine ⟨3137601267340863827780099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091734178227242551853399 3137601267340863827780099)
            ·
              refine ⟨4706401901011295741670149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3137601267340863827780099 4706401901011295741670149)
              ·
                refine ⟨882450356439617951563153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4706401901011295741670149 882450356439617951563153)
                ·
                  refine ⟨661837767329713463672365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 882450356439617951563153 661837767329713463672365)
                  ·
                    refine ⟨248189162748642548877137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661837767329713463672365 248189162748642548877137)
                    ·
                      refine ⟨186141872061481911657853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 248189162748642548877137 186141872061481911657853)
                      ·
                        rfl

theorem cell23_362510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_362510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362510 prefixEnd_362510 := by exact prefixLift 362510
  have htrace : WordTrace (prefixWord ++ tailWord_362510) baseStart_362510 baseEnd_362510 := by
    simpa [prefixWord, tailWord_362510, baseEnd_362510] using wordTrace_append hprefix tailTrace_362510
  have hstable : (prefixWord ++ tailWord_362510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362510).length < 2 ^ (prefixWord ++ tailWord_362510).sum := by decide
  have hdescent : baseEnd_362510 < baseStart_362510 := by decide
  rcases family_descends (prefixWord ++ tailWord_362510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362533 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 1, 6]
def baseStart_362533 : Nat := 118140960795 + 362533 * 2 ^ 59
def prefixEnd_362533 : Nat := 4983230072969 + 3 ^ 40 * 362533 * 2
def baseEnd_362533 : Nat := 62051227372178440556749

theorem tailTrace_362533 : CollatzResearch.WordTrace tailWord_362533 prefixEnd_362533 62051227372178440556749 := by
  unfold tailWord_362533
  simp only [CollatzResearch.WordTrace]
  refine ⟨13222664795612331552148253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8815109863741554368098835 13222664795612331552148253)
  ·
    refine ⟨4958499298354624332055595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13222664795612331552148253 4958499298354624332055595)
    ·
      refine ⟨7437748947531936498083393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4958499298354624332055595 7437748947531936498083393)
      ·
        refine ⟨5578311710648952373562545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7437748947531936498083393 5578311710648952373562545)
        ·
          refine ⟨4183733782986714280171909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5578311710648952373562545 4183733782986714280171909)
          ·
            refine ⟨784450084310008927532233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4183733782986714280171909 784450084310008927532233)
            ·
              refine ⟨588337563232506695649175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784450084310008927532233 588337563232506695649175)
              ·
                refine ⟨882506344848760043473763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588337563232506695649175 882506344848760043473763)
                ·
                  refine ⟨1323759517273140065210645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882506344848760043473763 1323759517273140065210645)
                  ·
                    refine ⟨62051227372178440556749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1323759517273140065210645 62051227372178440556749)
                    ·
                      rfl

theorem cell23_362533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_362533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362533 prefixEnd_362533 := by exact prefixLift 362533
  have htrace : WordTrace (prefixWord ++ tailWord_362533) baseStart_362533 baseEnd_362533 := by
    simpa [prefixWord, tailWord_362533, baseEnd_362533] using wordTrace_append hprefix tailTrace_362533
  have hstable : (prefixWord ++ tailWord_362533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362533).length < 2 ^ (prefixWord ++ tailWord_362533).sum := by decide
  have hdescent : baseEnd_362533 < baseStart_362533 := by decide
  rcases family_descends (prefixWord ++ tailWord_362533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362550 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_362550 : Nat := 118140960795 + 362550 * 2 ^ 59
def prefixEnd_362550 : Nat := 4983230072969 + 3 ^ 40 * 362550 * 2
def baseEnd_362550 : Nat := 62054137095887251719223

theorem tailTrace_362550 : CollatzResearch.WordTrace tailWord_362550 prefixEnd_362550 62054137095887251719223 := by
  unfold tailWord_362550
  simp only [CollatzResearch.WordTrace]
  refine ⟨826455302284421465969819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8815523224367162303678069 826455302284421465969819)
  ·
    refine ⟨1239682953426632198954729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 826455302284421465969819 1239682953426632198954729)
    ·
      refine ⟨929762215069974149216047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1239682953426632198954729 929762215069974149216047)
      ·
        refine ⟨1394643322604961223824071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929762215069974149216047 1394643322604961223824071)
        ·
          refine ⟨2091964983907441835736107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1394643322604961223824071 2091964983907441835736107)
          ·
            refine ⟨3137947475861162753604161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091964983907441835736107 3137947475861162753604161)
            ·
              refine ⟨2353460606895872065203121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3137947475861162753604161 2353460606895872065203121)
              ·
                refine ⟨1765095455171904048902341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2353460606895872065203121 1765095455171904048902341)
                ·
                  refine ⟨330955397844732009169189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1765095455171904048902341 330955397844732009169189)
                  ·
                    refine ⟨62054137095887251719223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 330955397844732009169189 62054137095887251719223)
                    ·
                      rfl

theorem cell23_362550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_362550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362550 prefixEnd_362550 := by exact prefixLift 362550
  have htrace : WordTrace (prefixWord ++ tailWord_362550) baseStart_362550 baseEnd_362550 := by
    simpa [prefixWord, tailWord_362550, baseEnd_362550] using wordTrace_append hprefix tailTrace_362550
  have hstable : (prefixWord ++ tailWord_362550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362550).length < 2 ^ (prefixWord ++ tailWord_362550).sum := by decide
  have hdescent : baseEnd_362550 < baseStart_362550 := by decide
  rcases family_descends (prefixWord ++ tailWord_362550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362560 : List Nat := [2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 3]
def baseStart_362560 : Nat := 118140960795 + 362560 * 2 ^ 59
def prefixEnd_362560 : Nat := 4983230072969 + 3 ^ 40 * 362560 * 2
def baseEnd_362560 : Nat := 186167546094206716032623

theorem tailTrace_362560 : CollatzResearch.WordTrace tailWord_362560 prefixEnd_362560 186167546094206716032623 := by
  unfold tailWord_362560
  simp only [CollatzResearch.WordTrace]
  refine ⟨6611824783257257581690567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8815766377676343442254089 6611824783257257581690567)
  ·
    refine ⟨9917737174885886372535851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6611824783257257581690567 9917737174885886372535851)
    ·
      refine ⟨14876605762328829558803777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9917737174885886372535851 14876605762328829558803777)
      ·
        refine ⟨11157454321746622169102833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14876605762328829558803777 11157454321746622169102833)
        ·
          refine ⟨8368090741309966626827125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11157454321746622169102833 8368090741309966626827125)
          ·
            refine ⟨784508506997809371265043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8368090741309966626827125 784508506997809371265043)
            ·
              refine ⟨1176762760496714056897565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784508506997809371265043 1176762760496714056897565)
              ·
                refine ⟨441286035186267771336587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1176762760496714056897565 441286035186267771336587)
                ·
                  refine ⟨661929052779401657004881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441286035186267771336587 661929052779401657004881)
                  ·
                    refine ⟨496446789584551242753661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 661929052779401657004881 496446789584551242753661)
                    ·
                      refine ⟨186167546094206716032623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 496446789584551242753661 186167546094206716032623)
                      ·
                        rfl

theorem cell23_362560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_362560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362560 prefixEnd_362560 := by exact prefixLift 362560
  have htrace : WordTrace (prefixWord ++ tailWord_362560) baseStart_362560 baseEnd_362560 := by
    simpa [prefixWord, tailWord_362560, baseEnd_362560] using wordTrace_append hprefix tailTrace_362560
  have hstable : (prefixWord ++ tailWord_362560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362560).length < 2 ^ (prefixWord ++ tailWord_362560).sum := by decide
  have hdescent : baseEnd_362560 < baseStart_362560 := by decide
  rcases family_descends (prefixWord ++ tailWord_362560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362574 : List Nat := [4, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2]
def baseStart_362574 : Nat := 118140960795 + 362574 * 2 ^ 59
def prefixEnd_362574 : Nat := 4983230072969 + 3 ^ 40 * 362574 * 2
def baseEnd_362574 : Nat := 186174734823369661257559

theorem tailTrace_362574 : CollatzResearch.WordTrace tailWord_362574 prefixEnd_362574 186174734823369661257559 := by
  unfold tailWord_362574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653020023557974444298847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8816106792309197036260517 1653020023557974444298847)
  ·
    refine ⟨2479530035336961666448271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1653020023557974444298847 2479530035336961666448271)
    ·
      refine ⟨3719295053005442499672407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2479530035336961666448271 3719295053005442499672407)
      ·
        refine ⟨5578942579508163749508611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3719295053005442499672407 5578942579508163749508611)
        ·
          refine ⟨8368413869262245624262917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5578942579508163749508611 8368413869262245624262917)
          ·
            refine ⟨1569077600486671054549297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8368413869262245624262917 1569077600486671054549297)
            ·
              refine ⟨1176808200365003290911973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569077600486671054549297 1176808200365003290911973)
              ·
                refine ⟨220651537568438117045995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1176808200365003290911973 220651537568438117045995)
                ·
                  refine ⟨330977306352657175568993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220651537568438117045995 330977306352657175568993)
                  ·
                    refine ⟨248232979764492881676745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 330977306352657175568993 248232979764492881676745)
                    ·
                      refine ⟨186174734823369661257559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 248232979764492881676745 186174734823369661257559)
                      ·
                        rfl

theorem cell23_362574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_362574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362574 prefixEnd_362574 := by exact prefixLift 362574
  have htrace : WordTrace (prefixWord ++ tailWord_362574) baseStart_362574 baseEnd_362574 := by
    simpa [prefixWord, tailWord_362574, baseEnd_362574] using wordTrace_append hprefix tailTrace_362574
  have hstable : (prefixWord ++ tailWord_362574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362574).length < 2 ^ (prefixWord ++ tailWord_362574).sum := by decide
  have hdescent : baseEnd_362574 < baseStart_362574 := by decide
  rcases family_descends (prefixWord ++ tailWord_362574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362594 : List Nat := [3, 3, 2, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_362594 : Nat := 118140960795 + 362594 * 2 ^ 59
def prefixEnd_362594 : Nat := 4983230072969 + 3 ^ 40 * 362594 * 2
def baseEnd_362594 : Nat := 186185004436459583007467

theorem tailTrace_362594 : CollatzResearch.WordTrace tailWord_362594 prefixEnd_362594 186185004436459583007467 := by
  unfold tailWord_362594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3306222412097834742529709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8816593098927559313412557 3306222412097834742529709)
  ·
    refine ⟨1239833404536688028448641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3306222412097834742529709 1239833404536688028448641)
    ·
      refine ⟨929875053402516021336481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1239833404536688028448641 929875053402516021336481)
      ·
        refine ⟨697406290051887016002361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 929875053402516021336481 697406290051887016002361)
        ·
          refine ⟨523054717538915262001771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697406290051887016002361 523054717538915262001771)
          ·
            refine ⟨784582076308372893002657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523054717538915262001771 784582076308372893002657)
            ·
              refine ⟨588436557231279669751993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784582076308372893002657 588436557231279669751993)
              ·
                refine ⟨441327417923459752313995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588436557231279669751993 441327417923459752313995)
                ·
                  refine ⟨661991126885189628470993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441327417923459752313995 661991126885189628470993)
                  ·
                    refine ⟨496493345163892221353245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 661991126885189628470993 496493345163892221353245)
                    ·
                      refine ⟨186185004436459583007467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 496493345163892221353245 186185004436459583007467)
                      ·
                        rfl

theorem cell23_362594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_362594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362594 prefixEnd_362594 := by exact prefixLift 362594
  have htrace : WordTrace (prefixWord ++ tailWord_362594) baseStart_362594 baseEnd_362594 := by
    simpa [prefixWord, tailWord_362594, baseEnd_362594] using wordTrace_append hprefix tailTrace_362594
  have hstable : (prefixWord ++ tailWord_362594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362594).length < 2 ^ (prefixWord ++ tailWord_362594).sum := by decide
  have hdescent : baseEnd_362594 < baseStart_362594 := by decide
  rcases family_descends (prefixWord ++ tailWord_362594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362617 : List Nat := [1, 2, 1, 3, 4, 1, 2, 3, 1, 3, 2]
def baseStart_362617 : Nat := 118140960795 + 362617 * 2 ^ 59
def prefixEnd_362617 : Nat := 4983230072969 + 3 ^ 40 * 362617 * 2
def baseEnd_362617 : Nat := 186196814491512993019861

theorem tailTrace_362617 : CollatzResearch.WordTrace tailWord_362617 prefixEnd_362617 186196814491512993019861 := by
  unfold tailWord_362617
  simp only [CollatzResearch.WordTrace]
  refine ⟨13225728527308013898206105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8817152351538675932137403 13225728527308013898206105)
  ·
    refine ⟨9919296395481010423654579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13225728527308013898206105 9919296395481010423654579)
    ·
      refine ⟨14878944593221515635481869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9919296395481010423654579 14878944593221515635481869)
      ·
        refine ⟨5579604222458068363305701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14878944593221515635481869 5579604222458068363305701)
        ·
          refine ⟨1046175791710887818119819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5579604222458068363305701 1046175791710887818119819)
          ·
            refine ⟨1569263687566331727179729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046175791710887818119819 1569263687566331727179729)
            ·
              refine ⟨1176947765674748795384797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569263687566331727179729 1176947765674748795384797)
              ·
                refine ⟨441355412128030798269299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1176947765674748795384797 441355412128030798269299)
                ·
                  refine ⟨662033118192046197403949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441355412128030798269299 662033118192046197403949)
                  ·
                    refine ⟨248262419322017324026481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 662033118192046197403949 248262419322017324026481)
                    ·
                      refine ⟨186196814491512993019861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 248262419322017324026481 186196814491512993019861)
                      ·
                        rfl

theorem cell23_362617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_362617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362617 prefixEnd_362617 := by exact prefixLift 362617
  have htrace : WordTrace (prefixWord ++ tailWord_362617) baseStart_362617 baseEnd_362617 := by
    simpa [prefixWord, tailWord_362617, baseEnd_362617] using wordTrace_append hprefix tailTrace_362617
  have hstable : (prefixWord ++ tailWord_362617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362617).length < 2 ^ (prefixWord ++ tailWord_362617).sum := by decide
  have hdescent : baseEnd_362617 < baseStart_362617 := by decide
  rcases family_descends (prefixWord ++ tailWord_362617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362633 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 2, 4, 3]
def baseStart_362633 : Nat := 118140960795 + 362633 * 2 ^ 59
def prefixEnd_362633 : Nat := 4983230072969 + 3 ^ 40 * 362633 * 2
def baseEnd_362633 : Nat := 186205030181984930419787

theorem tailTrace_362633 : CollatzResearch.WordTrace tailWord_362633 prefixEnd_362633 186205030181984930419787 := by
  unfold tailWord_362633
  simp only [CollatzResearch.WordTrace]
  refine ⟨13226312095250048630788553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8817541396833365753859035 13226312095250048630788553)
  ·
    refine ⟨9919734071437536473091415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13226312095250048630788553 9919734071437536473091415)
    ·
      refine ⟨14879601107156304709637123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9919734071437536473091415 14879601107156304709637123)
      ·
        refine ⟨22319401660734457064455685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14879601107156304709637123 22319401660734457064455685)
        ·
          refine ⟨4184887811387710699585441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22319401660734457064455685 4184887811387710699585441)
          ·
            refine ⟨3138665858540783024689081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4184887811387710699585441 3138665858540783024689081)
            ·
              refine ⟨2353999393905587268516811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3138665858540783024689081 2353999393905587268516811)
              ·
                refine ⟨3530999090858380902775217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2353999393905587268516811 3530999090858380902775217)
                ·
                  refine ⟨2648249318143785677081413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3530999090858380902775217 2648249318143785677081413)
                  ·
                    refine ⟨496546747151959814452765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2648249318143785677081413 496546747151959814452765)
                    ·
                      refine ⟨186205030181984930419787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 496546747151959814452765 186205030181984930419787)
                      ·
                        rfl

theorem cell23_362633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 4, 3].length) (baseStart_362633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362633 prefixEnd_362633 := by exact prefixLift 362633
  have htrace : WordTrace (prefixWord ++ tailWord_362633) baseStart_362633 baseEnd_362633 := by
    simpa [prefixWord, tailWord_362633, baseEnd_362633] using wordTrace_append hprefix tailTrace_362633
  have hstable : (prefixWord ++ tailWord_362633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362633).length < 2 ^ (prefixWord ++ tailWord_362633).sum := by decide
  have hdescent : baseEnd_362633 < baseStart_362633 := by decide
  rcases family_descends (prefixWord ++ tailWord_362633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362683 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 2, 5]
def baseStart_362683 : Nat := 118140960795 + 362683 * 2 ^ 59
def prefixEnd_362683 : Nat := 4983230072969 + 3 ^ 40 * 362683 * 2
def baseEnd_362683 : Nat := 62076901404903244931519

theorem tailTrace_362683 : CollatzResearch.WordTrace tailWord_362683 prefixEnd_362683 62076901404903244931519 := by
  unfold tailWord_362683
  simp only [CollatzResearch.WordTrace]
  refine ⟨13228135745068907170108703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8818757163379271446739135 13228135745068907170108703)
  ·
    refine ⟨19842203617603360755163055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13228135745068907170108703 19842203617603360755163055)
    ·
      refine ⟨29763305426405041132744583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19842203617603360755163055 29763305426405041132744583)
      ·
        refine ⟨44644958139607561699116875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29763305426405041132744583 44644958139607561699116875)
        ·
          refine ⟨66967437209411342548675313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44644958139607561699116875 66967437209411342548675313)
          ·
            refine ⟨50225577907058506911506485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66967437209411342548675313 50225577907058506911506485)
            ·
              refine ⟨4708647928786735022953733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50225577907058506911506485 4708647928786735022953733)
              ·
                refine ⟨882871486647512816803825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4708647928786735022953733 882871486647512816803825)
                ·
                  refine ⟨662153614985634612602869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 882871486647512816803825 662153614985634612602869)
                  ·
                    refine ⟨62076901404903244931519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 662153614985634612602869 62076901404903244931519)
                    ·
                      rfl

theorem cell23_362683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 5].length) (baseStart_362683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362683 prefixEnd_362683 := by exact prefixLift 362683
  have htrace : WordTrace (prefixWord ++ tailWord_362683) baseStart_362683 baseEnd_362683 := by
    simpa [prefixWord, tailWord_362683, baseEnd_362683] using wordTrace_append hprefix tailTrace_362683
  have hstable : (prefixWord ++ tailWord_362683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362683).length < 2 ^ (prefixWord ++ tailWord_362683).sum := by decide
  have hdescent : baseEnd_362683 < baseStart_362683 := by decide
  rcases family_descends (prefixWord ++ tailWord_362683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362693 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_362693 : Nat := 118140960795 + 362693 * 2 ^ 59
def prefixEnd_362693 : Nat := 4983230072969 + 3 ^ 40 * 362693 * 2
def baseEnd_362693 : Nat := 186235839021254695669511

theorem tailTrace_362693 : CollatzResearch.WordTrace tailWord_362693 prefixEnd_362693 186235839021254695669511 := by
  unfold tailWord_362693
  simp only [CollatzResearch.WordTrace]
  refine ⟨13228500475032678877972733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8819000316688452585315155 13228500475032678877972733)
  ·
    refine ⟨4960687678137254579239775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13228500475032678877972733 4960687678137254579239775)
    ·
      refine ⟨7441031517205881868859663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4960687678137254579239775 7441031517205881868859663)
      ·
        refine ⟨11161547275808822803289495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441031517205881868859663 11161547275808822803289495)
        ·
          refine ⟨16742320913713234204934243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11161547275808822803289495 16742320913713234204934243)
          ·
            refine ⟨25113481370569851307401365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16742320913713234204934243 25113481370569851307401365)
            ·
              refine ⟨1177194439245461780034439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25113481370569851307401365 1177194439245461780034439)
              ·
                refine ⟨1765791658868192670051659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177194439245461780034439 1765791658868192670051659)
                ·
                  refine ⟨2648687488302289005077489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765791658868192670051659 2648687488302289005077489)
                  ·
                    refine ⟨1986515616226716753808117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2648687488302289005077489 1986515616226716753808117)
                    ·
                      refine ⟨186235839021254695669511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1986515616226716753808117 186235839021254695669511)
                      ·
                        rfl

theorem cell23_362693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_362693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362693 prefixEnd_362693 := by exact prefixLift 362693
  have htrace : WordTrace (prefixWord ++ tailWord_362693) baseStart_362693 baseEnd_362693 := by
    simpa [prefixWord, tailWord_362693, baseEnd_362693] using wordTrace_append hprefix tailTrace_362693
  have hstable : (prefixWord ++ tailWord_362693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362693).length < 2 ^ (prefixWord ++ tailWord_362693).sum := by decide
  have hdescent : baseEnd_362693 < baseStart_362693 := by decide
  rcases family_descends (prefixWord ++ tailWord_362693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362703 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 4]
def baseStart_362703 : Nat := 118140960795 + 362703 * 2 ^ 59
def prefixEnd_362703 : Nat := 4983230072969 + 3 ^ 40 * 362703 * 2
def baseEnd_362703 : Nat := 186240973827799656544465

theorem tailTrace_362703 : CollatzResearch.WordTrace tailWord_362703 prefixEnd_362703 186240973827799656544465 := by
  unfold tailWord_362703
  simp only [CollatzResearch.WordTrace]
  refine ⟨13228865204996450585836763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8819243469997633723891175 13228865204996450585836763)
  ·
    refine ⟨19843297807494675878755145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13228865204996450585836763 19843297807494675878755145)
    ·
      refine ⟨14882473355621006909066359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19843297807494675878755145 14882473355621006909066359)
      ·
        refine ⟨22323710033431510363599539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14882473355621006909066359 22323710033431510363599539)
        ·
          refine ⟨33485565050147265545399309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22323710033431510363599539 33485565050147265545399309)
          ·
            refine ⟨12557086893805224579524741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33485565050147265545399309 12557086893805224579524741)
            ·
              refine ⟨2354453792588479608660889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12557086893805224579524741 2354453792588479608660889)
              ·
                refine ⟨1765840344441359706495667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2354453792588479608660889 1765840344441359706495667)
                ·
                  refine ⟨2648760516662039559743501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765840344441359706495667 2648760516662039559743501)
                  ·
                    refine ⟨993285193748264834903813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2648760516662039559743501 993285193748264834903813)
                    ·
                      refine ⟨186240973827799656544465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 993285193748264834903813 186240973827799656544465)
                      ·
                        rfl

theorem cell23_362703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_362703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362703 prefixEnd_362703 := by exact prefixLift 362703
  have htrace : WordTrace (prefixWord ++ tailWord_362703) baseStart_362703 baseEnd_362703 := by
    simpa [prefixWord, tailWord_362703, baseEnd_362703] using wordTrace_append hprefix tailTrace_362703
  have hstable : (prefixWord ++ tailWord_362703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362703).length < 2 ^ (prefixWord ++ tailWord_362703).sum := by decide
  have hdescent : baseEnd_362703 < baseStart_362703 := by decide
  rcases family_descends (prefixWord ++ tailWord_362703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362717 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_362717 : Nat := 118140960795 + 362717 * 2 ^ 59
def prefixEnd_362717 : Nat := 4983230072969 + 3 ^ 40 * 362717 * 2
def baseEnd_362717 : Nat := 62082720852320867256467

theorem tailTrace_362717 : CollatzResearch.WordTrace tailWord_362717 prefixEnd_362717 62082720852320867256467 := by
  unfold tailWord_362717
  simp only [CollatzResearch.WordTrace]
  refine ⟨13229375826945730976846405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8819583884630487317897603 13229375826945730976846405)
  ·
    refine ⟨2480507967552324558158701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13229375826945730976846405 2480507967552324558158701)
    ·
      refine ⟨930190487832121709309513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2480507967552324558158701 930190487832121709309513)
      ·
        refine ⟨697642865874091281982135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 930190487832121709309513 697642865874091281982135)
        ·
          refine ⟨1046464298811136922973203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697642865874091281982135 1046464298811136922973203)
          ·
            refine ⟨1569696448216705384459805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046464298811136922973203 1569696448216705384459805)
            ·
              refine ⟨588636168081264519172427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1569696448216705384459805 588636168081264519172427)
              ·
                refine ⟨882954252121896778758641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588636168081264519172427 882954252121896778758641)
                ·
                  refine ⟨662215689091422584068981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 882954252121896778758641 662215689091422584068981)
                  ·
                    refine ⟨62082720852320867256467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 662215689091422584068981 62082720852320867256467)
                    ·
                      rfl

theorem cell23_362717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_362717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362717 prefixEnd_362717 := by exact prefixLift 362717
  have htrace : WordTrace (prefixWord ++ tailWord_362717) baseStart_362717 baseEnd_362717 := by
    simpa [prefixWord, tailWord_362717, baseEnd_362717] using wordTrace_append hprefix tailTrace_362717
  have hstable : (prefixWord ++ tailWord_362717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362717).length < 2 ^ (prefixWord ++ tailWord_362717).sum := by decide
  have hdescent : baseEnd_362717 < baseStart_362717 := by decide
  rcases family_descends (prefixWord ++ tailWord_362717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362720 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 1, 6, 2]
def baseStart_362720 : Nat := 118140960795 + 362720 * 2 ^ 59
def prefixEnd_362720 : Nat := 4983230072969 + 3 ^ 40 * 362720 * 2
def baseEnd_362720 : Nat := 186249702998926090031887

theorem tailTrace_362720 : CollatzResearch.WordTrace tailWord_362720 prefixEnd_362720 186249702998926090031887 := by
  unfold tailWord_362720
  simp only [CollatzResearch.WordTrace]
  refine ⟨6614742622967431244602807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8819656830623241659470409 6614742622967431244602807)
  ·
    refine ⟨9922113934451146866904211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6614742622967431244602807 9922113934451146866904211)
    ·
      refine ⟨14883170901676720300356317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9922113934451146866904211 14883170901676720300356317)
      ·
        refine ⟨5581189088128770112633619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14883170901676720300356317 5581189088128770112633619)
        ·
          refine ⟨8371783632193155168950429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5581189088128770112633619 8371783632193155168950429)
          ·
            refine ⟨3139418862072433188356411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8371783632193155168950429 3139418862072433188356411)
            ·
              refine ⟨4709128293108649782534617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139418862072433188356411 4709128293108649782534617)
              ·
                refine ⟨3531846219831487336900963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4709128293108649782534617 3531846219831487336900963)
                ·
                  refine ⟨5297769329747231005351445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3531846219831487336900963 5297769329747231005351445)
                  ·
                    refine ⟨248332937331901453375849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5297769329747231005351445 248332937331901453375849)
                    ·
                      refine ⟨186249702998926090031887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 248332937331901453375849 186249702998926090031887)
                      ·
                        rfl

theorem cell23_362720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_362720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362720 prefixEnd_362720 := by exact prefixLift 362720
  have htrace : WordTrace (prefixWord ++ tailWord_362720) baseStart_362720 baseEnd_362720 := by
    simpa [prefixWord, tailWord_362720, baseEnd_362720] using wordTrace_append hprefix tailTrace_362720
  have hstable : (prefixWord ++ tailWord_362720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362720).length < 2 ^ (prefixWord ++ tailWord_362720).sum := by decide
  have hdescent : baseEnd_362720 < baseStart_362720 := by decide
  rcases family_descends (prefixWord ++ tailWord_362720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362730 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 5, 4]
def baseStart_362730 : Nat := 118140960795 + 362730 * 2 ^ 59
def prefixEnd_362730 : Nat := 4983230072969 + 3 ^ 40 * 362730 * 2
def baseEnd_362730 : Nat := 62084945935157016968947

theorem tailTrace_362730 : CollatzResearch.WordTrace tailWord_362730 prefixEnd_362730 62084945935157016968947 := by
  unfold tailWord_362730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307462493974658549267411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8819899983932422798046429 3307462493974658549267411)
  ·
    refine ⟨4961193740961987823901117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3307462493974658549267411 4961193740961987823901117)
    ·
      refine ⟨1860447652860745433962919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4961193740961987823901117 1860447652860745433962919)
      ·
        refine ⟨2790671479291118150944379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1860447652860745433962919 2790671479291118150944379)
        ·
          refine ⟨4186007218936677226416569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2790671479291118150944379 4186007218936677226416569)
          ·
            refine ⟨3139505414202507919812427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4186007218936677226416569 3139505414202507919812427)
            ·
              refine ⟨4709258121303761879718641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139505414202507919812427 4709258121303761879718641)
              ·
                refine ⟨3531943590977821409788981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4709258121303761879718641 3531943590977821409788981)
                ·
                  refine ⟨331119711654170757167717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3531943590977821409788981 331119711654170757167717)
                  ·
                    refine ⟨62084945935157016968947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 331119711654170757167717 62084945935157016968947)
                    ·
                      rfl

theorem cell23_362730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_362730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362730 prefixEnd_362730 := by exact prefixLift 362730
  have htrace : WordTrace (prefixWord ++ tailWord_362730) baseStart_362730 baseEnd_362730 := by
    simpa [prefixWord, tailWord_362730, baseEnd_362730] using wordTrace_append hprefix tailTrace_362730
  have hstable : (prefixWord ++ tailWord_362730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362730).length < 2 ^ (prefixWord ++ tailWord_362730).sum := by decide
  have hdescent : baseEnd_362730 < baseStart_362730 := by decide
  rcases family_descends (prefixWord ++ tailWord_362730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362750 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_362750 : Nat := 118140960795 + 362750 * 2 ^ 59
def prefixEnd_362750 : Nat := 4983230072969 + 3 ^ 40 * 362750 * 2
def baseEnd_362750 : Nat := 186265107418560972656749

theorem tailTrace_362750 : CollatzResearch.WordTrace tailWord_362750 prefixEnd_362750 186265107418560972656749 := by
  unfold tailWord_362750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653822429478272201599713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8820386290550785075198469 1653822429478272201599713)
  ·
    refine ⟨1240366822108704151199785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1653822429478272201599713 1240366822108704151199785)
    ·
      refine ⟨930275116581528113399839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1240366822108704151199785 930275116581528113399839)
      ·
        refine ⟨1395412674872292170099759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930275116581528113399839 1395412674872292170099759)
        ·
          refine ⟨2093119012308438255149639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1395412674872292170099759 2093119012308438255149639)
          ·
            refine ⟨3139678518462657382724459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093119012308438255149639 3139678518462657382724459)
            ·
              refine ⟨4709517777693986074086689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139678518462657382724459 4709517777693986074086689)
              ·
                refine ⟨3532138333270489555565017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4709517777693986074086689 3532138333270489555565017)
                ·
                  refine ⟨2649103749952867166673763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3532138333270489555565017 2649103749952867166673763)
                  ·
                    refine ⟨3973655624929300750010645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2649103749952867166673763 3973655624929300750010645)
                    ·
                      refine ⟨186265107418560972656749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3973655624929300750010645 186265107418560972656749)
                      ·
                        rfl

theorem cell23_362750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_362750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362750 prefixEnd_362750 := by exact prefixLift 362750
  have htrace : WordTrace (prefixWord ++ tailWord_362750) baseStart_362750 baseEnd_362750 := by
    simpa [prefixWord, tailWord_362750, baseEnd_362750] using wordTrace_append hprefix tailTrace_362750
  have hstable : (prefixWord ++ tailWord_362750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362750).length < 2 ^ (prefixWord ++ tailWord_362750).sum := by decide
  have hdescent : baseEnd_362750 < baseStart_362750 := by decide
  rcases family_descends (prefixWord ++ tailWord_362750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362754 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_362754 : Nat := 118140960795 + 362754 * 2 ^ 59
def prefixEnd_362754 : Nat := 4983230072969 + 3 ^ 40 * 362754 * 2
def baseEnd_362754 : Nat := 186267161341178957006731

theorem tailTrace_362754 : CollatzResearch.WordTrace tailWord_362754 prefixEnd_362754 186267161341178957006731 := by
  unfold tailWord_362754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307681331952921573985829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8820483551874457530628877 3307681331952921573985829)
  ·
    refine ⟨620190249741172795122343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3307681331952921573985829 620190249741172795122343)
    ·
      refine ⟨930285374611759192683515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620190249741172795122343 930285374611759192683515)
      ·
        refine ⟨1395428061917638789025273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930285374611759192683515 1395428061917638789025273)
        ·
          refine ⟨1046571046438229091768955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1395428061917638789025273 1046571046438229091768955)
          ·
            refine ⟨1569856569657343637653433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046571046438229091768955 1569856569657343637653433)
            ·
              refine ⟨1177392427243007728240075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569856569657343637653433 1177392427243007728240075)
              ·
                refine ⟨1766088640864511592360113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177392427243007728240075 1766088640864511592360113)
                ·
                  refine ⟨1324566480648383694270085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1766088640864511592360113 1324566480648383694270085)
                  ·
                    refine ⟨248356215121571942675641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1324566480648383694270085 248356215121571942675641)
                    ·
                      refine ⟨186267161341178957006731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 248356215121571942675641 186267161341178957006731)
                      ·
                        rfl

theorem cell23_362754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_362754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362754 prefixEnd_362754 := by exact prefixLift 362754
  have htrace : WordTrace (prefixWord ++ tailWord_362754) baseStart_362754 baseEnd_362754 := by
    simpa [prefixWord, tailWord_362754, baseEnd_362754] using wordTrace_append hprefix tailTrace_362754
  have hstable : (prefixWord ++ tailWord_362754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362754).length < 2 ^ (prefixWord ++ tailWord_362754).sum := by decide
  have hdescent : baseEnd_362754 < baseStart_362754 := by decide
  rcases family_descends (prefixWord ++ tailWord_362754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362763 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 6]
def baseStart_362763 : Nat := 118140960795 + 362763 * 2 ^ 59
def prefixEnd_362763 : Nat := 4983230072969 + 3 ^ 40 * 362763 * 2
def baseEnd_362763 : Nat := 186271782667069421794189

theorem tailTrace_362763 : CollatzResearch.WordTrace tailWord_362763 prefixEnd_362763 186271782667069421794189 := by
  unfold tailWord_362763
  simp only [CollatzResearch.WordTrace]
  refine ⟨13231053584779080833020943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8820702389852720555347295 13231053584779080833020943)
  ·
    refine ⟨19846580377168621249531415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13231053584779080833020943 19846580377168621249531415)
    ·
      refine ⟨29769870565752931874297123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19846580377168621249531415 29769870565752931874297123)
      ·
        refine ⟨44654805848629397811445685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29769870565752931874297123 44654805848629397811445685)
        ·
          refine ⟨4186388048309006044823033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44654805848629397811445685 4186388048309006044823033)
          ·
            refine ⟨3139791036231754533617275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4186388048309006044823033 3139791036231754533617275)
            ·
              refine ⟨4709686554347631800425913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139791036231754533617275 4709686554347631800425913)
              ·
                refine ⟨3532264915760723850319435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4709686554347631800425913 3532264915760723850319435)
                ·
                  refine ⟨5298397373641085775479153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3532264915760723850319435 5298397373641085775479153)
                  ·
                    refine ⟨3973798030230814331609365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5298397373641085775479153 3973798030230814331609365)
                    ·
                      refine ⟨186271782667069421794189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3973798030230814331609365 186271782667069421794189)
                      ·
                        rfl

theorem cell23_362763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_362763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362763 prefixEnd_362763 := by exact prefixLift 362763
  have htrace : WordTrace (prefixWord ++ tailWord_362763) baseStart_362763 baseEnd_362763 := by
    simpa [prefixWord, tailWord_362763, baseEnd_362763] using wordTrace_append hprefix tailTrace_362763
  have hstable : (prefixWord ++ tailWord_362763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362763).length < 2 ^ (prefixWord ++ tailWord_362763).sum := by decide
  have hdescent : baseEnd_362763 < baseStart_362763 := by decide
  rcases family_descends (prefixWord ++ tailWord_362763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362798 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_362798 : Nat := 118140960795 + 362798 * 2 ^ 59
def prefixEnd_362798 : Nat := 4983230072969 + 3 ^ 40 * 362798 * 2
def baseEnd_362798 : Nat := 62096584829992261618843

theorem tailTrace_362798 : CollatzResearch.WordTrace tailWord_362798 prefixEnd_362798 62096584829992261618843 := by
  unfold tailWord_362798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654041267456535226318131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8821553426434854540363365 1654041267456535226318131)
  ·
    refine ⟨2481061901184802839477197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1654041267456535226318131 2481061901184802839477197)
    ·
      refine ⟨930398212944301064803949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2481061901184802839477197 930398212944301064803949)
      ·
        refine ⟨348899329854112899301481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 930398212944301064803949 348899329854112899301481)
        ·
          refine ⟨261674497390584674476111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348899329854112899301481 261674497390584674476111)
          ·
            refine ⟨392511746085877011714167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261674497390584674476111 392511746085877011714167)
            ·
              refine ⟨588767619128815517571251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392511746085877011714167 588767619128815517571251)
              ·
                refine ⟨883151428693223276356877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588767619128815517571251 883151428693223276356877)
                ·
                  refine ⟨331181785759958728633829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883151428693223276356877 331181785759958728633829)
                  ·
                    refine ⟨62096584829992261618843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 331181785759958728633829 62096584829992261618843)
                    ·
                      rfl

theorem cell23_362798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_362798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362798 prefixEnd_362798 := by exact prefixLift 362798
  have htrace : WordTrace (prefixWord ++ tailWord_362798) baseStart_362798 baseEnd_362798 := by
    simpa [prefixWord, tailWord_362798, baseEnd_362798] using wordTrace_append hprefix tailTrace_362798
  have hstable : (prefixWord ++ tailWord_362798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362798).length < 2 ^ (prefixWord ++ tailWord_362798).sum := by decide
  have hdescent : baseEnd_362798 < baseStart_362798 := by decide
  rcases family_descends (prefixWord ++ tailWord_362798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362837 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 1, 6]
def baseStart_362837 : Nat := 118140960795 + 362837 * 2 ^ 59
def prefixEnd_362837 : Nat := 4983230072969 + 3 ^ 40 * 362837 * 2
def baseEnd_362837 : Nat := 62103260078500710756283

theorem tailTrace_362837 : CollatzResearch.WordTrace tailWord_362837 prefixEnd_362837 62103260078500710756283 := by
  unfold tailWord_362837
  simp only [CollatzResearch.WordTrace]
  refine ⟨13233752586510991471214765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8822501724340660980809843 13233752586510991471214765)
  ·
    refine ⟨4962657219941621801705537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13233752586510991471214765 4962657219941621801705537)
    ·
      refine ⟨3721992914956216351279153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4962657219941621801705537 3721992914956216351279153)
      ·
        refine ⟨2791494686217162263459365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3721992914956216351279153 2791494686217162263459365)
        ·
          refine ⟨523405253665717924398631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2791494686217162263459365 523405253665717924398631)
          ·
            refine ⟨785107880498576886597947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523405253665717924398631 785107880498576886597947)
            ·
              refine ⟨1177661820747865329896921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785107880498576886597947 1177661820747865329896921)
              ·
                refine ⟨883246365560898997422691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177661820747865329896921 883246365560898997422691)
                ·
                  refine ⟨1324869548341348496134037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883246365560898997422691 1324869548341348496134037)
                  ·
                    refine ⟨62103260078500710756283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1324869548341348496134037 62103260078500710756283)
                    ·
                      rfl

theorem cell23_362837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_362837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362837 prefixEnd_362837 := by exact prefixLift 362837
  have htrace : WordTrace (prefixWord ++ tailWord_362837) baseStart_362837 baseEnd_362837 := by
    simpa [prefixWord, tailWord_362837, baseEnd_362837] using wordTrace_append hprefix tailTrace_362837
  have hstable : (prefixWord ++ tailWord_362837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362837).length < 2 ^ (prefixWord ++ tailWord_362837).sum := by decide
  have hdescent : baseEnd_362837 < baseStart_362837 := by decide
  rcases family_descends (prefixWord ++ tailWord_362837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362847 : List Nat := [1, 1, 2, 3, 1, 2, 2, 5, 1, 2, 3]
def baseStart_362847 : Nat := 118140960795 + 362847 * 2 ^ 59
def prefixEnd_362847 : Nat := 4983230072969 + 3 ^ 40 * 362847 * 2
def baseEnd_362847 : Nat := 186314915042047093143803

theorem tailTrace_362847 : CollatzResearch.WordTrace tailWord_362847 prefixEnd_362847 186314915042047093143803 := by
  unfold tailWord_362847
  simp only [CollatzResearch.WordTrace]
  refine ⟨13234117316474763179078795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8822744877649842119385863 13234117316474763179078795)
  ·
    refine ⟨19851175974712144768618193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13234117316474763179078795 19851175974712144768618193)
    ·
      refine ⟨14888381981034108576463645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19851175974712144768618193 14888381981034108576463645)
      ·
        refine ⟨5583143242887790716173867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14888381981034108576463645 5583143242887790716173867)
        ·
          refine ⟨8374714864331686074260801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5583143242887790716173867 8374714864331686074260801)
          ·
            refine ⟨6281036148248764555695601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8374714864331686074260801 6281036148248764555695601)
            ·
              refine ⟨4710777111186573416771701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6281036148248764555695601 4710777111186573416771701)
              ·
                refine ⟨441635354173741257822347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4710777111186573416771701 441635354173741257822347)
                ·
                  refine ⟨662453031260611886733521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441635354173741257822347 662453031260611886733521)
                  ·
                    refine ⟨496839773445458915050141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 662453031260611886733521 496839773445458915050141)
                    ·
                      refine ⟨186314915042047093143803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 496839773445458915050141 186314915042047093143803)
                      ·
                        rfl

theorem cell23_362847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_362847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362847 prefixEnd_362847 := by exact prefixLift 362847
  have htrace : WordTrace (prefixWord ++ tailWord_362847) baseStart_362847 baseEnd_362847 := by
    simpa [prefixWord, tailWord_362847, baseEnd_362847] using wordTrace_append hprefix tailTrace_362847
  have hstable : (prefixWord ++ tailWord_362847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362847).length < 2 ^ (prefixWord ++ tailWord_362847).sum := by decide
  have hdescent : baseEnd_362847 < baseStart_362847 := by decide
  rcases family_descends (prefixWord ++ tailWord_362847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362850 : List Nat := [3, 3, 2, 1, 1, 13]
def baseStart_362850 : Nat := 118140960795 + 362850 * 2 ^ 59
def prefixEnd_362850 : Nat := 4983230072969 + 3 ^ 40 * 362850 * 2
def baseEnd_362850 : Nat := 766734384707862474923

theorem tailTrace_362850 : CollatzResearch.WordTrace tailWord_362850 prefixEnd_362850 766734384707862474923 := by
  unfold tailWord_362850
  simp only [CollatzResearch.WordTrace]
  refine ⟨3308556683865973672859501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8822817823642596460958669 3308556683865973672859501)
  ·
    refine ⟨1240708756449740127322313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3308556683865973672859501 1240708756449740127322313)
    ·
      refine ⟨930531567337305095491735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1240708756449740127322313 930531567337305095491735)
      ·
        refine ⟨1395797351005957643237603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930531567337305095491735 1395797351005957643237603)
        ·
          refine ⟨2093696026508936464856405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1395797351005957643237603 2093696026508936464856405)
          ·
            refine ⟨766734384707862474923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 2093696026508936464856405 766734384707862474923)
            ·
              rfl

theorem cell23_362850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 13].length) (baseStart_362850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362850 prefixEnd_362850 := by exact prefixLift 362850
  have htrace : WordTrace (prefixWord ++ tailWord_362850) baseStart_362850 baseEnd_362850 := by
    simpa [prefixWord, tailWord_362850, baseEnd_362850] using wordTrace_append hprefix tailTrace_362850
  have hstable : (prefixWord ++ tailWord_362850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362850).length < 2 ^ (prefixWord ++ tailWord_362850).sum := by decide
  have hdescent : baseEnd_362850 < baseStart_362850 := by decide
  rcases family_descends (prefixWord ++ tailWord_362850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362877 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_362877 : Nat := 118140960795 + 362877 * 2 ^ 59
def prefixEnd_362877 : Nat := 4983230072969 + 3 ^ 40 * 362877 * 2
def baseEnd_362877 : Nat := 186330319461681975768665

theorem tailTrace_362877 : CollatzResearch.WordTrace tailWord_362877 prefixEnd_362877 186330319461681975768665 := by
  unfold tailWord_362877
  simp only [CollatzResearch.WordTrace]
  refine ⟨13235211506366078302670885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8823474337577385535113923 13235211506366078302670885)
  ·
    refine ⟨2481602157443639681750791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13235211506366078302670885 2481602157443639681750791)
    ·
      refine ⟨3722403236165459522626187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2481602157443639681750791 3722403236165459522626187)
      ·
        refine ⟨5583604854248189283939281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3722403236165459522626187 5583604854248189283939281)
        ·
          refine ⟨4187703640686141962954461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5583604854248189283939281 4187703640686141962954461)
          ·
            refine ⟨1570388865257303236107923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4187703640686141962954461 1570388865257303236107923)
            ·
              refine ⟨2355583297885954854161885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570388865257303236107923 2355583297885954854161885)
              ·
                refine ⟨883343736707233070310707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2355583297885954854161885 883343736707233070310707)
                ·
                  refine ⟨1325015605060849605466061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883343736707233070310707 1325015605060849605466061)
                  ·
                    refine ⟨496880851897818602049773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1325015605060849605466061 496880851897818602049773)
                    ·
                      refine ⟨186330319461681975768665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 496880851897818602049773 186330319461681975768665)
                      ·
                        rfl

theorem cell23_362877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_362877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362877 prefixEnd_362877 := by exact prefixLift 362877
  have htrace : WordTrace (prefixWord ++ tailWord_362877) baseStart_362877 baseEnd_362877 := by
    simpa [prefixWord, tailWord_362877, baseEnd_362877] using wordTrace_append hprefix tailTrace_362877
  have hstable : (prefixWord ++ tailWord_362877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362877).length < 2 ^ (prefixWord ++ tailWord_362877).sum := by decide
  have hdescent : baseEnd_362877 < baseStart_362877 := by decide
  rcases family_descends (prefixWord ++ tailWord_362877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362894 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_362894 : Nat := 118140960795 + 362894 * 2 ^ 59
def prefixEnd_362894 : Nat := 4983230072969 + 3 ^ 40 * 362894 * 2
def baseEnd_362894 : Nat := 186339048632808409256087

theorem tailTrace_362894 : CollatzResearch.WordTrace tailWord_362894 prefixEnd_362894 186339048632808409256087 := by
  unfold tailWord_362894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654478943413061275754967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8823887698202993470693157 1654478943413061275754967)
  ·
    refine ⟨2481718415119591913632451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1654478943413061275754967 2481718415119591913632451)
    ·
      refine ⟨3722577622679387870448677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2481718415119591913632451 3722577622679387870448677)
      ·
        refine ⟨697983304252385225709127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3722577622679387870448677 697983304252385225709127)
        ·
          refine ⟨1046974956378577838563691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697983304252385225709127 1046974956378577838563691)
          ·
            refine ⟨1570462434567866757845537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046974956378577838563691 1570462434567866757845537)
            ·
              refine ⟨1177846825925900068384153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1570462434567866757845537 1177846825925900068384153)
              ·
                refine ⟨883385119444425051288115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177846825925900068384153 883385119444425051288115)
                ·
                  refine ⟨1325077679166637576932173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883385119444425051288115 1325077679166637576932173)
                  ·
                    refine ⟨496904129687489091349565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1325077679166637576932173 496904129687489091349565)
                    ·
                      refine ⟨186339048632808409256087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 496904129687489091349565 186339048632808409256087)
                      ·
                        rfl

theorem cell23_362894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_362894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_362894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_362894 prefixEnd_362894 := by exact prefixLift 362894
  have htrace : WordTrace (prefixWord ++ tailWord_362894) baseStart_362894 baseEnd_362894 := by
    simpa [prefixWord, tailWord_362894, baseEnd_362894] using wordTrace_append hprefix tailTrace_362894
  have hstable : (prefixWord ++ tailWord_362894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362894).length < 2 ^ (prefixWord ++ tailWord_362894).sum := by decide
  have hdescent : baseEnd_362894 < baseStart_362894 := by decide
  rcases family_descends (prefixWord ++ tailWord_362894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363017 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 7, 4]
def baseStart_363017 : Nat := 118140960795 + 363017 * 2 ^ 59
def prefixEnd_363017 : Nat := 4983230072969 + 3 ^ 40 * 363017 * 2
def baseEnd_363017 : Nat := 62134068917770476006007

theorem tailTrace_363017 : CollatzResearch.WordTrace tailWord_363017 prefixEnd_363017 62134068917770476006007 := by
  unfold tailWord_363017
  simp only [CollatzResearch.WordTrace]
  refine ⟨13240317725858882212767305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8826878483905921475178203 13240317725858882212767305)
  ·
    refine ⟨9930238294394161659575479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13240317725858882212767305 9930238294394161659575479)
    ·
      refine ⟨14895357441591242489363219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9930238294394161659575479 14895357441591242489363219)
      ·
        refine ⟨22343036162386863734044829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14895357441591242489363219 22343036162386863734044829)
        ·
          refine ⟨8378638560895073900266811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22343036162386863734044829 8378638560895073900266811)
          ·
            refine ⟨12567957841342610850400217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8378638560895073900266811 12567957841342610850400217)
            ·
              refine ⟨9425968381006958137800163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12567957841342610850400217 9425968381006958137800163)
              ·
                refine ⟨14138952571510437206700245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9425968381006958137800163 14138952571510437206700245)
                ·
                  refine ⟨331381700894775872032037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14138952571510437206700245 331381700894775872032037)
                  ·
                    refine ⟨62134068917770476006007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 331381700894775872032037 62134068917770476006007)
                    ·
                      rfl

theorem cell23_363017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 4].length) (baseStart_363017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363017 prefixEnd_363017 := by exact prefixLift 363017
  have htrace : WordTrace (prefixWord ++ tailWord_363017) baseStart_363017 baseEnd_363017 := by
    simpa [prefixWord, tailWord_363017, baseEnd_363017] using wordTrace_append hprefix tailTrace_363017
  have hstable : (prefixWord ++ tailWord_363017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363017).length < 2 ^ (prefixWord ++ tailWord_363017).sum := by decide
  have hdescent : baseEnd_363017 < baseStart_363017 := by decide
  rcases family_descends (prefixWord ++ tailWord_363017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363068 : List Nat := [2, 2, 2, 2, 3, 2, 2, 3, 1, 4]
def baseStart_363068 : Nat := 118140960795 + 363068 * 2 ^ 59
def prefixEnd_363068 : Nat := 4983230072969 + 3 ^ 40 * 363068 * 2
def baseEnd_363068 : Nat := 62142798088896909493429

theorem tailTrace_363068 : CollatzResearch.WordTrace tailWord_363068 prefixEnd_363068 62142798088896909493429 := by
  unfold tailWord_363068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6621088924337058961436929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8828118565782745281915905 6621088924337058961436929)
  ·
    refine ⟨4965816693252794221077697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6621088924337058961436929 4965816693252794221077697)
    ·
      refine ⟨3724362519939595665808273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4965816693252794221077697 3724362519939595665808273)
      ·
        refine ⟨2793271889954696749356205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3724362519939595665808273 2793271889954696749356205)
        ·
          refine ⟨1047476958733011281008577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2793271889954696749356205 1047476958733011281008577)
          ·
            refine ⟨785607719049758460756433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1047476958733011281008577 785607719049758460756433)
            ·
              refine ⟨589205789287318845567325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785607719049758460756433 589205789287318845567325)
              ·
                refine ⟨220952170982744567087747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 589205789287318845567325 220952170982744567087747)
                ·
                  refine ⟨331428256474116850631621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220952170982744567087747 331428256474116850631621)
                  ·
                    refine ⟨62142798088896909493429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 331428256474116850631621 62142798088896909493429)
                    ·
                      rfl

theorem cell23_363068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_363068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363068 prefixEnd_363068 := by exact prefixLift 363068
  have htrace : WordTrace (prefixWord ++ tailWord_363068) baseStart_363068 baseEnd_363068 := by
    simpa [prefixWord, tailWord_363068, baseEnd_363068] using wordTrace_append hprefix tailTrace_363068
  have hstable : (prefixWord ++ tailWord_363068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363068).length < 2 ^ (prefixWord ++ tailWord_363068).sum := by decide
  have hdescent : baseEnd_363068 < baseStart_363068 := by decide
  rcases family_descends (prefixWord ++ tailWord_363068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363154 : List Nat := [3, 2, 3, 1, 2, 1, 1, 10]
def baseStart_363154 : Nat := 118140960795 + 363154 * 2 ^ 59
def prefixEnd_363154 : Nat := 4983230072969 + 3 ^ 40 * 363154 * 2
def baseEnd_363154 : Nat := 6906390874184347852033

theorem tailTrace_363154 : CollatzResearch.WordTrace tailWord_363154 prefixEnd_363154 6906390874184347852033 := by
  unfold tailWord_363154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311328631590638652626129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8830209684241703073669677 3311328631590638652626129)
  ·
    refine ⟨2483496473692978989469597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3311328631590638652626129 2483496473692978989469597)
    ·
      refine ⟨931311177634867121051099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2483496473692978989469597 931311177634867121051099)
      ·
        refine ⟨1396966766452300681576649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931311177634867121051099 1396966766452300681576649)
        ·
          refine ⟨1047725074839225511182487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1396966766452300681576649 1047725074839225511182487)
          ·
            refine ⟨1571587612258838266773731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047725074839225511182487 1571587612258838266773731)
            ·
              refine ⟨2357381418388257400160597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571587612258838266773731 2357381418388257400160597)
              ·
                refine ⟨6906390874184347852033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2357381418388257400160597 6906390874184347852033)
                ·
                  rfl

theorem cell23_363154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 10].length) (baseStart_363154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363154 prefixEnd_363154 := by exact prefixLift 363154
  have htrace : WordTrace (prefixWord ++ tailWord_363154) baseStart_363154 baseEnd_363154 := by
    simpa [prefixWord, tailWord_363154, baseEnd_363154] using wordTrace_append hprefix tailTrace_363154
  have hstable : (prefixWord ++ tailWord_363154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363154).length < 2 ^ (prefixWord ++ tailWord_363154).sum := by decide
  have hdescent : baseEnd_363154 < baseStart_363154 := by decide
  rcases family_descends (prefixWord ++ tailWord_363154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363181 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_363181 : Nat := 118140960795 + 363181 * 2 ^ 59
def prefixEnd_363181 : Nat := 4983230072969 + 3 ^ 40 * 363181 * 2
def baseEnd_363181 : Nat := 186486417580648786367267

theorem tailTrace_363181 : CollatzResearch.WordTrace tailWord_363181 prefixEnd_363181 186486417580648786367267 := by
  unfold tailWord_363181
  simp only [CollatzResearch.WordTrace]
  refine ⟨13246299297264738221737397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8830866198176492147824931 13246299297264738221737397)
  ·
    refine ⟨1241840559118569208287881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13246299297264738221737397 1241840559118569208287881)
    ·
      refine ⟨931380419338926906215911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1241840559118569208287881 931380419338926906215911)
      ·
        refine ⟨1397070629008390359323867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931380419338926906215911 1397070629008390359323867)
        ·
          refine ⟨2095605943512585538985801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397070629008390359323867 2095605943512585538985801)
          ·
            refine ⟨1571704457634439154239351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2095605943512585538985801 1571704457634439154239351)
            ·
              refine ⟨2357556686451658731359027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571704457634439154239351 2357556686451658731359027)
              ·
                refine ⟨3536335029677488097038541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357556686451658731359027 3536335029677488097038541)
                ·
                  refine ⟨1326125636129058036389453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3536335029677488097038541 1326125636129058036389453)
                  ·
                    refine ⟨497297113548396763646045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1326125636129058036389453 497297113548396763646045)
                    ·
                      refine ⟨186486417580648786367267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 497297113548396763646045 186486417580648786367267)
                      ·
                        rfl

theorem cell23_363181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_363181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363181 prefixEnd_363181 := by exact prefixLift 363181
  have htrace : WordTrace (prefixWord ++ tailWord_363181) baseStart_363181 baseEnd_363181 := by
    simpa [prefixWord, tailWord_363181, baseEnd_363181] using wordTrace_append hprefix tailTrace_363181
  have hstable : (prefixWord ++ tailWord_363181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363181).length < 2 ^ (prefixWord ++ tailWord_363181).sum := by decide
  have hdescent : baseEnd_363181 < baseStart_363181 := by decide
  rcases family_descends (prefixWord ++ tailWord_363181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363185 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 1, 1, 5]
def baseStart_363185 : Nat := 118140960795 + 363185 * 2 ^ 59
def prefixEnd_363185 : Nat := 4983230072969 + 3 ^ 40 * 363185 * 2
def baseEnd_363185 : Nat := 186488471503266770717249

theorem tailTrace_363185 : CollatzResearch.WordTrace tailWord_363185 prefixEnd_363185 186488471503266770717249 := by
  unfold tailWord_363185
  simp only [CollatzResearch.WordTrace]
  refine ⟨13246445189250246904883009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8830963459500164603255339 13246445189250246904883009)
  ·
    refine ⟨9934833891937685178662257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13246445189250246904883009 9934833891937685178662257)
    ·
      refine ⟨7451125418953263883996693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9934833891937685178662257 7451125418953263883996693)
      ·
        refine ⟨349271504013434244562345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7451125418953263883996693 349271504013434244562345)
        ·
          refine ⟨261953628010075683421759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349271504013434244562345 261953628010075683421759)
          ·
            refine ⟨392930442015113525132639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261953628010075683421759 392930442015113525132639)
            ·
              refine ⟨589395663022670287698959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392930442015113525132639 589395663022670287698959)
              ·
                refine ⟨884093494534005431548439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589395663022670287698959 884093494534005431548439)
                ·
                  refine ⟨1326140241801008147322659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884093494534005431548439 1326140241801008147322659)
                  ·
                    refine ⟨1989210362701512220983989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1326140241801008147322659 1989210362701512220983989)
                    ·
                      refine ⟨186488471503266770717249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1989210362701512220983989 186488471503266770717249)
                      ·
                        rfl

theorem cell23_363185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_363185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363185 prefixEnd_363185 := by exact prefixLift 363185
  have htrace : WordTrace (prefixWord ++ tailWord_363185) baseStart_363185 baseEnd_363185 := by
    simpa [prefixWord, tailWord_363185, baseEnd_363185] using wordTrace_append hprefix tailTrace_363185
  have hstable : (prefixWord ++ tailWord_363185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363185).length < 2 ^ (prefixWord ++ tailWord_363185).sum := by decide
  have hdescent : baseEnd_363185 < baseStart_363185 := by decide
  rcases family_descends (prefixWord ++ tailWord_363185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363214 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_363214 : Nat := 118140960795 + 363214 * 2 ^ 59
def prefixEnd_363214 : Nat := 4983230072969 + 3 ^ 40 * 363214 * 2
def baseEnd_363214 : Nat := 62167787480749052418205

theorem tailTrace_363214 : CollatzResearch.WordTrace tailWord_363214 prefixEnd_363214 62167787480749052418205 := by
  unfold tailWord_363214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1655937863268148107211087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8831668604096789905125797 1655937863268148107211087)
  ·
    refine ⟨2483906794902222160816631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1655937863268148107211087 2483906794902222160816631)
    ·
      refine ⟨3725860192353333241224947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2483906794902222160816631 3725860192353333241224947)
      ·
        refine ⟨5588790288529999861837421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3725860192353333241224947 5588790288529999861837421)
        ·
          refine ⟨2095796358198749948189033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5588790288529999861837421 2095796358198749948189033)
          ·
            refine ⟨1571847268649062461141775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2095796358198749948189033 1571847268649062461141775)
            ·
              refine ⟨2357770902973593691712663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571847268649062461141775 2357770902973593691712663)
              ·
                refine ⟨3536656354460390537568995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357770902973593691712663 3536656354460390537568995)
                ·
                  refine ⟨5304984531690585806353493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3536656354460390537568995 5304984531690585806353493)
                  ·
                    refine ⟨62167787480749052418205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5304984531690585806353493 62167787480749052418205)
                    ·
                      rfl

theorem cell23_363214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_363214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363214 prefixEnd_363214 := by exact prefixLift 363214
  have htrace : WordTrace (prefixWord ++ tailWord_363214) baseStart_363214 baseEnd_363214 := by
    simpa [prefixWord, tailWord_363214, baseEnd_363214] using wordTrace_append hprefix tailTrace_363214
  have hstable : (prefixWord ++ tailWord_363214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363214).length < 2 ^ (prefixWord ++ tailWord_363214).sum := by decide
  have hdescent : baseEnd_363214 < baseStart_363214 := by decide
  rcases family_descends (prefixWord ++ tailWord_363214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363261 : List Nat := [1, 4, 1, 1, 1, 1, 3, 6, 5]
def baseStart_363261 : Nat := 118140960795 + 363261 * 2 ^ 59
def prefixEnd_363261 : Nat := 4983230072969 + 3 ^ 40 * 363261 * 2
def baseEnd_363261 : Nat := 20725277337000941485211

theorem tailTrace_363261 : CollatzResearch.WordTrace tailWord_363261 prefixEnd_363261 20725277337000941485211 := by
  unfold tailWord_363261
  simp only [CollatzResearch.WordTrace]
  refine ⟨13249217136974911884649637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8832811424649941256433091 13249217136974911884649637)
  ·
    refine ⟨2484228213182795978371807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13249217136974911884649637 2484228213182795978371807)
    ·
      refine ⟨3726342319774193967557711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2484228213182795978371807 3726342319774193967557711)
      ·
        refine ⟨5589513479661290951336567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3726342319774193967557711 5589513479661290951336567)
        ·
          refine ⟨8384270219491936427004851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5589513479661290951336567 8384270219491936427004851)
          ·
            refine ⟨12576405329237904640507277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8384270219491936427004851 12576405329237904640507277)
            ·
              refine ⟨4716151998464214240190229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12576405329237904640507277 4716151998464214240190229)
              ·
                refine ⟨221069624928010042508917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4716151998464214240190229 221069624928010042508917)
                ·
                  refine ⟨20725277337000941485211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221069624928010042508917 20725277337000941485211)
                  ·
                    rfl

theorem cell23_363261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_363261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363261 prefixEnd_363261 := by exact prefixLift 363261
  have htrace : WordTrace (prefixWord ++ tailWord_363261) baseStart_363261 baseEnd_363261 := by
    simpa [prefixWord, tailWord_363261, baseEnd_363261] using wordTrace_append hprefix tailTrace_363261
  have hstable : (prefixWord ++ tailWord_363261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363261).length < 2 ^ (prefixWord ++ tailWord_363261).sum := by decide
  have hdescent : baseEnd_363261 < baseStart_363261 := by decide
  rcases family_descends (prefixWord ++ tailWord_363261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363272 : List Nat := [2, 1, 3, 2, 2, 3, 3, 1, 2, 2, 2]
def baseStart_363272 : Nat := 118140960795 + 363272 * 2 ^ 59
def prefixEnd_363272 : Nat := 4983230072969 + 3 ^ 40 * 363272 * 2
def baseEnd_363272 : Nat := 186533144320207930329349

theorem tailTrace_363272 : CollatzResearch.WordTrace tailWord_363272 prefixEnd_363272 186533144320207930329349 := by
  unfold tailWord_363272
  simp only [CollatzResearch.WordTrace]
  refine ⟨6624809169967530381650035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8833078893290040508866713 6624809169967530381650035)
  ·
    refine ⟨9937213754951295572475053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6624809169967530381650035 9937213754951295572475053)
    ·
      refine ⟨3726455158106735839678145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9937213754951295572475053 3726455158106735839678145)
      ·
        refine ⟨2794841368580051879758609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3726455158106735839678145 2794841368580051879758609)
        ·
          refine ⟨2096131026435038909818957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2794841368580051879758609 2096131026435038909818957)
          ·
            refine ⟨786049134913139591182109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2096131026435038909818957 786049134913139591182109)
            ·
              refine ⟨294768425592427346693291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 786049134913139591182109 294768425592427346693291)
              ·
                refine ⟨442152638388641020039937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294768425592427346693291 442152638388641020039937)
                ·
                  refine ⟨331614478791480765029953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442152638388641020039937 331614478791480765029953)
                  ·
                    refine ⟨248710859093610573772465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 331614478791480765029953 248710859093610573772465)
                    ·
                      refine ⟨186533144320207930329349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 248710859093610573772465 186533144320207930329349)
                      ·
                        rfl

theorem cell23_363272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_363272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363272 prefixEnd_363272 := by exact prefixLift 363272
  have htrace : WordTrace (prefixWord ++ tailWord_363272) baseStart_363272 baseEnd_363272 := by
    simpa [prefixWord, tailWord_363272, baseEnd_363272] using wordTrace_append hprefix tailTrace_363272
  have hstable : (prefixWord ++ tailWord_363272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363272).length < 2 ^ (prefixWord ++ tailWord_363272).sum := by decide
  have hdescent : baseEnd_363272 < baseStart_363272 := by decide
  rcases family_descends (prefixWord ++ tailWord_363272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363274 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 3, 7]
def baseStart_363274 : Nat := 118140960795 + 363274 * 2 ^ 59
def prefixEnd_363274 : Nat := 4983230072969 + 3 ^ 40 * 363274 * 2
def baseEnd_363274 : Nat := 62178057093838974168113

theorem tailTrace_363274 : CollatzResearch.WordTrace tailWord_363274 prefixEnd_363274 62178057093838974168113 := by
  unfold tailWord_363274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3312422821481953776218219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8833127523951876736581917 3312422821481953776218219)
  ·
    refine ⟨4968634232222930664327329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3312422821481953776218219 4968634232222930664327329)
    ·
      refine ⟨3726475674167197998245497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4968634232222930664327329 3726475674167197998245497)
      ·
        refine ⟨2794856755625398498684123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3726475674167197998245497 2794856755625398498684123)
        ·
          refine ⟨4192285133438097748026185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794856755625398498684123 4192285133438097748026185)
          ·
            refine ⟨3144213850078573311019639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4192285133438097748026185 3144213850078573311019639)
            ·
              refine ⟨4716320775117859966529459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144213850078573311019639 4716320775117859966529459)
              ·
                refine ⟨7074481162676789949794189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4716320775117859966529459 7074481162676789949794189)
                ·
                  refine ⟨2652930436003796231172821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7074481162676789949794189 2652930436003796231172821)
                  ·
                    refine ⟨62178057093838974168113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2652930436003796231172821 62178057093838974168113)
                    ·
                      rfl

theorem cell23_363274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_363274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363274 prefixEnd_363274 := by exact prefixLift 363274
  have htrace : WordTrace (prefixWord ++ tailWord_363274) baseStart_363274 baseEnd_363274 := by
    simpa [prefixWord, tailWord_363274, baseEnd_363274] using wordTrace_append hprefix tailTrace_363274
  have hstable : (prefixWord ++ tailWord_363274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363274).length < 2 ^ (prefixWord ++ tailWord_363274).sum := by decide
  have hdescent : baseEnd_363274 < baseStart_363274 := by decide
  rcases family_descends (prefixWord ++ tailWord_363274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363281 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 2, 5, 2]
def baseStart_363281 : Nat := 118140960795 + 363281 * 2 ^ 59
def prefixEnd_363281 : Nat := 4983230072969 + 3 ^ 40 * 363281 * 2
def baseEnd_363281 : Nat := 186537765646098395116807

theorem tailTrace_363281 : CollatzResearch.WordTrace tailWord_363281 prefixEnd_363281 186537765646098395116807 := by
  unfold tailWord_363281
  simp only [CollatzResearch.WordTrace]
  refine ⟨13249946596902455300377697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8833297731268303533585131 13249946596902455300377697)
  ·
    refine ⟨9937459947676841475283273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13249946596902455300377697 9937459947676841475283273)
    ·
      refine ⟨7453094960757631106462455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9937459947676841475283273 7453094960757631106462455)
      ·
        refine ⟨11179642441136446659693683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7453094960757631106462455 11179642441136446659693683)
        ·
          refine ⟨16769463661704669989540525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11179642441136446659693683 16769463661704669989540525)
          ·
            refine ⟨6288548873139251246077697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16769463661704669989540525 6288548873139251246077697)
            ·
              refine ⟨4716411654854438434558273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6288548873139251246077697 4716411654854438434558273)
              ·
                refine ⟨3537308741140828825918705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4716411654854438434558273 3537308741140828825918705)
                ·
                  refine ⟨2652981555855621619439029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3537308741140828825918705 2652981555855621619439029)
                  ·
                    refine ⟨248717020861464526822409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2652981555855621619439029 248717020861464526822409)
                    ·
                      refine ⟨186537765646098395116807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 248717020861464526822409 186537765646098395116807)
                      ·
                        rfl

theorem cell23_363281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 5, 2].length) (baseStart_363281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363281 prefixEnd_363281 := by exact prefixLift 363281
  have htrace : WordTrace (prefixWord ++ tailWord_363281) baseStart_363281 baseEnd_363281 := by
    simpa [prefixWord, tailWord_363281, baseEnd_363281] using wordTrace_append hprefix tailTrace_363281
  have hstable : (prefixWord ++ tailWord_363281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363281).length < 2 ^ (prefixWord ++ tailWord_363281).sum := by decide
  have hdescent : baseEnd_363281 < baseStart_363281 := by decide
  rcases family_descends (prefixWord ++ tailWord_363281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363331 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 3]
def baseStart_363331 : Nat := 118140960795 + 363331 * 2 ^ 59
def prefixEnd_363331 : Nat := 4983230072969 + 3 ^ 40 * 363331 * 2
def baseEnd_363331 : Nat := 186563439678823199491577

theorem tailTrace_363331 : CollatzResearch.WordTrace tailWord_363331 prefixEnd_363331 186563439678823199491577 := by
  unfold tailWord_363331
  simp only [CollatzResearch.WordTrace]
  refine ⟨13251770246721313839697847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8834513497814209226465231 13251770246721313839697847)
  ·
    refine ⟨19877655370081970759546771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13251770246721313839697847 19877655370081970759546771)
    ·
      refine ⟨29816483055122956139320157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19877655370081970759546771 29816483055122956139320157)
      ·
        refine ⟨11181181145671108552245059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29816483055122956139320157 11181181145671108552245059)
        ·
          refine ⟨16771771718506662828367589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11181181145671108552245059 16771771718506662828367589)
          ·
            refine ⟨3144707197219999280318923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16771771718506662828367589 3144707197219999280318923)
            ·
              refine ⟨4717060795829998920478385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144707197219999280318923 4717060795829998920478385)
              ·
                refine ⟨3537795596872499190358789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4717060795829998920478385 3537795596872499190358789)
                ·
                  refine ⟨663336674413593598192273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3537795596872499190358789 663336674413593598192273)
                  ·
                    refine ⟨497502505810195198644205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 663336674413593598192273 497502505810195198644205)
                    ·
                      refine ⟨186563439678823199491577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 497502505810195198644205 186563439678823199491577)
                      ·
                        rfl

theorem cell23_363331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_363331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363331 prefixEnd_363331 := by exact prefixLift 363331
  have htrace : WordTrace (prefixWord ++ tailWord_363331) baseStart_363331 baseEnd_363331 := by
    simpa [prefixWord, tailWord_363331, baseEnd_363331] using wordTrace_append hprefix tailTrace_363331
  have hstable : (prefixWord ++ tailWord_363331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363331).length < 2 ^ (prefixWord ++ tailWord_363331).sum := by decide
  have hdescent : baseEnd_363331 < baseStart_363331 := by decide
  rcases family_descends (prefixWord ++ tailWord_363331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363368 : List Nat := [2, 1, 4, 2, 1, 3, 2, 2, 6]
def baseStart_363368 : Nat := 118140960795 + 363368 * 2 ^ 59
def prefixEnd_363368 : Nat := 4983230072969 + 3 ^ 40 * 363368 * 2
def baseEnd_363368 : Nat := 20731382051448839414323

theorem tailTrace_363368 : CollatzResearch.WordTrace tailWord_363368 prefixEnd_363368 20731382051448839414323 := by
  unfold tailWord_363368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6626559873793634579397379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8835413165058179439196505 6626559873793634579397379)
  ·
    refine ⟨9939839810690451869096069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6626559873793634579397379 9939839810690451869096069)
    ·
      refine ⟨1863719964504459725455513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9939839810690451869096069 1863719964504459725455513)
      ·
        refine ⟨1397789973378344794091635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1863719964504459725455513 1397789973378344794091635)
        ·
          refine ⟨2096684960067517191137453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397789973378344794091635 2096684960067517191137453)
          ·
            refine ⟨786256860025318946676545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2096684960067517191137453 786256860025318946676545)
            ·
              refine ⟨589692645018989210007409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786256860025318946676545 589692645018989210007409)
              ·
                refine ⟨442269483764241907505557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589692645018989210007409 442269483764241907505557)
                ·
                  refine ⟨20731382051448839414323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 442269483764241907505557 20731382051448839414323)
                  ·
                    rfl

theorem cell23_363368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 6].length) (baseStart_363368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363368 prefixEnd_363368 := by exact prefixLift 363368
  have htrace : WordTrace (prefixWord ++ tailWord_363368) baseStart_363368 baseEnd_363368 := by
    simpa [prefixWord, tailWord_363368, baseEnd_363368] using wordTrace_append hprefix tailTrace_363368
  have hstable : (prefixWord ++ tailWord_363368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363368).length < 2 ^ (prefixWord ++ tailWord_363368).sum := by decide
  have hdescent : baseEnd_363368 < baseStart_363368 := by decide
  rcases family_descends (prefixWord ++ tailWord_363368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363388 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 4, 3, 2]
def baseStart_363388 : Nat := 118140960795 + 363388 * 2 ^ 59
def prefixEnd_363388 : Nat := 4983230072969 + 3 ^ 40 * 363388 * 2
def baseEnd_363388 : Nat := 186592708076129476478815

theorem tailTrace_363388 : CollatzResearch.WordTrace tailWord_363388 prefixEnd_363388 186592708076129476478815 := by
  unfold tailWord_363388
  simp only [CollatzResearch.WordTrace]
  refine ⟨6626924603757406287261409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8835899471676541716348545 6626924603757406287261409)
  ·
    refine ⟨4970193452818054715446057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6626924603757406287261409 4970193452818054715446057)
    ·
      refine ⟨3727645089613541036584543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4970193452818054715446057 3727645089613541036584543)
      ·
        refine ⟨5591467634420311554876815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3727645089613541036584543 5591467634420311554876815)
        ·
          refine ⟨8387201451630467332315223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5591467634420311554876815 8387201451630467332315223)
          ·
            refine ⟨12580802177445700998472835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8387201451630467332315223 12580802177445700998472835)
            ·
              refine ⟨18871203266168551497709253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12580802177445700998472835 18871203266168551497709253)
              ·
                refine ⟨3538350612406603405820485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18871203266168551497709253 3538350612406603405820485)
                ·
                  refine ⟨663440739826238138591341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3538350612406603405820485 663440739826238138591341)
                  ·
                    refine ⟨248790277434839301971753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 663440739826238138591341 248790277434839301971753)
                    ·
                      refine ⟨186592708076129476478815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 248790277434839301971753 186592708076129476478815)
                      ·
                        rfl

theorem cell23_363388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_363388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363388 prefixEnd_363388 := by exact prefixLift 363388
  have htrace : WordTrace (prefixWord ++ tailWord_363388) baseStart_363388 baseEnd_363388 := by
    simpa [prefixWord, tailWord_363388, baseEnd_363388] using wordTrace_append hprefix tailTrace_363388
  have hstable : (prefixWord ++ tailWord_363388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363388).length < 2 ^ (prefixWord ++ tailWord_363388).sum := by decide
  have hdescent : baseEnd_363388 < baseStart_363388 := by decide
  rcases family_descends (prefixWord ++ tailWord_363388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363428 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_363428 : Nat := 118140960795 + 363428 * 2 ^ 59
def prefixEnd_363428 : Nat := 4983230072969 + 3 ^ 40 * 363428 * 2
def baseEnd_363428 : Nat := 62204415767436439992877

theorem tailTrace_363428 : CollatzResearch.WordTrace tailWord_363428 prefixEnd_363428 62204415767436439992877 := by
  unfold tailWord_363428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6627654063684949702989469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8836872084913266270652625 6627654063684949702989469)
  ·
    refine ⟨2485370273881856138621051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6627654063684949702989469 2485370273881856138621051)
    ·
      refine ⟨3728055410822784207931577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2485370273881856138621051 3728055410822784207931577)
      ·
        refine ⟨2796041558117088155948683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3728055410822784207931577 2796041558117088155948683)
        ·
          refine ⟨4194062337175632233923025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2796041558117088155948683 4194062337175632233923025)
          ·
            refine ⟨3145546752881724175442269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4194062337175632233923025 3145546752881724175442269)
            ·
              refine ⟨1179580032330646565790851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3145546752881724175442269 1179580032330646565790851)
              ·
                refine ⟨1769370048495969848686277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179580032330646565790851 1769370048495969848686277)
                ·
                  refine ⟨331756884092994346628677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1769370048495969848686277 331756884092994346628677)
                  ·
                    refine ⟨62204415767436439992877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 331756884092994346628677 62204415767436439992877)
                    ·
                      rfl

theorem cell23_363428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_363428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363428 prefixEnd_363428 := by exact prefixLift 363428
  have htrace : WordTrace (prefixWord ++ tailWord_363428) baseStart_363428 baseEnd_363428 := by
    simpa [prefixWord, tailWord_363428, baseEnd_363428] using wordTrace_append hprefix tailTrace_363428
  have hstable : (prefixWord ++ tailWord_363428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363428).length < 2 ^ (prefixWord ++ tailWord_363428).sum := by decide
  have hdescent : baseEnd_363428 < baseStart_363428 := by decide
  rcases family_descends (prefixWord ++ tailWord_363428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363448 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 1, 2, 4]
def baseStart_363448 : Nat := 118140960795 + 363448 * 2 ^ 59
def prefixEnd_363448 : Nat := 4983230072969 + 3 ^ 40 * 363448 * 2
def baseEnd_363448 : Nat := 186623516915399241728539

theorem tailTrace_363448 : CollatzResearch.WordTrace tailWord_363448 prefixEnd_363448 186623516915399241728539 := by
  unfold tailWord_363448
  simp only [CollatzResearch.WordTrace]
  refine ⟨6628018793648721410853499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8837358391531628547804665 6628018793648721410853499)
  ·
    refine ⟨9942028190473082116280249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6628018793648721410853499 9942028190473082116280249)
    ·
      refine ⟨7456521142854811587210187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9942028190473082116280249 7456521142854811587210187)
      ·
        refine ⟨11184781714282217380815281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7456521142854811587210187 11184781714282217380815281)
        ·
          refine ⟨8388586285711663035611461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11184781714282217380815281 8388586285711663035611461)
          ·
            refine ⟨1572859928570936819177149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8388586285711663035611461 1572859928570936819177149)
            ·
              refine ⟨589822473214101307191431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1572859928570936819177149 589822473214101307191431)
              ·
                refine ⟨884733709821151960787147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589822473214101307191431 884733709821151960787147)
                ·
                  refine ⟨1327100564731727941180721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884733709821151960787147 1327100564731727941180721)
                  ·
                    refine ⟨995325423548795955885541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1327100564731727941180721 995325423548795955885541)
                    ·
                      refine ⟨186623516915399241728539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 995325423548795955885541 186623516915399241728539)
                      ·
                        rfl

theorem cell23_363448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_363448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363448 prefixEnd_363448 := by exact prefixLift 363448
  have htrace : WordTrace (prefixWord ++ tailWord_363448) baseStart_363448 baseEnd_363448 := by
    simpa [prefixWord, tailWord_363448, baseEnd_363448] using wordTrace_append hprefix tailTrace_363448
  have hstable : (prefixWord ++ tailWord_363448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363448).length < 2 ^ (prefixWord ++ tailWord_363448).sum := by decide
  have hdescent : baseEnd_363448 < baseStart_363448 := by decide
  rcases family_descends (prefixWord ++ tailWord_363448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363468 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 3, 3, 3]
def baseStart_363468 : Nat := 118140960795 + 363468 * 2 ^ 59
def prefixEnd_363468 : Nat := 4983230072969 + 3 ^ 40 * 363468 * 2
def baseEnd_363468 : Nat := 186633786528489163478447

theorem tailTrace_363468 : CollatzResearch.WordTrace tailWord_363468 prefixEnd_363468 186633786528489163478447 := by
  unfold tailWord_363468
  simp only [CollatzResearch.WordTrace]
  refine ⟨6628383523612493118717529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8837844698149990824956705 6628383523612493118717529)
  ·
    refine ⟨4971287642709369839038147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6628383523612493118717529 4971287642709369839038147)
    ·
      refine ⟨7456931464064054758557221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4971287642709369839038147 7456931464064054758557221)
      ·
        refine ⟨1398174649512010267229479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7456931464064054758557221 1398174649512010267229479)
        ·
          refine ⟨2097261974268015400844219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1398174649512010267229479 2097261974268015400844219)
          ·
            refine ⟨3145892961402023101266329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097261974268015400844219 3145892961402023101266329)
            ·
              refine ⟨2359419721051517325949747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3145892961402023101266329 2359419721051517325949747)
              ·
                refine ⟨3539129581577275988924621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359419721051517325949747 3539129581577275988924621)
                ·
                  refine ⟨1327173593091478495846733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3539129581577275988924621 1327173593091478495846733)
                  ·
                    refine ⟨497690097409304435942525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1327173593091478495846733 497690097409304435942525)
                    ·
                      refine ⟨186633786528489163478447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 497690097409304435942525 186633786528489163478447)
                      ·
                        rfl

theorem cell23_363468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_363468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363468 prefixEnd_363468 := by exact prefixLift 363468
  have htrace : WordTrace (prefixWord ++ tailWord_363468) baseStart_363468 baseEnd_363468 := by
    simpa [prefixWord, tailWord_363468, baseEnd_363468] using wordTrace_append hprefix tailTrace_363468
  have hstable : (prefixWord ++ tailWord_363468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363468).length < 2 ^ (prefixWord ++ tailWord_363468).sum := by decide
  have hdescent : baseEnd_363468 < baseStart_363468 := by decide
  rcases family_descends (prefixWord ++ tailWord_363468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363506 : List Nat := [3, 2, 1, 5, 2, 1, 1, 2, 1, 2, 3]
def baseStart_363506 : Nat := 118140960795 + 363506 * 2 ^ 59
def prefixEnd_363506 : Nat := 4983230072969 + 3 ^ 40 * 363506 * 2
def baseEnd_363506 : Nat := 186653298793360014803273

theorem tailTrace_363506 : CollatzResearch.WordTrace tailWord_363506 prefixEnd_363506 186653298793360014803273 := by
  unfold tailWord_363506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314538255271829681829593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8838768680724879151545581 3314538255271829681829593)
  ·
    refine ⟨2485903691453872261372195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3314538255271829681829593 2485903691453872261372195)
    ·
      refine ⟨3728855537180808392058293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2485903691453872261372195 3728855537180808392058293)
      ·
        refine ⟨349580206610700786755465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3728855537180808392058293 349580206610700786755465)
        ·
          refine ⟨262185154958025590066599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349580206610700786755465 262185154958025590066599)
          ·
            refine ⟨393277732437038385099899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262185154958025590066599 393277732437038385099899)
            ·
              refine ⟨589916598655557577649849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393277732437038385099899 589916598655557577649849)
              ·
                refine ⟨442437448991668183237387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589916598655557577649849 442437448991668183237387)
                ·
                  refine ⟨663656173487502274856081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442437448991668183237387 663656173487502274856081)
                  ·
                    refine ⟨497742130115626706142061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 663656173487502274856081 497742130115626706142061)
                    ·
                      refine ⟨186653298793360014803273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 497742130115626706142061 186653298793360014803273)
                      ·
                        rfl

theorem cell23_363506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_363506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363506 prefixEnd_363506 := by exact prefixLift 363506
  have htrace : WordTrace (prefixWord ++ tailWord_363506) baseStart_363506 baseEnd_363506 := by
    simpa [prefixWord, tailWord_363506, baseEnd_363506] using wordTrace_append hprefix tailTrace_363506
  have hstable : (prefixWord ++ tailWord_363506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363506).length < 2 ^ (prefixWord ++ tailWord_363506).sum := by decide
  have hdescent : baseEnd_363506 < baseStart_363506 := by decide
  rcases family_descends (prefixWord ++ tailWord_363506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363525 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 1, 4, 2]
def baseStart_363525 : Nat := 118140960795 + 363525 * 2 ^ 59
def prefixEnd_363525 : Nat := 4983230072969 + 3 ^ 40 * 363525 * 2
def baseEnd_363525 : Nat := 186663054925795440465685

theorem tailTrace_363525 : CollatzResearch.WordTrace tailWord_363525 prefixEnd_363525 186663054925795440465685 := by
  unfold tailWord_363525
  simp only [CollatzResearch.WordTrace]
  refine ⟨13258846008018484972260029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8839230672012323314840019 13258846008018484972260029)
  ·
    refine ⟨4972067253006931864597511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13258846008018484972260029 4972067253006931864597511)
    ·
      refine ⟨7458100879510397796896267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4972067253006931864597511 7458100879510397796896267)
      ·
        refine ⟨11187151319265596695344401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7458100879510397796896267 11187151319265596695344401)
        ·
          refine ⟨8390363489449197521508301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11187151319265596695344401 8390363489449197521508301)
          ·
            refine ⟨3146386308543449070565613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8390363489449197521508301 3146386308543449070565613)
            ·
              refine ⟨1179894865703793401462105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3146386308543449070565613 1179894865703793401462105)
              ·
                refine ⟨884921149277845051096579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1179894865703793401462105 884921149277845051096579)
                ·
                  refine ⟨1327381723916767576644869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884921149277845051096579 1327381723916767576644869)
                  ·
                    refine ⟨248884073234393920620913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1327381723916767576644869 248884073234393920620913)
                    ·
                      refine ⟨186663054925795440465685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 248884073234393920620913 186663054925795440465685)
                      ·
                        rfl

theorem cell23_363525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 4, 2].length) (baseStart_363525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363525 prefixEnd_363525 := by exact prefixLift 363525
  have htrace : WordTrace (prefixWord ++ tailWord_363525) baseStart_363525 baseEnd_363525 := by
    simpa [prefixWord, tailWord_363525, baseEnd_363525] using wordTrace_append hprefix tailTrace_363525
  have hstable : (prefixWord ++ tailWord_363525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363525).length < 2 ^ (prefixWord ++ tailWord_363525).sum := by decide
  have hdescent : baseEnd_363525 < baseStart_363525 := by decide
  rcases family_descends (prefixWord ++ tailWord_363525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363528 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_363528 : Nat := 118140960795 + 363528 * 2 ^ 59
def prefixEnd_363528 : Nat := 4983230072969 + 3 ^ 40 * 363528 * 2
def baseEnd_363528 : Nat := 186664595367758928728171

theorem tailTrace_363528 : CollatzResearch.WordTrace tailWord_363528 prefixEnd_363528 186664595367758928728171 := by
  unfold tailWord_363528
  simp only [CollatzResearch.WordTrace]
  refine ⟨6629477713503808242309619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8839303618005077656412825 6629477713503808242309619)
  ·
    refine ⟨9944216570255712363464429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6629477713503808242309619 9944216570255712363464429)
    ·
      refine ⟨3729081213845892136299161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9944216570255712363464429 3729081213845892136299161)
      ·
        refine ⟨2796810910384419102224371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3729081213845892136299161 2796810910384419102224371)
        ·
          refine ⟨4195216365576628653336557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2796810910384419102224371 4195216365576628653336557)
          ·
            refine ⟨1573206137091235745001209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4195216365576628653336557 1573206137091235745001209)
            ·
              refine ⟨1179904602818426808750907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1573206137091235745001209 1179904602818426808750907)
              ·
                refine ⟨1769856904227640213126361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179904602818426808750907 1769856904227640213126361)
                ·
                  refine ⟨1327392678170730159844771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1769856904227640213126361 1327392678170730159844771)
                  ·
                    refine ⟨1991089017256095239767157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1327392678170730159844771 1991089017256095239767157)
                    ·
                      refine ⟨186664595367758928728171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1991089017256095239767157 186664595367758928728171)
                      ·
                        rfl

theorem cell23_363528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_363528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363528 prefixEnd_363528 := by exact prefixLift 363528
  have htrace : WordTrace (prefixWord ++ tailWord_363528) baseStart_363528 baseEnd_363528 := by
    simpa [prefixWord, tailWord_363528, baseEnd_363528] using wordTrace_append hprefix tailTrace_363528
  have hstable : (prefixWord ++ tailWord_363528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363528).length < 2 ^ (prefixWord ++ tailWord_363528).sum := by decide
  have hdescent : baseEnd_363528 < baseStart_363528 := by decide
  rcases family_descends (prefixWord ++ tailWord_363528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363559 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_363559 : Nat := 118140960795 + 363559 * 2 ^ 59
def prefixEnd_363559 : Nat := 4983230072969 + 3 ^ 40 * 363559 * 2
def baseEnd_363559 : Nat := 186680513268048307440529

theorem tailTrace_363559 : CollatzResearch.WordTrace tailWord_363559 prefixEnd_363559 186680513268048307440529 := by
  unfold tailWord_363559
  simp only [CollatzResearch.WordTrace]
  refine ⟨13260086089895308778997731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8840057393263539185998487 13260086089895308778997731)
  ·
    refine ⟨19890129134842963168496597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13260086089895308778997731 19890129134842963168496597)
    ·
      refine ⟨466174901597881949261639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 19890129134842963168496597 466174901597881949261639)
      ·
        refine ⟨699262352396822923892459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466174901597881949261639 699262352396822923892459)
        ·
          refine ⟨1048893528595234385838689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699262352396822923892459 1048893528595234385838689)
          ·
            refine ⟨786670146446425789379017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1048893528595234385838689 786670146446425789379017)
            ·
              refine ⟨590002609834819342034263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786670146446425789379017 590002609834819342034263)
              ·
                refine ⟨885003914752229013051395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590002609834819342034263 885003914752229013051395)
                ·
                  refine ⟨1327505872128343519577093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885003914752229013051395 1327505872128343519577093)
                  ·
                    refine ⟨248907351024064409920705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1327505872128343519577093 248907351024064409920705)
                    ·
                      refine ⟨186680513268048307440529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 248907351024064409920705 186680513268048307440529)
                      ·
                        rfl

theorem cell23_363559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_363559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363559 prefixEnd_363559 := by exact prefixLift 363559
  have htrace : WordTrace (prefixWord ++ tailWord_363559) baseStart_363559 baseEnd_363559 := by
    simpa [prefixWord, tailWord_363559, baseEnd_363559] using wordTrace_append hprefix tailTrace_363559
  have hstable : (prefixWord ++ tailWord_363559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363559).length < 2 ^ (prefixWord ++ tailWord_363559).sum := by decide
  have hdescent : baseEnd_363559 < baseStart_363559 := by decide
  rcases family_descends (prefixWord ++ tailWord_363559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363582 : List Nat := [4, 2, 1, 3, 1, 1, 1, 5, 5]
def baseStart_363582 : Nat := 118140960795 + 363582 * 2 ^ 59
def prefixEnd_363582 : Nat := 4983230072969 + 3 ^ 40 * 363582 * 2
def baseEnd_363582 : Nat := 20743591480344635272547

theorem tailTrace_363582 : CollatzResearch.WordTrace tailWord_363582 prefixEnd_363582 20743591480344635272547 := by
  unfold tailWord_363582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1657615621101497963385625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8840616645874655804723333 1657615621101497963385625)
  ·
    refine ⟨1243211715826123472539219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1657615621101497963385625 1243211715826123472539219)
    ·
      refine ⟨1864817573739185208808829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1243211715826123472539219 1864817573739185208808829)
      ·
        refine ⟨699306590152194453303311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1864817573739185208808829 699306590152194453303311)
        ·
          refine ⟨1048959885228291679954967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699306590152194453303311 1048959885228291679954967)
          ·
            refine ⟨1573439827842437519932451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048959885228291679954967 1573439827842437519932451)
            ·
              refine ⟨2360159741763656279898677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573439827842437519932451 2360159741763656279898677)
              ·
                refine ⟨221264975790342776240501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2360159741763656279898677 221264975790342776240501)
                ·
                  refine ⟨20743591480344635272547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221264975790342776240501 20743591480344635272547)
                  ·
                    rfl

theorem cell23_363582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_363582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363582 prefixEnd_363582 := by exact prefixLift 363582
  have htrace : WordTrace (prefixWord ++ tailWord_363582) baseStart_363582 baseEnd_363582 := by
    simpa [prefixWord, tailWord_363582, baseEnd_363582] using wordTrace_append hprefix tailTrace_363582
  have hstable : (prefixWord ++ tailWord_363582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363582).length < 2 ^ (prefixWord ++ tailWord_363582).sum := by decide
  have hdescent : baseEnd_363582 < baseStart_363582 := by decide
  rcases family_descends (prefixWord ++ tailWord_363582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363615 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 2, 4, 2]
def baseStart_363615 : Nat := 118140960795 + 363615 * 2 ^ 59
def prefixEnd_363615 : Nat := 4983230072969 + 3 ^ 40 * 363615 * 2
def baseEnd_363615 : Nat := 186709268184700088340271

theorem tailTrace_363615 : CollatzResearch.WordTrace tailWord_363615 prefixEnd_363615 186709268184700088340271 := by
  unfold tailWord_363615
  simp only [CollatzResearch.WordTrace]
  refine ⟨13262128577692430343036299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8841419051794953562024199 13262128577692430343036299)
  ·
    refine ⟨19893192866538645514554449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13262128577692430343036299 19893192866538645514554449)
    ·
      refine ⟨14919894649903984135915837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19893192866538645514554449 14919894649903984135915837)
      ·
        refine ⟨5594960493713994050968439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14919894649903984135915837 5594960493713994050968439)
        ·
          refine ⟨8392440740570991076452659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5594960493713994050968439 8392440740570991076452659)
          ·
            refine ⟨12588661110856486614678989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8392440740570991076452659 12588661110856486614678989)
            ·
              refine ⟨4720747916571182480504621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12588661110856486614678989 4720747916571182480504621)
              ·
                refine ⟨1770280468714193430189233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4720747916571182480504621 1770280468714193430189233)
                ·
                  refine ⟨1327710351535645072641925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1770280468714193430189233 1327710351535645072641925)
                  ·
                    refine ⟨248945690912933451120361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1327710351535645072641925 248945690912933451120361)
                    ·
                      refine ⟨186709268184700088340271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 248945690912933451120361 186709268184700088340271)
                      ·
                        rfl

theorem cell23_363615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_363615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363615 prefixEnd_363615 := by exact prefixLift 363615
  have htrace : WordTrace (prefixWord ++ tailWord_363615) baseStart_363615 baseEnd_363615 := by
    simpa [prefixWord, tailWord_363615, baseEnd_363615] using wordTrace_append hprefix tailTrace_363615
  have hstable : (prefixWord ++ tailWord_363615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363615).length < 2 ^ (prefixWord ++ tailWord_363615).sum := by decide
  have hdescent : baseEnd_363615 < baseStart_363615 := by decide
  rcases family_descends (prefixWord ++ tailWord_363615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363625 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 3, 4]
def baseStart_363625 : Nat := 118140960795 + 363625 * 2 ^ 59
def prefixEnd_363625 : Nat := 4983230072969 + 3 ^ 40 * 363625 * 2
def baseEnd_363625 : Nat := 62238134330415016405075

theorem tailTrace_363625 : CollatzResearch.WordTrace tailWord_363625 prefixEnd_363625 62238134330415016405075 := by
  unfold tailWord_363625
  simp only [CollatzResearch.WordTrace]
  refine ⟨13262493307656202050900329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8841662205104134700600219 13262493307656202050900329)
  ·
    refine ⟨9946869980742151538175247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13262493307656202050900329 9946869980742151538175247)
    ·
      refine ⟨14920304971113227307262871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9946869980742151538175247 14920304971113227307262871)
      ·
        refine ⟨22380457456669840960894307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14920304971113227307262871 22380457456669840960894307)
        ·
          refine ⟨33570686185004761441341461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22380457456669840960894307 33570686185004761441341461)
          ·
            refine ⟨1573625914922098192562881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33570686185004761441341461 1573625914922098192562881)
            ·
              refine ⟨1180219436191573644422161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1573625914922098192562881 1180219436191573644422161)
              ·
                refine ⟨885164577143680233316621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180219436191573644422161 885164577143680233316621)
                ·
                  refine ⟨331936716428880087493733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885164577143680233316621 331936716428880087493733)
                  ·
                    refine ⟨62238134330415016405075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 331936716428880087493733 62238134330415016405075)
                    ·
                      rfl

theorem cell23_363625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 4].length) (baseStart_363625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363625 prefixEnd_363625 := by exact prefixLift 363625
  have htrace : WordTrace (prefixWord ++ tailWord_363625) baseStart_363625 baseEnd_363625 := by
    simpa [prefixWord, tailWord_363625, baseEnd_363625] using wordTrace_append hprefix tailTrace_363625
  have hstable : (prefixWord ++ tailWord_363625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363625).length < 2 ^ (prefixWord ++ tailWord_363625).sum := by decide
  have hdescent : baseEnd_363625 < baseStart_363625 := by decide
  rcases family_descends (prefixWord ++ tailWord_363625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363628 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_363628 : Nat := 118140960795 + 363628 * 2 ^ 59
def prefixEnd_363628 : Nat := 4983230072969 + 3 ^ 40 * 363628 * 2
def baseEnd_363628 : Nat := 186715943433208537477711

theorem tailTrace_363628 : CollatzResearch.WordTrace tailWord_363628 prefixEnd_363628 186715943433208537477711 := by
  unfold tailWord_363628
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631301363322666781629769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8841735151096889042173025 6631301363322666781629769)
  ·
    refine ⟨4973476022492000086222327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6631301363322666781629769 4973476022492000086222327)
    ·
      refine ⟨7460214033738000129333491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4973476022492000086222327 7460214033738000129333491)
      ·
        refine ⟨11190321050607000194000237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7460214033738000129333491 11190321050607000194000237)
        ·
          refine ⟨4196370393977625072750089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11190321050607000194000237 4196370393977625072750089)
          ·
            refine ⟨3147277795483218804562567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4196370393977625072750089 3147277795483218804562567)
            ·
              refine ⟨4720916693224828206843851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3147277795483218804562567 4720916693224828206843851)
              ·
                refine ⟨7081375039837242310265777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4720916693224828206843851 7081375039837242310265777)
                ·
                  refine ⟨5311031279877931732699333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7081375039837242310265777 5311031279877931732699333)
                  ·
                    refine ⟨995818364977112199881125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5311031279877931732699333 995818364977112199881125)
                    ·
                      refine ⟨186715943433208537477711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 995818364977112199881125 186715943433208537477711)
                      ·
                        rfl

theorem cell23_363628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_363628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363628 prefixEnd_363628 := by exact prefixLift 363628
  have htrace : WordTrace (prefixWord ++ tailWord_363628) baseStart_363628 baseEnd_363628 := by
    simpa [prefixWord, tailWord_363628, baseEnd_363628] using wordTrace_append hprefix tailTrace_363628
  have hstable : (prefixWord ++ tailWord_363628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363628).length < 2 ^ (prefixWord ++ tailWord_363628).sum := by decide
  have hdescent : baseEnd_363628 < baseStart_363628 := by decide
  rcases family_descends (prefixWord ++ tailWord_363628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363646 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_363646 : Nat := 118140960795 + 363646 * 2 ^ 59
def prefixEnd_363646 : Nat := 4983230072969 + 3 ^ 40 * 363646 * 2
def baseEnd_363646 : Nat := 62241728694996489017543

theorem tailTrace_363646 : CollatzResearch.WordTrace tailWord_363646 prefixEnd_363646 62241728694996489017543 := by
  unfold tailWord_363646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1657907405072515329676849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8842172827053415091609861 1657907405072515329676849)
  ·
    refine ⟨1243430553804386497257637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1657907405072515329676849 1243430553804386497257637)
    ·
      refine ⟨233143228838322468235807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1243430553804386497257637 233143228838322468235807)
      ·
        refine ⟨349714843257483702353711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233143228838322468235807 349714843257483702353711)
        ·
          refine ⟨524572264886225553530567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349714843257483702353711 524572264886225553530567)
          ·
            refine ⟨786858397329338330295851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524572264886225553530567 786858397329338330295851)
            ·
              refine ⟨1180287595994007495443777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786858397329338330295851 1180287595994007495443777)
              ·
                refine ⟨885215696995505621582833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180287595994007495443777 885215696995505621582833)
                ·
                  refine ⟨663911772746629216187125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 885215696995505621582833 663911772746629216187125)
                  ·
                    refine ⟨62241728694996489017543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 663911772746629216187125 62241728694996489017543)
                    ·
                      rfl

theorem cell23_363646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_363646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363646 prefixEnd_363646 := by exact prefixLift 363646
  have htrace : WordTrace (prefixWord ++ tailWord_363646) baseStart_363646 baseEnd_363646 := by
    simpa [prefixWord, tailWord_363646, baseEnd_363646] using wordTrace_append hprefix tailTrace_363646
  have hstable : (prefixWord ++ tailWord_363646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363646).length < 2 ^ (prefixWord ++ tailWord_363646).sum := by decide
  have hdescent : baseEnd_363646 < baseStart_363646 := by decide
  rcases family_descends (prefixWord ++ tailWord_363646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363652 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_363652 : Nat := 118140960795 + 363652 * 2 ^ 59
def prefixEnd_363652 : Nat := 4983230072969 + 3 ^ 40 * 363652 * 2
def baseEnd_363652 : Nat := 186728266968916443577601

theorem tailTrace_363652 : CollatzResearch.WordTrace tailWord_363652 prefixEnd_363652 186728266968916443577601 := by
  unfold tailWord_363652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631739039279192831066605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8842318719038923774755473 6631739039279192831066605)
  ·
    refine ⟨2486902139729697311649977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6631739039279192831066605 2486902139729697311649977)
    ·
      refine ⟨1865176604797272983737483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2486902139729697311649977 1865176604797272983737483)
      ·
        refine ⟨2797764907195909475606225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1865176604797272983737483 2797764907195909475606225)
        ·
          refine ⟨2098323680396932106704669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2797764907195909475606225 2098323680396932106704669)
          ·
            refine ⟨786871380148849540014251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2098323680396932106704669 786871380148849540014251)
            ·
              refine ⟨1180307070223274310021377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786871380148849540014251 1180307070223274310021377)
              ·
                refine ⟨885230302667455732516033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180307070223274310021377 885230302667455732516033)
                ·
                  refine ⟨663922727000591799387025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 885230302667455732516033 663922727000591799387025)
                  ·
                    refine ⟨497942045250443849540269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 663922727000591799387025 497942045250443849540269)
                    ·
                      refine ⟨186728266968916443577601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 497942045250443849540269 186728266968916443577601)
                      ·
                        rfl

theorem cell23_363652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_363652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363652 prefixEnd_363652 := by exact prefixLift 363652
  have htrace : WordTrace (prefixWord ++ tailWord_363652) baseStart_363652 baseEnd_363652 := by
    simpa [prefixWord, tailWord_363652, baseEnd_363652] using wordTrace_append hprefix tailTrace_363652
  have hstable : (prefixWord ++ tailWord_363652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363652).length < 2 ^ (prefixWord ++ tailWord_363652).sum := by decide
  have hdescent : baseEnd_363652 < baseStart_363652 := by decide
  rcases family_descends (prefixWord ++ tailWord_363652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363672 : List Nat := [2, 1, 2, 4, 2, 1, 4, 1, 6]
def baseStart_363672 : Nat := 118140960795 + 363672 * 2 ^ 59
def prefixEnd_363672 : Nat := 4983230072969 + 3 ^ 40 * 363672 * 2
def baseEnd_363672 : Nat := 20748726286889596147501

theorem tailTrace_363672 : CollatzResearch.WordTrace tailWord_363672 prefixEnd_363672 20748726286889596147501 := by
  unfold tailWord_363672
  simp only [CollatzResearch.WordTrace]
  refine ⟨6632103769242964538930635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8842805025657286051907513 6632103769242964538930635)
  ·
    refine ⟨9948155653864446808395953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6632103769242964538930635 9948155653864446808395953)
    ·
      refine ⟨7461116740398335106296965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9948155653864446808395953 7461116740398335106296965)
      ·
        refine ⟨1398959388824687832430681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7461116740398335106296965 1398959388824687832430681)
        ·
          refine ⟨1049219541618515874323011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1398959388824687832430681 1049219541618515874323011)
          ·
            refine ⟨1573829312427773811484517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049219541618515874323011 1573829312427773811484517)
            ·
              refine ⟨295092996080207589653347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1573829312427773811484517 295092996080207589653347)
              ·
                refine ⟨442639494120311384480021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295092996080207589653347 442639494120311384480021)
                ·
                  refine ⟨20748726286889596147501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 442639494120311384480021 20748726286889596147501)
                  ·
                    rfl

theorem cell23_363672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 6].length) (baseStart_363672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363672 prefixEnd_363672 := by exact prefixLift 363672
  have htrace : WordTrace (prefixWord ++ tailWord_363672) baseStart_363672 baseEnd_363672 := by
    simpa [prefixWord, tailWord_363672, baseEnd_363672] using wordTrace_append hprefix tailTrace_363672
  have hstable : (prefixWord ++ tailWord_363672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363672).length < 2 ^ (prefixWord ++ tailWord_363672).sum := by decide
  have hdescent : baseEnd_363672 < baseStart_363672 := by decide
  rcases family_descends (prefixWord ++ tailWord_363672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363685 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 3, 5]
def baseStart_363685 : Nat := 118140960795 + 363685 * 2 ^ 59
def prefixEnd_363685 : Nat := 4983230072969 + 3 ^ 40 * 363685 * 2
def baseEnd_363685 : Nat := 62248403943504938154983

theorem tailTrace_363685 : CollatzResearch.WordTrace tailWord_363685 prefixEnd_363685 62248403943504938154983 := by
  unfold tailWord_363685
  simp only [CollatzResearch.WordTrace]
  refine ⟨13264681687438832298084509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8843121124959221532056339 13264681687438832298084509)
  ·
    refine ⟨4974255632789562111781691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13264681687438832298084509 4974255632789562111781691)
    ·
      refine ⟨7461383449184343167672537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4974255632789562111781691 7461383449184343167672537)
      ·
        refine ⟨5596037586888257375754403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7461383449184343167672537 5596037586888257375754403)
        ·
          refine ⟨8394056380332386063631605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5596037586888257375754403 8394056380332386063631605)
          ·
            refine ⟨786942785656161193465463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8394056380332386063631605 786942785656161193465463)
            ·
              refine ⟨1180414178484241790198195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786942785656161193465463 1180414178484241790198195)
              ·
                refine ⟨1770621267726362685297293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1180414178484241790198195 1770621267726362685297293)
                ·
                  refine ⟨663982975397386006986485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1770621267726362685297293 663982975397386006986485)
                  ·
                    refine ⟨62248403943504938154983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 663982975397386006986485 62248403943504938154983)
                    ·
                      rfl

theorem cell23_363685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_363685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363685 prefixEnd_363685 := by exact prefixLift 363685
  have htrace : WordTrace (prefixWord ++ tailWord_363685) baseStart_363685 baseEnd_363685 := by
    simpa [prefixWord, tailWord_363685, baseEnd_363685] using wordTrace_append hprefix tailTrace_363685
  have hstable : (prefixWord ++ tailWord_363685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363685).length < 2 ^ (prefixWord ++ tailWord_363685).sum := by decide
  have hdescent : baseEnd_363685 < baseStart_363685 := by decide
  rcases family_descends (prefixWord ++ tailWord_363685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363735 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_363735 : Nat := 118140960795 + 363735 * 2 ^ 59
def prefixEnd_363735 : Nat := 4983230072969 + 3 ^ 40 * 363735 * 2
def baseEnd_363735 : Nat := 186770885863239618839719

theorem tailTrace_363735 : CollatzResearch.WordTrace tailWord_363735 prefixEnd_363735 186770885863239618839719 := by
  unfold tailWord_363735
  simp only [CollatzResearch.WordTrace]
  refine ⟨13266505337257690837404659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8844336891505127224936439 13266505337257690837404659)
  ·
    refine ⟨19899758005886536256106989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13266505337257690837404659 19899758005886536256106989)
    ·
      refine ⟨7462409252207451096040121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19899758005886536256106989 7462409252207451096040121)
      ·
        refine ⟨5596806939155588322030091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7462409252207451096040121 5596806939155588322030091)
        ·
          refine ⟨8395210408733382483045137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5596806939155588322030091 8395210408733382483045137)
          ·
            refine ⟨6296407806550036862283853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8395210408733382483045137 6296407806550036862283853)
            ·
              refine ⟨2361152927456263823356445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6296407806550036862283853 2361152927456263823356445)
              ·
                refine ⟨885432347796098933758667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2361152927456263823356445 885432347796098933758667)
                ·
                  refine ⟨1328148521694148400638001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885432347796098933758667 1328148521694148400638001)
                  ·
                    refine ⟨996111391270611300478501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1328148521694148400638001 996111391270611300478501)
                    ·
                      refine ⟨186770885863239618839719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 996111391270611300478501 186770885863239618839719)
                      ·
                        rfl

theorem cell23_363735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_363735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363735 prefixEnd_363735 := by exact prefixLift 363735
  have htrace : WordTrace (prefixWord ++ tailWord_363735) baseStart_363735 baseEnd_363735 := by
    simpa [prefixWord, tailWord_363735, baseEnd_363735] using wordTrace_append hprefix tailTrace_363735
  have hstable : (prefixWord ++ tailWord_363735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363735).length < 2 ^ (prefixWord ++ tailWord_363735).sum := by decide
  have hdescent : baseEnd_363735 < baseStart_363735 := by decide
  rcases family_descends (prefixWord ++ tailWord_363735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363756 : List Nat := [2, 2, 1, 1, 2, 4, 1, 5, 1, 2, 2]
def baseStart_363756 : Nat := 118140960795 + 363756 * 2 ^ 59
def prefixEnd_363756 : Nat := 4983230072969 + 3 ^ 40 * 363756 * 2
def baseEnd_363756 : Nat := 186781668956984036677123

theorem tailTrace_363756 : CollatzResearch.WordTrace tailWord_363756 prefixEnd_363756 186781668956984036677123 := by
  unfold tailWord_363756
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633635635090805711959561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8844847513454407615946081 6633635635090805711959561)
  ·
    refine ⟨4975226726318104283969671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6633635635090805711959561 4975226726318104283969671)
    ·
      refine ⟨7462840089477156425954507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4975226726318104283969671 7462840089477156425954507)
      ·
        refine ⟨11194260134215734638931761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7462840089477156425954507 11194260134215734638931761)
        ·
          refine ⟨8395695100661800979198821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11194260134215734638931761 8395695100661800979198821)
          ·
            refine ⟨1574192831374087683599779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8395695100661800979198821 1574192831374087683599779)
            ·
              refine ⟨2361289247061131525399669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1574192831374087683599779 2361289247061131525399669)
              ·
                refine ⟨221370866911981080506219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2361289247061131525399669 221370866911981080506219)
                ·
                  refine ⟨332056300367971620759329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221370866911981080506219 332056300367971620759329)
                  ·
                    refine ⟨249042225275978715569497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 332056300367971620759329 249042225275978715569497)
                    ·
                      refine ⟨186781668956984036677123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249042225275978715569497 186781668956984036677123)
                      ·
                        rfl

theorem cell23_363756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 1, 2, 2].length) (baseStart_363756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363756 prefixEnd_363756 := by exact prefixLift 363756
  have htrace : WordTrace (prefixWord ++ tailWord_363756) baseStart_363756 baseEnd_363756 := by
    simpa [prefixWord, tailWord_363756, baseEnd_363756] using wordTrace_append hprefix tailTrace_363756
  have hstable : (prefixWord ++ tailWord_363756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363756).length < 2 ^ (prefixWord ++ tailWord_363756).sum := by decide
  have hdescent : baseEnd_363756 < baseStart_363756 := by decide
  rcases family_descends (prefixWord ++ tailWord_363756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363759 : List Nat := [1, 1, 2, 1, 7, 1, 1, 3, 1, 2, 3]
def baseStart_363759 : Nat := 118140960795 + 363759 * 2 ^ 59
def prefixEnd_363759 : Nat := 4983230072969 + 3 ^ 40 * 363759 * 2
def baseEnd_363759 : Nat := 186783209398947524939609

theorem tailTrace_363759 : CollatzResearch.WordTrace tailWord_363759 prefixEnd_363759 186783209398947524939609 := by
  unfold tailWord_363759
  simp only [CollatzResearch.WordTrace]
  refine ⟨13267380689170742936278331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8844920459447161957518887 13267380689170742936278331)
  ·
    refine ⟨19901071033756114404417497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13267380689170742936278331 19901071033756114404417497)
    ·
      refine ⟨14925803275317085803313123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19901071033756114404417497 14925803275317085803313123)
      ·
        refine ⟨22388704912975628704969685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14925803275317085803313123 22388704912975628704969685)
        ·
          refine ⟨524735271397866297772727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 22388704912975628704969685 524735271397866297772727)
          ·
            refine ⟨787102907096799446659091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524735271397866297772727 787102907096799446659091)
            ·
              refine ⟨1180654360645199169988637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787102907096799446659091 1180654360645199169988637)
              ·
                refine ⟨442745385241949688745739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1180654360645199169988637 442745385241949688745739)
                ·
                  refine ⟨664118077862924533118609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442745385241949688745739 664118077862924533118609)
                  ·
                    refine ⟨498088558397193399838957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 664118077862924533118609 498088558397193399838957)
                    ·
                      refine ⟨186783209398947524939609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 498088558397193399838957 186783209398947524939609)
                      ·
                        rfl

theorem cell23_363759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 2, 3].length) (baseStart_363759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363759 prefixEnd_363759 := by exact prefixLift 363759
  have htrace : WordTrace (prefixWord ++ tailWord_363759) baseStart_363759 baseEnd_363759 := by
    simpa [prefixWord, tailWord_363759, baseEnd_363759] using wordTrace_append hprefix tailTrace_363759
  have hstable : (prefixWord ++ tailWord_363759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363759).length < 2 ^ (prefixWord ++ tailWord_363759).sum := by decide
  have hdescent : baseEnd_363759 < baseStart_363759 := by decide
  rcases family_descends (prefixWord ++ tailWord_363759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363816 : List Nat := [2, 1, 5, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_363816 : Nat := 118140960795 + 363816 * 2 ^ 59
def prefixEnd_363816 : Nat := 4983230072969 + 3 ^ 40 * 363816 * 2
def baseEnd_363816 : Nat := 186812477796253801926847

theorem tailTrace_363816 : CollatzResearch.WordTrace tailWord_363816 prefixEnd_363816 186812477796253801926847 := by
  unfold tailWord_363816
  simp only [CollatzResearch.WordTrace]
  refine ⟨6634729824982120835551651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8846306433309494447402201 6634729824982120835551651)
  ·
    refine ⟨9952094737473181253327477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6634729824982120835551651 9952094737473181253327477)
    ·
      refine ⟨933008881638110742499451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9952094737473181253327477 933008881638110742499451)
      ·
        refine ⟨1399513322457166113749177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933008881638110742499451 1399513322457166113749177)
        ·
          refine ⟨1049634991842874585311883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1399513322457166113749177 1049634991842874585311883)
          ·
            refine ⟨1574452487764311877967825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049634991842874585311883 1574452487764311877967825)
            ·
              refine ⟨1180839365823233908475869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1574452487764311877967825 1180839365823233908475869)
              ·
                refine ⟨442814762183712715678451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1180839365823233908475869 442814762183712715678451)
                ·
                  refine ⟨664222143275569073517677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442814762183712715678451 664222143275569073517677)
                  ·
                    refine ⟨249083303728338402569129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 664222143275569073517677 249083303728338402569129)
                    ·
                      refine ⟨186812477796253801926847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249083303728338402569129 186812477796253801926847)
                      ·
                        rfl

theorem cell23_363816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_363816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363816 prefixEnd_363816 := by exact prefixLift 363816
  have htrace : WordTrace (prefixWord ++ tailWord_363816) baseStart_363816 baseEnd_363816 := by
    simpa [prefixWord, tailWord_363816, baseEnd_363816] using wordTrace_append hprefix tailTrace_363816
  have hstable : (prefixWord ++ tailWord_363816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363816).length < 2 ^ (prefixWord ++ tailWord_363816).sum := by decide
  have hdescent : baseEnd_363816 < baseStart_363816 := by decide
  rcases family_descends (prefixWord ++ tailWord_363816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363865 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 1, 7]
def baseStart_363865 : Nat := 118140960795 + 363865 * 2 ^ 59
def prefixEnd_363865 : Nat := 4983230072969 + 3 ^ 40 * 363865 * 2
def baseEnd_363865 : Nat := 62279212782774703404707

theorem tailTrace_363865 : CollatzResearch.WordTrace tailWord_363865 prefixEnd_363865 62279212782774703404707 := by
  unfold tailWord_363865
  simp only [CollatzResearch.WordTrace]
  refine ⟨13271246826786723039637049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8847497884524482026424699 13271246826786723039637049)
  ·
    refine ⟨9953435120090042279727787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13271246826786723039637049 9953435120090042279727787)
    ·
      refine ⟨14930152680135063419591681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9953435120090042279727787 14930152680135063419591681)
      ·
        refine ⟨11197614510101297564693761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14930152680135063419591681 11197614510101297564693761)
        ·
          refine ⟨8398210882575973173520321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11197614510101297564693761 8398210882575973173520321)
          ·
            refine ⟨6298658161931979880140241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8398210882575973173520321 6298658161931979880140241)
            ·
              refine ⟨4723993621448984910105181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6298658161931979880140241 4723993621448984910105181)
              ·
                refine ⟨1771497608043369341289443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4723993621448984910105181 1771497608043369341289443)
                ·
                  refine ⟨2657246412065054011934165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771497608043369341289443 2657246412065054011934165)
                  ·
                    refine ⟨62279212782774703404707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2657246412065054011934165 62279212782774703404707)
                    ·
                      rfl

theorem cell23_363865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_363865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363865 prefixEnd_363865 := by exact prefixLift 363865
  have htrace : WordTrace (prefixWord ++ tailWord_363865) baseStart_363865 baseEnd_363865 := by
    simpa [prefixWord, tailWord_363865, baseEnd_363865] using wordTrace_append hprefix tailTrace_363865
  have hstable : (prefixWord ++ tailWord_363865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363865).length < 2 ^ (prefixWord ++ tailWord_363865).sum := by decide
  have hdescent : baseEnd_363865 < baseStart_363865 := by decide
  rcases family_descends (prefixWord ++ tailWord_363865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363959 : List Nat := [1, 1, 3, 1, 3, 2, 5, 1, 6]
def baseStart_363959 : Nat := 118140960795 + 363959 * 2 ^ 59
def prefixEnd_363959 : Nat := 4983230072969 + 3 ^ 40 * 363959 * 2
def baseEnd_363959 : Nat := 20765100614427415826521

theorem tailTrace_363959 : CollatzResearch.WordTrace tailWord_363959 prefixEnd_363959 20765100614427415826521 := by
  unfold tailWord_363959
  simp only [CollatzResearch.WordTrace]
  refine ⟨13274675288446177093558931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8849783525630784729039287 13274675288446177093558931)
  ·
    refine ⟨19912012932669265640338397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13274675288446177093558931 19912012932669265640338397)
    ·
      refine ⟨7467004849750974615126899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19912012932669265640338397 7467004849750974615126899)
      ·
        refine ⟨11200507274626461922690349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7467004849750974615126899 11200507274626461922690349)
        ·
          refine ⟨4200190227984923221008881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11200507274626461922690349 4200190227984923221008881)
          ·
            refine ⟨3150142670988692415756661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4200190227984923221008881 3150142670988692415756661)
            ·
              refine ⟨295325875405189913977187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3150142670988692415756661 295325875405189913977187)
              ·
                refine ⟨442988813107784870965781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295325875405189913977187 442988813107784870965781)
                ·
                  refine ⟨20765100614427415826521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 442988813107784870965781 20765100614427415826521)
                  ·
                    rfl

theorem cell23_363959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 6].length) (baseStart_363959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363959 prefixEnd_363959 := by exact prefixLift 363959
  have htrace : WordTrace (prefixWord ++ tailWord_363959) baseStart_363959 baseEnd_363959 := by
    simpa [prefixWord, tailWord_363959, baseEnd_363959] using wordTrace_append hprefix tailTrace_363959
  have hstable : (prefixWord ++ tailWord_363959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363959).length < 2 ^ (prefixWord ++ tailWord_363959).sum := by decide
  have hdescent : baseEnd_363959 < baseStart_363959 := by decide
  rcases family_descends (prefixWord ++ tailWord_363959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363979 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 1, 5, 2]
def baseStart_363979 : Nat := 118140960795 + 363979 * 2 ^ 59
def prefixEnd_363979 : Nat := 4983230072969 + 3 ^ 40 * 363979 * 2
def baseEnd_363979 : Nat := 186896175142936664188597

theorem tailTrace_363979 : CollatzResearch.WordTrace tailWord_363979 prefixEnd_363979 186896175142936664188597 := by
  unfold tailWord_363979
  simp only [CollatzResearch.WordTrace]
  refine ⟨13275404748373720509286991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8850269832249147006191327 13275404748373720509286991)
  ·
    refine ⟨19913107122560580763930487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13275404748373720509286991 19913107122560580763930487)
    ·
      refine ⟨29869660683840871145895731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19913107122560580763930487 29869660683840871145895731)
      ·
        refine ⟨44804491025761306718843597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29869660683840871145895731 44804491025761306718843597)
        ·
          refine ⟨16801684134660490019566349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44804491025761306718843597 16801684134660490019566349)
          ·
            refine ⟨6300631550497683757337381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16801684134660490019566349 6300631550497683757337381)
            ·
              refine ⟨1181368415718315704500759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6300631550497683757337381 1181368415718315704500759)
              ·
                refine ⟨1772052623577473556751139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181368415718315704500759 1772052623577473556751139)
                ·
                  refine ⟨2658078935366210335126709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772052623577473556751139 2658078935366210335126709)
                  ·
                    refine ⟨249194900190582218918129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2658078935366210335126709 249194900190582218918129)
                    ·
                      refine ⟨186896175142936664188597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249194900190582218918129 186896175142936664188597)
                      ·
                        rfl

theorem cell23_363979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 5, 2].length) (baseStart_363979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363979 prefixEnd_363979 := by exact prefixLift 363979
  have htrace : WordTrace (prefixWord ++ tailWord_363979) baseStart_363979 baseEnd_363979 := by
    simpa [prefixWord, tailWord_363979, baseEnd_363979] using wordTrace_append hprefix tailTrace_363979
  have hstable : (prefixWord ++ tailWord_363979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363979).length < 2 ^ (prefixWord ++ tailWord_363979).sum := by decide
  have hdescent : baseEnd_363979 < baseStart_363979 := by decide
  rcases family_descends (prefixWord ++ tailWord_363979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363989 : List Nat := [1, 3, 2, 3, 1, 1, 1, 5, 1, 5]
def baseStart_363989 : Nat := 118140960795 + 363989 * 2 ^ 59
def prefixEnd_363989 : Nat := 4983230072969 + 3 ^ 40 * 363989 * 2
def baseEnd_363989 : Nat := 62300436649827208354517

theorem tailTrace_363989 : CollatzResearch.WordTrace tailWord_363989 prefixEnd_363989 62300436649827208354517 := by
  unfold tailWord_363989
  simp only [CollatzResearch.WordTrace]
  refine ⟨13275769478337492217151021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8850512985558328144767347 13275769478337492217151021)
  ·
    refine ⟨4978413554376559581431633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13275769478337492217151021 4978413554376559581431633)
    ·
      refine ⟨3733810165782419686073725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4978413554376559581431633 3733810165782419686073725)
      ·
        refine ⟨1400178812168407382277647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3733810165782419686073725 1400178812168407382277647)
        ·
          refine ⟨2100268218252611073416471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400178812168407382277647 2100268218252611073416471)
          ·
            refine ⟨3150402327378916610124707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100268218252611073416471 3150402327378916610124707)
            ·
              refine ⟨4725603491068374915187061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3150402327378916610124707 4725603491068374915187061)
              ·
                refine ⟨443025327287660148298787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4725603491068374915187061 443025327287660148298787)
                ·
                  refine ⟨664537990931490222448181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443025327287660148298787 664537990931490222448181)
                  ·
                    refine ⟨62300436649827208354517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 664537990931490222448181 62300436649827208354517)
                    ·
                      rfl

theorem cell23_363989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_363989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_363989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_363989 prefixEnd_363989 := by exact prefixLift 363989
  have htrace : WordTrace (prefixWord ++ tailWord_363989) baseStart_363989 baseEnd_363989 := by
    simpa [prefixWord, tailWord_363989, baseEnd_363989] using wordTrace_append hprefix tailTrace_363989
  have hstable : (prefixWord ++ tailWord_363989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363989).length < 2 ^ (prefixWord ++ tailWord_363989).sum := by decide
  have hdescent : baseEnd_363989 < baseStart_363989 := by decide
  rcases family_descends (prefixWord ++ tailWord_363989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364003 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 3, 1, 3]
def baseStart_364003 : Nat := 118140960795 + 364003 * 2 ^ 59
def prefixEnd_364003 : Nat := 4983230072969 + 3 ^ 40 * 364003 * 2
def baseEnd_364003 : Nat := 186908498678644570288487

theorem tailTrace_364003 : CollatzResearch.WordTrace tailWord_364003 prefixEnd_364003 186908498678644570288487 := by
  unfold tailWord_364003
  simp only [CollatzResearch.WordTrace]
  refine ⟨13276280100286772608160663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8850853400191181738773775 13276280100286772608160663)
  ·
    refine ⟨19914420150430158912240995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13276280100286772608160663 19914420150430158912240995)
    ·
      refine ⟨29871630225645238368361493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19914420150430158912240995 29871630225645238368361493)
      ·
        refine ⟨1400232666827120548516945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29871630225645238368361493 1400232666827120548516945)
        ·
          refine ⟨1050174500120340411387709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1400232666827120548516945 1050174500120340411387709)
          ·
            refine ⟨393815437545127654270391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1050174500120340411387709 393815437545127654270391)
            ·
              refine ⟨590723156317691481405587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393815437545127654270391 590723156317691481405587)
              ·
                refine ⟨886084734476537222108381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590723156317691481405587 886084734476537222108381)
                ·
                  refine ⟨332281775428701458290643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886084734476537222108381 332281775428701458290643)
                  ·
                    refine ⟨498422663143052187435965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 332281775428701458290643 498422663143052187435965)
                    ·
                      refine ⟨186908498678644570288487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 498422663143052187435965 186908498678644570288487)
                      ·
                        rfl

theorem cell23_364003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_364003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364003 prefixEnd_364003 := by exact prefixLift 364003
  have htrace : WordTrace (prefixWord ++ tailWord_364003) baseStart_364003 baseEnd_364003 := by
    simpa [prefixWord, tailWord_364003, baseEnd_364003] using wordTrace_append hprefix tailTrace_364003
  have hstable : (prefixWord ++ tailWord_364003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364003).length < 2 ^ (prefixWord ++ tailWord_364003).sum := by decide
  have hdescent : baseEnd_364003 < baseStart_364003 := by decide
  rcases family_descends (prefixWord ++ tailWord_364003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364012 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_364012 : Nat := 118140960795 + 364012 * 2 ^ 59
def prefixEnd_364012 : Nat := 4983230072969 + 3 ^ 40 * 364012 * 2
def baseEnd_364012 : Nat := 186913120004535035075945

theorem tailTrace_364012 : CollatzResearch.WordTrace tailWord_364012 prefixEnd_364012 186913120004535035075945 := by
  unfold tailWord_364012
  simp only [CollatzResearch.WordTrace]
  refine ⟨6638304178627083572619145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8851072238169444763492193 6638304178627083572619145)
  ·
    refine ⟨4978728133970312679464359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6638304178627083572619145 4978728133970312679464359)
    ·
      refine ⟨7468092200955469019196539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4978728133970312679464359 7468092200955469019196539)
      ·
        refine ⟨11202138301433203528794809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7468092200955469019196539 11202138301433203528794809)
        ·
          refine ⟨8401603726074902646596107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11202138301433203528794809 8401603726074902646596107)
          ·
            refine ⟨12602405589112353969894161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8401603726074902646596107 12602405589112353969894161)
            ·
              refine ⟨9451804191834265477420621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12602405589112353969894161 9451804191834265477420621)
              ·
                refine ⟨3544426571937849554032733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9451804191834265477420621 3544426571937849554032733)
                ·
                  refine ⟨1329159964476693582762275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3544426571937849554032733 1329159964476693582762275)
                  ·
                    refine ⟨1993739946715040374143413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1329159964476693582762275 1993739946715040374143413)
                    ·
                      refine ⟨186913120004535035075945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1993739946715040374143413 186913120004535035075945)
                      ·
                        rfl

theorem cell23_364012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_364012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364012 prefixEnd_364012 := by exact prefixLift 364012
  have htrace : WordTrace (prefixWord ++ tailWord_364012) baseStart_364012 baseEnd_364012 := by
    simpa [prefixWord, tailWord_364012, baseEnd_364012] using wordTrace_append hprefix tailTrace_364012
  have hstable : (prefixWord ++ tailWord_364012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364012).length < 2 ^ (prefixWord ++ tailWord_364012).sum := by decide
  have hdescent : baseEnd_364012 < baseStart_364012 := by decide
  rcases family_descends (prefixWord ++ tailWord_364012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364026 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2]
def baseStart_364026 : Nat := 118140960795 + 364026 * 2 ^ 59
def prefixEnd_364026 : Nat := 4983230072969 + 3 ^ 40 * 364026 * 2
def baseEnd_364026 : Nat := 186920308733697980300881

theorem tailTrace_364026 : CollatzResearch.WordTrace tailWord_364026 prefixEnd_364026 186920308733697980300881 := by
  unfold tailWord_364026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3319279744800861884061983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8851412652802298357498621 3319279744800861884061983)
  ·
    refine ⟨4978919617201292826092975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3319279744800861884061983 4978919617201292826092975)
    ·
      refine ⟨7468379425801939239139463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4978919617201292826092975 7468379425801939239139463)
      ·
        refine ⟨11202569138702908858709195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7468379425801939239139463 11202569138702908858709195)
        ·
          refine ⟨16803853708054363288063793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11202569138702908858709195 16803853708054363288063793)
          ·
            refine ⟨12602890281040772466047845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16803853708054363288063793 12602890281040772466047845)
            ·
              refine ⟨2363041927695144837383971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12602890281040772466047845 2363041927695144837383971)
              ·
                refine ⟨3544562891542717256075957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363041927695144837383971 3544562891542717256075957)
                ·
                  refine ⟨332302771082129742757121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3544562891542717256075957 332302771082129742757121)
                  ·
                    refine ⟨249227078311597307067841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 332302771082129742757121 249227078311597307067841)
                    ·
                      refine ⟨186920308733697980300881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249227078311597307067841 186920308733697980300881)
                      ·
                        rfl

theorem cell23_364026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2].length) (baseStart_364026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364026 prefixEnd_364026 := by exact prefixLift 364026
  have htrace : WordTrace (prefixWord ++ tailWord_364026) baseStart_364026 baseEnd_364026 := by
    simpa [prefixWord, tailWord_364026, baseEnd_364026] using wordTrace_append hprefix tailTrace_364026
  have hstable : (prefixWord ++ tailWord_364026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364026).length < 2 ^ (prefixWord ++ tailWord_364026).sum := by decide
  have hdescent : baseEnd_364026 < baseStart_364026 := by decide
  rcases family_descends (prefixWord ++ tailWord_364026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364036 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_364036 : Nat := 118140960795 + 364036 * 2 ^ 59
def prefixEnd_364036 : Nat := 4983230072969 + 3 ^ 40 * 364036 * 2
def baseEnd_364036 : Nat := 62308481180080980391945

theorem tailTrace_364036 : CollatzResearch.WordTrace tailWord_364036 prefixEnd_364036 62308481180080980391945 := by
  unfold tailWord_364036
  simp only [CollatzResearch.WordTrace]
  refine ⟨6638741854583609622055981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8851655806111479496074641 6638741854583609622055981)
  ·
    refine ⟨2489528195468853608270993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6638741854583609622055981 2489528195468853608270993)
    ·
      refine ⟨1867146146601640206203245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2489528195468853608270993 1867146146601640206203245)
      ·
        refine ⟨700179804975615077326217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1867146146601640206203245 700179804975615077326217)
        ·
          refine ⟨525134853731711307994663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 700179804975615077326217 525134853731711307994663)
          ·
            refine ⟨787702280597566961991995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525134853731711307994663 787702280597566961991995)
            ·
              refine ⟨1181553420896350442987993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787702280597566961991995 1181553420896350442987993)
              ·
                refine ⟨886165065672262832240995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1181553420896350442987993 886165065672262832240995)
                ·
                  refine ⟨1329247598508394248361493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886165065672262832240995 1329247598508394248361493)
                  ·
                    refine ⟨62308481180080980391945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1329247598508394248361493 62308481180080980391945)
                    ·
                      rfl

theorem cell23_364036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_364036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364036 prefixEnd_364036 := by exact prefixLift 364036
  have htrace : WordTrace (prefixWord ++ tailWord_364036) baseStart_364036 baseEnd_364036 := by
    simpa [prefixWord, tailWord_364036, baseEnd_364036] using wordTrace_append hprefix tailTrace_364036
  have hstable : (prefixWord ++ tailWord_364036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364036).length < 2 ^ (prefixWord ++ tailWord_364036).sum := by decide
  have hdescent : baseEnd_364036 < baseStart_364036 := by decide
  rcases family_descends (prefixWord ++ tailWord_364036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364039 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_364039 : Nat := 118140960795 + 364039 * 2 ^ 59
def prefixEnd_364039 : Nat := 4983230072969 + 3 ^ 40 * 364039 * 2
def baseEnd_364039 : Nat := 186926983982206429438321

theorem tailTrace_364039 : CollatzResearch.WordTrace tailWord_364039 prefixEnd_364039 186926983982206429438321 := by
  unfold tailWord_364039
  simp only [CollatzResearch.WordTrace]
  refine ⟨13277593128156350756471171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8851728752104233837647447 13277593128156350756471171)
  ·
    refine ⟨19916389692234526134706757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13277593128156350756471171 19916389692234526134706757)
    ·
      refine ⟨3734323067293973650257517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19916389692234526134706757 3734323067293973650257517)
      ·
        refine ⟨1400371150235240118846569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3734323067293973650257517 1400371150235240118846569)
        ·
          refine ⟨1050278362676430089134927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1400371150235240118846569 1050278362676430089134927)
          ·
            refine ⟨1575417544014645133702391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050278362676430089134927 1575417544014645133702391)
            ·
              refine ⟨2363126316021967700553587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575417544014645133702391 2363126316021967700553587)
              ·
                refine ⟨3544689474032951550830381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363126316021967700553587 3544689474032951550830381)
                ·
                  refine ⟨1329258552762356831561393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3544689474032951550830381 1329258552762356831561393)
                  ·
                    refine ⟨996943914571767623671045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1329258552762356831561393 996943914571767623671045)
                    ·
                      refine ⟨186926983982206429438321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 996943914571767623671045 186926983982206429438321)
                      ·
                        rfl

theorem cell23_364039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_364039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364039 prefixEnd_364039 := by exact prefixLift 364039
  have htrace : WordTrace (prefixWord ++ tailWord_364039) baseStart_364039 baseEnd_364039 := by
    simpa [prefixWord, tailWord_364039, baseEnd_364039] using wordTrace_append hprefix tailTrace_364039
  have hstable : (prefixWord ++ tailWord_364039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364039).length < 2 ^ (prefixWord ++ tailWord_364039).sum := by decide
  have hdescent : baseEnd_364039 < baseStart_364039 := by decide
  rcases family_descends (prefixWord ++ tailWord_364039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364043 : List Nat := [1, 1, 1, 1, 8, 1, 3, 1, 1, 1, 4]
def baseStart_364043 : Nat := 118140960795 + 364043 * 2 ^ 59
def prefixEnd_364043 : Nat := 4983230072969 + 3 ^ 40 * 364043 * 2
def baseEnd_364043 : Nat := 186929037904824413788303

theorem tailTrace_364043 : CollatzResearch.WordTrace tailWord_364043 prefixEnd_364043 186929037904824413788303 := by
  unfold tailWord_364043
  simp only [CollatzResearch.WordTrace]
  refine ⟨13277739020141859439616783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8851826013427906293077855 13277739020141859439616783)
  ·
    refine ⟨19916608530212789159425175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13277739020141859439616783 19916608530212789159425175)
    ·
      refine ⟨29874912795319183739137763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19916608530212789159425175 29874912795319183739137763)
      ·
        refine ⟨44812369192978775608706645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29874912795319183739137763 44812369192978775608706645)
        ·
          refine ⟨525144951480220026664531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 44812369192978775608706645 525144951480220026664531)
          ·
            refine ⟨787717427220330039996797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525144951480220026664531 787717427220330039996797)
            ·
              refine ⟨295394035207623764998799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 787717427220330039996797 295394035207623764998799)
              ·
                refine ⟨443091052811435647498199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295394035207623764998799 443091052811435647498199)
                ·
                  refine ⟨664636579217153471247299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443091052811435647498199 664636579217153471247299)
                  ·
                    refine ⟨996954868825730206870949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 664636579217153471247299 996954868825730206870949)
                    ·
                      refine ⟨186929037904824413788303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 996954868825730206870949 186929037904824413788303)
                      ·
                        rfl

theorem cell23_364043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 1, 1, 4].length) (baseStart_364043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364043 prefixEnd_364043 := by exact prefixLift 364043
  have htrace : WordTrace (prefixWord ++ tailWord_364043) baseStart_364043 baseEnd_364043 := by
    simpa [prefixWord, tailWord_364043, baseEnd_364043] using wordTrace_append hprefix tailTrace_364043
  have hstable : (prefixWord ++ tailWord_364043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364043).length < 2 ^ (prefixWord ++ tailWord_364043).sum := by decide
  have hdescent : baseEnd_364043 < baseStart_364043 := by decide
  rcases family_descends (prefixWord ++ tailWord_364043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364060 : List Nat := [2, 2, 3, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_364060 : Nat := 118140960795 + 364060 * 2 ^ 59
def prefixEnd_364060 : Nat := 4983230072969 + 3 ^ 40 * 364060 * 2
def baseEnd_364060 : Nat := 186937767075950847275725

theorem tailTrace_364060 : CollatzResearch.WordTrace tailWord_364060 prefixEnd_364060 186937767075950847275725 := by
  unfold tailWord_364060
  simp only [CollatzResearch.WordTrace]
  refine ⟨6639179530540135671492817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8852239374053514228657089 6639179530540135671492817)
  ·
    refine ⟨4979384647905101753619613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6639179530540135671492817 4979384647905101753619613)
    ·
      refine ⟨1867269242964413157607355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4979384647905101753619613 1867269242964413157607355)
      ·
        refine ⟨2800903864446619736411033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1867269242964413157607355 2800903864446619736411033)
        ·
          refine ⟨2100677898334964802308275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2800903864446619736411033 2100677898334964802308275)
          ·
            refine ⟨3151016847502447203462413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100677898334964802308275 3151016847502447203462413)
            ·
              refine ⟨1181631317813417701298405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3151016847502447203462413 1181631317813417701298405)
              ·
                refine ⟨221555872090015818993451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1181631317813417701298405 221555872090015818993451)
                ·
                  refine ⟨332333808135023728490177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221555872090015818993451 332333808135023728490177)
                  ·
                    refine ⟨249250356101267796367633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 332333808135023728490177 249250356101267796367633)
                    ·
                      refine ⟨186937767075950847275725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249250356101267796367633 186937767075950847275725)
                      ·
                        rfl

theorem cell23_364060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_364060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364060 prefixEnd_364060 := by exact prefixLift 364060
  have htrace : WordTrace (prefixWord ++ tailWord_364060) baseStart_364060 baseEnd_364060 := by
    simpa [prefixWord, tailWord_364060, baseEnd_364060] using wordTrace_append hprefix tailTrace_364060
  have hstable : (prefixWord ++ tailWord_364060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364060).length < 2 ^ (prefixWord ++ tailWord_364060).sum := by decide
  have hdescent : baseEnd_364060 < baseStart_364060 := by decide
  rcases family_descends (prefixWord ++ tailWord_364060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364129 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_364129 : Nat := 118140960795 + 364129 * 2 ^ 59
def prefixEnd_364129 : Nat := 4983230072969 + 3 ^ 40 * 364129 * 2
def baseEnd_364129 : Nat := 186973197241111077312907

theorem tailTrace_364129 : CollatzResearch.WordTrace tailWord_364129 prefixEnd_364129 186973197241111077312907 := by
  unfold tailWord_364129
  simp only [CollatzResearch.WordTrace]
  refine ⟨13280875697830296127247441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8853917131886864084831627 13280875697830296127247441)
  ·
    refine ⟨9960656773372722095435581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13280875697830296127247441 9960656773372722095435581)
    ·
      refine ⟨3735246290014770785788343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9960656773372722095435581 3735246290014770785788343)
      ·
        refine ⟨5602869435022156178682515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3735246290014770785788343 5602869435022156178682515)
        ·
          refine ⟨8404304152533234268023773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5602869435022156178682515 8404304152533234268023773)
          ·
            refine ⟨3151614057199962850508915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8404304152533234268023773 3151614057199962850508915)
            ·
              refine ⟨4727421085799944275763373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3151614057199962850508915 4727421085799944275763373)
              ·
                refine ⟨1772782907174979103411265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4727421085799944275763373 1772782907174979103411265)
                ·
                  refine ⟨1329587180381234327558449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1772782907174979103411265 1329587180381234327558449)
                  ·
                    refine ⟨997190385285925745668837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1329587180381234327558449 997190385285925745668837)
                    ·
                      refine ⟨186973197241111077312907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 997190385285925745668837 186973197241111077312907)
                      ·
                        rfl

theorem cell23_364129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_364129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364129 prefixEnd_364129 := by exact prefixLift 364129
  have htrace : WordTrace (prefixWord ++ tailWord_364129) baseStart_364129 baseEnd_364129 := by
    simpa [prefixWord, tailWord_364129, baseEnd_364129] using wordTrace_append hprefix tailTrace_364129
  have hstable : (prefixWord ++ tailWord_364129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364129).length < 2 ^ (prefixWord ++ tailWord_364129).sum := by decide
  have hdescent : baseEnd_364129 < baseStart_364129 := by decide
  rcases family_descends (prefixWord ++ tailWord_364129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364133 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 1, 4, 2]
def baseStart_364133 : Nat := 118140960795 + 364133 * 2 ^ 59
def prefixEnd_364133 : Nat := 4983230072969 + 3 ^ 40 * 364133 * 2
def baseEnd_364133 : Nat := 186975251163729061662889

theorem tailTrace_364133 : CollatzResearch.WordTrace tailWord_364133 prefixEnd_364133 186975251163729061662889 := by
  unfold tailWord_364133
  simp only [CollatzResearch.WordTrace]
  refine ⟨13281021589815804810393053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8854014393210536540262035 13281021589815804810393053)
  ·
    refine ⟨4980383096180926803897395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13281021589815804810393053 4980383096180926803897395)
    ·
      refine ⟨7470574644271390205846093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4980383096180926803897395 7470574644271390205846093)
      ·
        refine ⟨2801465491601771327192285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7470574644271390205846093 2801465491601771327192285)
        ·
          refine ⟨1050549559350664247697107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2801465491601771327192285 1050549559350664247697107)
          ·
            refine ⟨1575824339025996371545661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050549559350664247697107 1575824339025996371545661)
            ·
              refine ⟨590934127134748639329623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1575824339025996371545661 590934127134748639329623)
              ·
                refine ⟨886401190702122958994435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590934127134748639329623 886401190702122958994435)
                ·
                  refine ⟨1329601786053184438491653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886401190702122958994435 1329601786053184438491653)
                  ·
                    refine ⟨249300334884972082217185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1329601786053184438491653 249300334884972082217185)
                    ·
                      refine ⟨186975251163729061662889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249300334884972082217185 186975251163729061662889)
                      ·
                        rfl

theorem cell23_364133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_364133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364133 prefixEnd_364133 := by exact prefixLift 364133
  have htrace : WordTrace (prefixWord ++ tailWord_364133) baseStart_364133 baseEnd_364133 := by
    simpa [prefixWord, tailWord_364133, baseEnd_364133] using wordTrace_append hprefix tailTrace_364133
  have hstable : (prefixWord ++ tailWord_364133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364133).length < 2 ^ (prefixWord ++ tailWord_364133).sum := by decide
  have hdescent : baseEnd_364133 < baseStart_364133 := by decide
  rcases family_descends (prefixWord ++ tailWord_364133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364150 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_364150 : Nat := 118140960795 + 364150 * 2 ^ 59
def prefixEnd_364150 : Nat := 4983230072969 + 3 ^ 40 * 364150 * 2
def baseEnd_364150 : Nat := 186983980334855495150311

theorem tailTrace_364150 : CollatzResearch.WordTrace tailWord_364150 prefixEnd_364150 186983980334855495150311 := by
  unfold tailWord_364150
  simp only [CollatzResearch.WordTrace]
  refine ⟨830102601922138544610119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8854427753836144475841269 830102601922138544610119)
  ·
    refine ⟨1245153902883207816915179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 830102601922138544610119 1245153902883207816915179)
    ·
      refine ⟨1867730854324811725372769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1245153902883207816915179 1867730854324811725372769)
      ·
        refine ⟨1400798140743608794029577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1867730854324811725372769 1400798140743608794029577)
        ·
          refine ⟨1050598605557706595522183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1400798140743608794029577 1050598605557706595522183)
          ·
            refine ⟨1575897908336559893283275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050598605557706595522183 1575897908336559893283275)
            ·
              refine ⟨2363846862504839839924913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575897908336559893283275 2363846862504839839924913)
              ·
                refine ⟨1772885146878629879943685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2363846862504839839924913 1772885146878629879943685)
                ·
                  refine ⟨332415965039743102489441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772885146878629879943685 332415965039743102489441)
                  ·
                    refine ⟨249311973779807326867081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 332415965039743102489441 249311973779807326867081)
                    ·
                      refine ⟨186983980334855495150311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249311973779807326867081 186983980334855495150311)
                      ·
                        rfl

theorem cell23_364150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_364150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364150 prefixEnd_364150 := by exact prefixLift 364150
  have htrace : WordTrace (prefixWord ++ tailWord_364150) baseStart_364150 baseEnd_364150 := by
    simpa [prefixWord, tailWord_364150, baseEnd_364150] using wordTrace_append hprefix tailTrace_364150
  have hstable : (prefixWord ++ tailWord_364150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364150).length < 2 ^ (prefixWord ++ tailWord_364150).sum := by decide
  have hdescent : baseEnd_364150 < baseStart_364150 := by decide
  rcases family_descends (prefixWord ++ tailWord_364150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364169 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 4, 5]
def baseStart_364169 : Nat := 118140960795 + 364169 * 2 ^ 59
def prefixEnd_364169 : Nat := 4983230072969 + 3 ^ 40 * 364169 * 2
def baseEnd_364169 : Nat := 62331245489096973604241

theorem tailTrace_364169 : CollatzResearch.WordTrace tailWord_364169 prefixEnd_364169 62331245489096973604241 := by
  unfold tailWord_364169
  simp only [CollatzResearch.WordTrace]
  refine ⟨13282334617685382958703561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8854889745123588639135707 13282334617685382958703561)
  ·
    refine ⟨9961750963264037219027671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13282334617685382958703561 9961750963264037219027671)
    ·
      refine ⟨14942626444896055828541507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9961750963264037219027671 14942626444896055828541507)
      ·
        refine ⟨22413939667344083742812261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14942626444896055828541507 22413939667344083742812261)
        ·
          refine ⟨4202613687627015701777299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22413939667344083742812261 4202613687627015701777299)
          ·
            refine ⟨6303920531440523552665949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4202613687627015701777299 6303920531440523552665949)
            ·
              refine ⟨2363970199290196332249731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6303920531440523552665949 2363970199290196332249731)
              ·
                refine ⟨3545955298935294498374597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363970199290196332249731 3545955298935294498374597)
                ·
                  refine ⟨664866618550367718445237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3545955298935294498374597 664866618550367718445237)
                  ·
                    refine ⟨62331245489096973604241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 664866618550367718445237 62331245489096973604241)
                    ·
                      rfl

theorem cell23_364169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_364169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364169 prefixEnd_364169 := by exact prefixLift 364169
  have htrace : WordTrace (prefixWord ++ tailWord_364169) baseStart_364169 baseEnd_364169 := by
    simpa [prefixWord, tailWord_364169, baseEnd_364169] using wordTrace_append hprefix tailTrace_364169
  have hstable : (prefixWord ++ tailWord_364169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364169).length < 2 ^ (prefixWord ++ tailWord_364169).sum := by decide
  have hdescent : baseEnd_364169 < baseStart_364169 := by decide
  rcases family_descends (prefixWord ++ tailWord_364169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364230 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_364230 : Nat := 118140960795 + 364230 * 2 ^ 59
def prefixEnd_364230 : Nat := 4983230072969 + 3 ^ 40 * 364230 * 2
def baseEnd_364230 : Nat := 187025058787215182149943

theorem tailTrace_364230 : CollatzResearch.WordTrace tailWord_364230 prefixEnd_364230 187025058787215182149943 := by
  unfold tailWord_364230
  simp only [CollatzResearch.WordTrace]
  refine ⟨415142483452012199271067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8856372980309593584449429 415142483452012199271067)
  ·
    refine ⟨622713725178018298906601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 415142483452012199271067 622713725178018298906601)
    ·
      refine ⟨467035293883513724179951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 622713725178018298906601 467035293883513724179951)
      ·
        refine ⟨700552940825270586269927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467035293883513724179951 700552940825270586269927)
        ·
          refine ⟨1050829411237905879404891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700552940825270586269927 1050829411237905879404891)
          ·
            refine ⟨1576244116856858819107337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050829411237905879404891 1576244116856858819107337)
            ·
              refine ⟨1182183087642644114330503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1576244116856858819107337 1182183087642644114330503)
              ·
                refine ⟨1773274631463966171495755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182183087642644114330503 1773274631463966171495755)
                ·
                  refine ⟨2659911947195949257243633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1773274631463966171495755 2659911947195949257243633)
                  ·
                    refine ⟨1994933960396961942932725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2659911947195949257243633 1994933960396961942932725)
                    ·
                      refine ⟨187025058787215182149943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1994933960396961942932725 187025058787215182149943)
                      ·
                        rfl

theorem cell23_364230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_364230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364230 prefixEnd_364230 := by exact prefixLift 364230
  have htrace : WordTrace (prefixWord ++ tailWord_364230) baseStart_364230 baseEnd_364230 := by
    simpa [prefixWord, tailWord_364230, baseEnd_364230] using wordTrace_append hprefix tailTrace_364230
  have hstable : (prefixWord ++ tailWord_364230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364230).length < 2 ^ (prefixWord ++ tailWord_364230).sum := by decide
  have hdescent : baseEnd_364230 < baseStart_364230 := by decide
  rcases family_descends (prefixWord ++ tailWord_364230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364316 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_364316 : Nat := 118140960795 + 364316 * 2 ^ 59
def prefixEnd_364316 : Nat := 4983230072969 + 3 ^ 40 * 364316 * 2
def baseEnd_364316 : Nat := 187069218123501845674547

theorem tailTrace_364316 : CollatzResearch.WordTrace tailWord_364316 prefixEnd_364316 187069218123501845674547 := by
  unfold tailWord_364316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6643848074076413532152401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8858464098768551376203201 6643848074076413532152401)
  ·
    refine ⟨4982886055557310149114301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6643848074076413532152401 4982886055557310149114301)
    ·
      refine ⟨1868582270833991305917863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4982886055557310149114301 1868582270833991305917863)
      ·
        refine ⟨2802873406250986958876795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1868582270833991305917863 2802873406250986958876795)
        ·
          refine ⟨4204310109376480438315193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802873406250986958876795 4204310109376480438315193)
          ·
            refine ⟨3153232582032360328736395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4204310109376480438315193 3153232582032360328736395)
            ·
              refine ⟨4729848873048540493104593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3153232582032360328736395 4729848873048540493104593)
              ·
                refine ⟨3547386654786405369828445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4729848873048540493104593 3547386654786405369828445)
                ·
                  refine ⟨1330269995544902013685667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3547386654786405369828445 1330269995544902013685667)
                  ·
                    refine ⟨1995404993317353020528501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1330269995544902013685667 1995404993317353020528501)
                    ·
                      refine ⟨187069218123501845674547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1995404993317353020528501 187069218123501845674547)
                      ·
                        rfl

theorem cell23_364316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_364316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364316 prefixEnd_364316 := by exact prefixLift 364316
  have htrace : WordTrace (prefixWord ++ tailWord_364316) baseStart_364316 baseEnd_364316 := by
    simpa [prefixWord, tailWord_364316, baseEnd_364316] using wordTrace_append hprefix tailTrace_364316
  have hstable : (prefixWord ++ tailWord_364316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364316).length < 2 ^ (prefixWord ++ tailWord_364316).sum := by decide
  have hdescent : baseEnd_364316 < baseStart_364316 := by decide
  rcases family_descends (prefixWord ++ tailWord_364316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364318 : List Nat := [4, 3, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_364318 : Nat := 118140960795 + 364318 * 2 ^ 59
def prefixEnd_364318 : Nat := 4983230072969 + 3 ^ 40 * 364318 * 2
def baseEnd_364318 : Nat := 62356748361603612616513

theorem tailTrace_364318 : CollatzResearch.WordTrace tailWord_364318 prefixEnd_364318 62356748361603612616513 := by
  unfold tailWord_364318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660971136768197675734701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8858512729430387603918405 1660971136768197675734701)
  ·
    refine ⟨622864176288074128400513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1660971136768197675734701 622864176288074128400513)
    ·
      refine ⟨467148132216055596300385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 622864176288074128400513 467148132216055596300385)
      ·
        refine ⟨350361099162041697225289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467148132216055596300385 350361099162041697225289)
        ·
          refine ⟨262770824371531272918967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350361099162041697225289 262770824371531272918967)
          ·
            refine ⟨394156236557296909378451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262770824371531272918967 394156236557296909378451)
            ·
              refine ⟨591234354835945364067677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394156236557296909378451 591234354835945364067677)
              ·
                refine ⟨221712883063479511525379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 591234354835945364067677 221712883063479511525379)
                ·
                  refine ⟨332569324595219267288069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221712883063479511525379 332569324595219267288069)
                  ·
                    refine ⟨62356748361603612616513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 332569324595219267288069 62356748361603612616513)
                    ·
                      rfl

theorem cell23_364318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_364318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364318 prefixEnd_364318 := by exact prefixLift 364318
  have htrace : WordTrace (prefixWord ++ tailWord_364318) baseStart_364318 baseEnd_364318 := by
    simpa [prefixWord, tailWord_364318, baseEnd_364318] using wordTrace_append hprefix tailTrace_364318
  have hstable : (prefixWord ++ tailWord_364318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364318).length < 2 ^ (prefixWord ++ tailWord_364318).sum := by decide
  have hdescent : baseEnd_364318 < baseStart_364318 := by decide
  rcases family_descends (prefixWord ++ tailWord_364318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364324 : List Nat := [2, 3, 1, 3, 2, 3, 1, 3, 1, 1, 3]
def baseStart_364324 : Nat := 118140960795 + 364324 * 2 ^ 59
def prefixEnd_364324 : Nat := 4983230072969 + 3 ^ 40 * 364324 * 2
def baseEnd_364324 : Nat := 187073325968737814374511

theorem tailTrace_364324 : CollatzResearch.WordTrace tailWord_364324 prefixEnd_364324 187073325968737814374511 := by
  unfold tailWord_364324
  simp only [CollatzResearch.WordTrace]
  refine ⟨6643993966061922215298013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8858658621415896287064017 6643993966061922215298013)
  ·
    refine ⟨2491497737273220830736755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6643993966061922215298013 2491497737273220830736755)
    ·
      refine ⟨3737246605909831246105133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2491497737273220830736755 3737246605909831246105133)
      ·
        refine ⟨1401467477216186717289425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3737246605909831246105133 1401467477216186717289425)
        ·
          refine ⟨1051100607912140037967069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1401467477216186717289425 1051100607912140037967069)
          ·
            refine ⟨394162727967052514237651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1051100607912140037967069 394162727967052514237651)
            ·
              refine ⟨591244091950578771356477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394162727967052514237651 591244091950578771356477)
              ·
                refine ⟨221716534481467039258679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 591244091950578771356477 221716534481467039258679)
                ·
                  refine ⟨332574801722200558888019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221716534481467039258679 332574801722200558888019)
                  ·
                    refine ⟨498862202583300838332029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 332574801722200558888019 498862202583300838332029)
                    ·
                      refine ⟨187073325968737814374511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 498862202583300838332029 187073325968737814374511)
                      ·
                        rfl

theorem cell23_364324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_364324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364324 prefixEnd_364324 := by exact prefixLift 364324
  have htrace : WordTrace (prefixWord ++ tailWord_364324) baseStart_364324 baseEnd_364324 := by
    simpa [prefixWord, tailWord_364324, baseEnd_364324] using wordTrace_append hprefix tailTrace_364324
  have hstable : (prefixWord ++ tailWord_364324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364324).length < 2 ^ (prefixWord ++ tailWord_364324).sum := by decide
  have hdescent : baseEnd_364324 < baseStart_364324 := by decide
  rcases family_descends (prefixWord ++ tailWord_364324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364340 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_364340 : Nat := 118140960795 + 364340 * 2 ^ 59
def prefixEnd_364340 : Nat := 4983230072969 + 3 ^ 40 * 364340 * 2
def baseEnd_364340 : Nat := 62360513886403250591479

theorem tailTrace_364340 : CollatzResearch.WordTrace tailWord_364340 prefixEnd_364340 62360513886403250591479 := by
  unfold tailWord_364340
  simp only [CollatzResearch.WordTrace]
  refine ⟨6644285750032939581589237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8859047666710586108785649 6644285750032939581589237)
  ·
    refine ⟨622901789065588085773991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6644285750032939581589237 622901789065588085773991)
    ·
      refine ⟨934352683598382128660987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622901789065588085773991 934352683598382128660987)
      ·
        refine ⟨1401529025397573192991481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934352683598382128660987 1401529025397573192991481)
        ·
          refine ⟨1051146769048179894743611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1401529025397573192991481 1051146769048179894743611)
          ·
            refine ⟨1576720153572269842115417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051146769048179894743611 1576720153572269842115417)
            ·
              refine ⟨1182540115179202381586563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1576720153572269842115417 1182540115179202381586563)
              ·
                refine ⟨1773810172768803572379845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182540115179202381586563 1773810172768803572379845)
                ·
                  refine ⟨332589407394150669821221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1773810172768803572379845 332589407394150669821221)
                  ·
                    refine ⟨62360513886403250591479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 332589407394150669821221 62360513886403250591479)
                    ·
                      rfl

theorem cell23_364340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_364340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364340 prefixEnd_364340 := by exact prefixLift 364340
  have htrace : WordTrace (prefixWord ++ tailWord_364340) baseStart_364340 baseEnd_364340 := by
    simpa [prefixWord, tailWord_364340, baseEnd_364340] using wordTrace_append hprefix tailTrace_364340
  have hstable : (prefixWord ++ tailWord_364340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364340).length < 2 ^ (prefixWord ++ tailWord_364340).sum := by decide
  have hdescent : baseEnd_364340 < baseStart_364340 := by decide
  rcases family_descends (prefixWord ++ tailWord_364340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364398 : List Nat := [4, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_364398 : Nat := 118140960795 + 364398 * 2 ^ 59
def prefixEnd_364398 : Nat := 4983230072969 + 3 ^ 40 * 364398 * 2
def baseEnd_364398 : Nat := 187111323537170524849171

theorem tailTrace_364398 : CollatzResearch.WordTrace tailWord_364398 prefixEnd_364398 187111323537170524849171 := by
  unfold tailWord_364398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1661335866731969383598731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8860457955903836712526565 1661335866731969383598731)
  ·
    refine ⟨2492003800097954075398097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1661335866731969383598731 2492003800097954075398097)
    ·
      refine ⟨1869002850073465556548573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2492003800097954075398097 1869002850073465556548573)
      ·
        refine ⟨700876068777549583705715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1869002850073465556548573 700876068777549583705715)
        ·
          refine ⟨1051314103166324375558573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700876068777549583705715 1051314103166324375558573)
          ·
            refine ⟨394242788687371640834465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1051314103166324375558573 394242788687371640834465)
            ·
              refine ⟨295682091515528730625849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394242788687371640834465 295682091515528730625849)
              ·
                refine ⟨221761568636646547969387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295682091515528730625849 221761568636646547969387)
                ·
                  refine ⟨332642352954969821954081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221761568636646547969387 332642352954969821954081)
                  ·
                    refine ⟨249481764716227366465561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 332642352954969821954081 249481764716227366465561)
                    ·
                      refine ⟨187111323537170524849171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249481764716227366465561 187111323537170524849171)
                      ·
                        rfl

theorem cell23_364398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_364398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364398 prefixEnd_364398 := by exact prefixLift 364398
  have htrace : WordTrace (prefixWord ++ tailWord_364398) baseStart_364398 baseEnd_364398 := by
    simpa [prefixWord, tailWord_364398, baseEnd_364398] using wordTrace_append hprefix tailTrace_364398
  have hstable : (prefixWord ++ tailWord_364398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364398).length < 2 ^ (prefixWord ++ tailWord_364398).sum := by decide
  have hdescent : baseEnd_364398 < baseStart_364398 := by decide
  rcases family_descends (prefixWord ++ tailWord_364398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364403 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 5, 4, 2]
def baseStart_364403 : Nat := 118140960795 + 364403 * 2 ^ 59
def prefixEnd_364403 : Nat := 4983230072969 + 3 ^ 40 * 364403 * 2
def baseEnd_364403 : Nat := 187113890940443005286647

theorem tailTrace_364403 : CollatzResearch.WordTrace tailWord_364403 prefixEnd_364403 187113890940443005286647 := by
  unfold tailWord_364403
  simp only [CollatzResearch.WordTrace]
  refine ⟨13290869298837640922721863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8860579532558427281814575 13290869298837640922721863)
  ·
    refine ⟨19936303948256461384082795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13290869298837640922721863 19936303948256461384082795)
    ·
      refine ⟨29904455922384692076124193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19936303948256461384082795 29904455922384692076124193)
      ·
        refine ⟨22428341941788519057093145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29904455922384692076124193 22428341941788519057093145)
        ·
          refine ⟨16821256456341389292819859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22428341941788519057093145 16821256456341389292819859)
          ·
            refine ⟨25231884684512083939229789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16821256456341389292819859 25231884684512083939229789)
            ·
              refine ⟨9461956756692031477211171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25231884684512083939229789 9461956756692031477211171)
              ·
                refine ⟨14192935135038047215816757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9461956756692031477211171 14192935135038047215816757)
                ·
                  refine ⟨1330587668909816926482821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14192935135038047215816757 1330587668909816926482821)
                  ·
                    refine ⟨249485187920590673715529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1330587668909816926482821 249485187920590673715529)
                    ·
                      refine ⟨187113890940443005286647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249485187920590673715529 187113890940443005286647)
                      ·
                        rfl

theorem cell23_364403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 4, 2].length) (baseStart_364403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364403 prefixEnd_364403 := by exact prefixLift 364403
  have htrace : WordTrace (prefixWord ++ tailWord_364403) baseStart_364403 baseEnd_364403 := by
    simpa [prefixWord, tailWord_364403, baseEnd_364403] using wordTrace_append hprefix tailTrace_364403
  have hstable : (prefixWord ++ tailWord_364403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364403).length < 2 ^ (prefixWord ++ tailWord_364403).sum := by decide
  have hdescent : baseEnd_364403 < baseStart_364403 := by decide
  rcases family_descends (prefixWord ++ tailWord_364403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364414 : List Nat := [4, 2, 3, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_364414 : Nat := 118140960795 + 364414 * 2 ^ 59
def prefixEnd_364414 : Nat := 4983230072969 + 3 ^ 40 * 364414 * 2
def baseEnd_364414 : Nat := 187119539227642462249097

theorem tailTrace_364414 : CollatzResearch.WordTrace tailWord_364414 prefixEnd_364414 187119539227642462249097 := by
  unfold tailWord_364414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1661408812724723725171537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8860847001198526534248197 1661408812724723725171537)
  ·
    refine ⟨1246056609543542793878653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1661408812724723725171537 1246056609543542793878653)
    ·
      refine ⟨467271228578828547704495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1246056609543542793878653 467271228578828547704495)
      ·
        refine ⟨700906842868242821556743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467271228578828547704495 700906842868242821556743)
        ·
          refine ⟨1051360264302364232335115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700906842868242821556743 1051360264302364232335115)
          ·
            refine ⟨1577040396453546348502673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051360264302364232335115 1577040396453546348502673)
            ·
              refine ⟨1182780297340159761377005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1577040396453546348502673 1182780297340159761377005)
              ·
                refine ⟨443542611502559910516377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1182780297340159761377005 443542611502559910516377)
                ·
                  refine ⟨332656958626919932887283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443542611502559910516377 332656958626919932887283)
                  ·
                    refine ⟨498985437940379899330925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 332656958626919932887283 498985437940379899330925)
                    ·
                      refine ⟨187119539227642462249097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 498985437940379899330925 187119539227642462249097)
                      ·
                        rfl

theorem cell23_364414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_364414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364414 prefixEnd_364414 := by exact prefixLift 364414
  have htrace : WordTrace (prefixWord ++ tailWord_364414) baseStart_364414 baseEnd_364414 := by
    simpa [prefixWord, tailWord_364414, baseEnd_364414] using wordTrace_append hprefix tailTrace_364414
  have hstable : (prefixWord ++ tailWord_364414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364414).length < 2 ^ (prefixWord ++ tailWord_364414).sum := by decide
  have hdescent : baseEnd_364414 < baseStart_364414 := by decide
  rcases family_descends (prefixWord ++ tailWord_364414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364420 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_364420 : Nat := 118140960795 + 364420 * 2 ^ 59
def prefixEnd_364420 : Nat := 4983230072969 + 3 ^ 40 * 364420 * 2
def baseEnd_364420 : Nat := 187122620111569438774069

theorem tailTrace_364420 : CollatzResearch.WordTrace tailWord_364420 prefixEnd_364420 187122620111569438774069 := by
  unfold tailWord_364420
  simp only [CollatzResearch.WordTrace]
  refine ⟨6645744669888026413045357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8860992893184035217393809 6645744669888026413045357)
  ·
    refine ⟨2492154251208009904892009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6645744669888026413045357 2492154251208009904892009)
    ·
      refine ⟨1869115688406007428669007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2492154251208009904892009 1869115688406007428669007)
      ·
        refine ⟨2803673532609011143003511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1869115688406007428669007 2803673532609011143003511)
        ·
          refine ⟨4205510298913516714505267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2803673532609011143003511 4205510298913516714505267)
          ·
            refine ⟨6308265448370275071757901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205510298913516714505267 6308265448370275071757901)
            ·
              refine ⟨2365599543138853151909213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6308265448370275071757901 2365599543138853151909213)
              ·
                refine ⟨887099828677069931965955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2365599543138853151909213 887099828677069931965955)
                ·
                  refine ⟨1330649743015604897948933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887099828677069931965955 1330649743015604897948933)
                  ·
                    refine ⟨249496826815425918365425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1330649743015604897948933 249496826815425918365425)
                    ·
                      refine ⟨187122620111569438774069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249496826815425918365425 187122620111569438774069)
                      ·
                        rfl

theorem cell23_364420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_364420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364420 prefixEnd_364420 := by exact prefixLift 364420
  have htrace : WordTrace (prefixWord ++ tailWord_364420) baseStart_364420 baseEnd_364420 := by
    simpa [prefixWord, tailWord_364420, baseEnd_364420] using wordTrace_append hprefix tailTrace_364420
  have hstable : (prefixWord ++ tailWord_364420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364420).length < 2 ^ (prefixWord ++ tailWord_364420).sum := by decide
  have hdescent : baseEnd_364420 < baseStart_364420 := by decide
  rcases family_descends (prefixWord ++ tailWord_364420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364543 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 3]
def baseStart_364543 : Nat := 118140960795 + 364543 * 2 ^ 59
def prefixEnd_364543 : Nat := 4983230072969 + 3 ^ 40 * 364543 * 2
def baseEnd_364543 : Nat := 187185778232072457536003

theorem tailTrace_364543 : CollatzResearch.WordTrace tailWord_364543 prefixEnd_364543 187185778232072457536003 := by
  unfold tailWord_364543
  simp only [CollatzResearch.WordTrace]
  refine ⟨13295975518330444832818283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8863983678886963221878855 13295975518330444832818283)
  ·
    refine ⟨19943963277495667249227425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13295975518330444832818283 19943963277495667249227425)
    ·
      refine ⟨14957972458121750436920569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19943963277495667249227425 14957972458121750436920569)
      ·
        refine ⟨11218479343591312827690427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14957972458121750436920569 11218479343591312827690427)
        ·
          refine ⟨16827719015386969241535641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11218479343591312827690427 16827719015386969241535641)
          ·
            refine ⟨12620789261540226931151731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16827719015386969241535641 12620789261540226931151731)
            ·
              refine ⟨18931183892310340396727597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12620789261540226931151731 18931183892310340396727597)
              ·
                refine ⟨7099193959616377648772849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18931183892310340396727597 7099193959616377648772849)
                ·
                  refine ⟨5324395469712283236579637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7099193959616377648772849 5324395469712283236579637)
                  ·
                    refine ⟨499162075285526553429341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5324395469712283236579637 499162075285526553429341)
                    ·
                      refine ⟨187185778232072457536003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 499162075285526553429341 187185778232072457536003)
                      ·
                        rfl

theorem cell23_364543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_364543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364543 prefixEnd_364543 := by exact prefixLift 364543
  have htrace : WordTrace (prefixWord ++ tailWord_364543) baseStart_364543 baseEnd_364543 := by
    simpa [prefixWord, tailWord_364543, baseEnd_364543] using wordTrace_append hprefix tailTrace_364543
  have hstable : (prefixWord ++ tailWord_364543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364543).length < 2 ^ (prefixWord ++ tailWord_364543).sum := by decide
  have hdescent : baseEnd_364543 < baseStart_364543 := by decide
  rcases family_descends (prefixWord ++ tailWord_364543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364560 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 5, 1, 3]
def baseStart_364560 : Nat := 118140960795 + 364560 * 2 ^ 59
def prefixEnd_364560 : Nat := 4983230072969 + 3 ^ 40 * 364560 * 2
def baseEnd_364560 : Nat := 187194507403198891023425

theorem tailTrace_364560 : CollatzResearch.WordTrace tailWord_364560 prefixEnd_364560 187194507403198891023425 := by
  unfold tailWord_364560
  simp only [CollatzResearch.WordTrace]
  refine ⟨6648297779634428368093567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8864397039512571157458089 6648297779634428368093567)
  ·
    refine ⟨9972446669451642552140351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6648297779634428368093567 9972446669451642552140351)
    ·
      refine ⟨14958670004177463828210527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9972446669451642552140351 14958670004177463828210527)
      ·
        refine ⟨22438005006266195742315791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14958670004177463828210527 22438005006266195742315791)
        ·
          refine ⟨33657007509399293613473687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22438005006266195742315791 33657007509399293613473687)
          ·
            refine ⟨50485511264098940420210531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33657007509399293613473687 50485511264098940420210531)
            ·
              refine ⟨75728266896148410630315797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50485511264098940420210531 75728266896148410630315797)
              ·
                refine ⟨3549762510756956748296053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75728266896148410630315797 3549762510756956748296053)
                ·
                  refine ⟨332790235383464695152755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3549762510756956748296053 332790235383464695152755)
                  ·
                    refine ⟨499185353075197042729133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 332790235383464695152755 499185353075197042729133)
                    ·
                      refine ⟨187194507403198891023425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 499185353075197042729133 187194507403198891023425)
                      ·
                        rfl

theorem cell23_364560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 5, 1, 3].length) (baseStart_364560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364560 prefixEnd_364560 := by exact prefixLift 364560
  have htrace : WordTrace (prefixWord ++ tailWord_364560) baseStart_364560 baseEnd_364560 := by
    simpa [prefixWord, tailWord_364560, baseEnd_364560] using wordTrace_append hprefix tailTrace_364560
  have hstable : (prefixWord ++ tailWord_364560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364560).length < 2 ^ (prefixWord ++ tailWord_364560).sum := by decide
  have hdescent : baseEnd_364560 < baseStart_364560 := by decide
  rcases family_descends (prefixWord ++ tailWord_364560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364567 : List Nat := [1, 1, 3, 5, 2, 1, 2, 2, 6]
def baseStart_364567 : Nat := 118140960795 + 364567 * 2 ^ 59
def prefixEnd_364567 : Nat := 4983230072969 + 3 ^ 40 * 364567 * 2
def baseEnd_364567 : Nat := 20799789085308929292877

theorem tailTrace_364567 : CollatzResearch.WordTrace tailWord_364567 prefixEnd_364567 20799789085308929292877 := by
  unfold tailWord_364567
  simp only [CollatzResearch.WordTrace]
  refine ⟨13296850870243496931691955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8864567246828997954461303 13296850870243496931691955)
  ·
    refine ⟨19945276305365245397537933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13296850870243496931691955 19945276305365245397537933)
    ·
      refine ⟨7479478614511967024076725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19945276305365245397537933 7479478614511967024076725)
      ·
        refine ⟨701201120110496908507193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7479478614511967024076725 701201120110496908507193)
        ·
          refine ⟨525900840082872681380395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701201120110496908507193 525900840082872681380395)
          ·
            refine ⟨788851260124309022070593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525900840082872681380395 788851260124309022070593)
            ·
              refine ⟨591638445093231766552945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788851260124309022070593 591638445093231766552945)
              ·
                refine ⟨443728833819923824914709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591638445093231766552945 443728833819923824914709)
                ·
                  refine ⟨20799789085308929292877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 443728833819923824914709 20799789085308929292877)
                  ·
                    rfl

theorem cell23_364567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 6].length) (baseStart_364567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364567 prefixEnd_364567 := by exact prefixLift 364567
  have htrace : WordTrace (prefixWord ++ tailWord_364567) baseStart_364567 baseEnd_364567 := by
    simpa [prefixWord, tailWord_364567, baseEnd_364567] using wordTrace_append hprefix tailTrace_364567
  have hstable : (prefixWord ++ tailWord_364567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364567).length < 2 ^ (prefixWord ++ tailWord_364567).sum := by decide
  have hdescent : baseEnd_364567 < baseStart_364567 := by decide
  rcases family_descends (prefixWord ++ tailWord_364567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364603 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 5]
def baseStart_364603 : Nat := 118140960795 + 364603 * 2 ^ 59
def prefixEnd_364603 : Nat := 4983230072969 + 3 ^ 40 * 364603 * 2
def baseEnd_364603 : Nat := 187216587071342222785727

theorem tailTrace_364603 : CollatzResearch.WordTrace tailWord_364603 prefixEnd_364603 187216587071342222785727 := by
  unfold tailWord_364603
  simp only [CollatzResearch.WordTrace]
  refine ⟨13298163898113075080002463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8865442598742050053334975 13298163898113075080002463)
  ·
    refine ⟨19947245847169612620003695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13298163898113075080002463 19947245847169612620003695)
    ·
      refine ⟨29920868770754418930005543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19947245847169612620003695 29920868770754418930005543)
      ·
        refine ⟨44881303156131628395008315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29920868770754418930005543 44881303156131628395008315)
        ·
          refine ⟨67321954734197442592512473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44881303156131628395008315 67321954734197442592512473)
          ·
            refine ⟨50491466050648081944384355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67321954734197442592512473 50491466050648081944384355)
            ·
              refine ⟨75737199075972122916576533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50491466050648081944384355 75737199075972122916576533)
              ·
                refine ⟨3550181206686193261714525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75737199075972122916576533 3550181206686193261714525)
                ·
                  refine ⟨1331317952507322473142947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3550181206686193261714525 1331317952507322473142947)
                  ·
                    refine ⟨1996976928760983709714421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1331317952507322473142947 1996976928760983709714421)
                    ·
                      refine ⟨187216587071342222785727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1996976928760983709714421 187216587071342222785727)
                      ·
                        rfl

theorem cell23_364603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 5].length) (baseStart_364603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364603 prefixEnd_364603 := by exact prefixLift 364603
  have htrace : WordTrace (prefixWord ++ tailWord_364603) baseStart_364603 baseEnd_364603 := by
    simpa [prefixWord, tailWord_364603, baseEnd_364603] using wordTrace_append hprefix tailTrace_364603
  have hstable : (prefixWord ++ tailWord_364603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364603).length < 2 ^ (prefixWord ++ tailWord_364603).sum := by decide
  have hdescent : baseEnd_364603 < baseStart_364603 := by decide
  rcases family_descends (prefixWord ++ tailWord_364603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364613 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_364613 : Nat := 118140960795 + 364613 * 2 ^ 59
def prefixEnd_364613 : Nat := 4983230072969 + 3 ^ 40 * 364613 * 2
def baseEnd_364613 : Nat := 187221721877887183660681

theorem tailTrace_364613 : CollatzResearch.WordTrace tailWord_364613 prefixEnd_364613 187221721877887183660681 := by
  unfold tailWord_364613
  simp only [CollatzResearch.WordTrace]
  refine ⟨13298528628076846787866493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8865685752051231191910995 13298528628076846787866493)
  ·
    refine ⟨4986948235528817545449935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13298528628076846787866493 4986948235528817545449935)
    ·
      refine ⟨7480422353293226318174903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4986948235528817545449935 7480422353293226318174903)
      ·
        refine ⟨11220633529939839477262355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7480422353293226318174903 11220633529939839477262355)
        ·
          refine ⟨16830950294909759215893533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11220633529939839477262355 16830950294909759215893533)
          ·
            refine ⟨6311606360591159705960075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16830950294909759215893533 6311606360591159705960075)
            ·
              refine ⟨9467409540886739558940113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6311606360591159705960075 9467409540886739558940113)
              ·
                refine ⟨7100557155665054669205085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9467409540886739558940113 7100557155665054669205085)
                ·
                  refine ⟨2662708933374395500951907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7100557155665054669205085 2662708933374395500951907)
                  ·
                    refine ⟨3994063400061593251427861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2662708933374395500951907 3994063400061593251427861)
                    ·
                      refine ⟨187221721877887183660681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3994063400061593251427861 187221721877887183660681)
                      ·
                        rfl

theorem cell23_364613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_364613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364613 prefixEnd_364613 := by exact prefixLift 364613
  have htrace : WordTrace (prefixWord ++ tailWord_364613) baseStart_364613 baseEnd_364613 := by
    simpa [prefixWord, tailWord_364613, baseEnd_364613] using wordTrace_append hprefix tailTrace_364613
  have hstable : (prefixWord ++ tailWord_364613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364613).length < 2 ^ (prefixWord ++ tailWord_364613).sum := by decide
  have hdescent : baseEnd_364613 < baseStart_364613 := by decide
  rcases family_descends (prefixWord ++ tailWord_364613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364614 : List Nat := [6, 1, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_364614 : Nat := 118140960795 + 364614 * 2 ^ 59
def prefixEnd_364614 : Nat := 4983230072969 + 3 ^ 40 * 364614 * 2
def baseEnd_364614 : Nat := 62407411786180559916059

theorem tailTrace_364614 : CollatzResearch.WordTrace tailWord_364614 prefixEnd_364614 62407411786180559916059 := by
  unfold tailWord_364614
  simp only [CollatzResearch.WordTrace]
  refine ⟨415580159408538248707903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8865710067382149305768597 415580159408538248707903)
  ·
    refine ⟨623370239112807373061855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 415580159408538248707903 623370239112807373061855)
    ·
      refine ⟨935055358669211059592783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623370239112807373061855 935055358669211059592783)
      ·
        refine ⟨1402583038003816589389175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935055358669211059592783 1402583038003816589389175)
        ·
          refine ⟨2103874557005724884083763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402583038003816589389175 2103874557005724884083763)
          ·
            refine ⟨3155811835508587326125645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103874557005724884083763 3155811835508587326125645)
            ·
              refine ⟨1183429438315720247297117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3155811835508587326125645 1183429438315720247297117)
              ·
                refine ⟨443786039368395092736419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1183429438315720247297117 443786039368395092736419)
                ·
                  refine ⟨665679059052592639104629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443786039368395092736419 665679059052592639104629)
                  ·
                    refine ⟨62407411786180559916059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 665679059052592639104629 62407411786180559916059)
                    ·
                      rfl

theorem cell23_364614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_364614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364614 prefixEnd_364614 := by exact prefixLift 364614
  have htrace : WordTrace (prefixWord ++ tailWord_364614) baseStart_364614 baseEnd_364614 := by
    simpa [prefixWord, tailWord_364614, baseEnd_364614] using wordTrace_append hprefix tailTrace_364614
  have hstable : (prefixWord ++ tailWord_364614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364614).length < 2 ^ (prefixWord ++ tailWord_364614).sum := by decide
  have hdescent : baseEnd_364614 < baseStart_364614 := by decide
  rcases family_descends (prefixWord ++ tailWord_364614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364617 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 5, 2, 2]
def baseStart_364617 : Nat := 118140960795 + 364617 * 2 ^ 59
def prefixEnd_364617 : Nat := 4983230072969 + 3 ^ 40 * 364617 * 2
def baseEnd_364617 : Nat := 187223775800505168010663

theorem tailTrace_364617 : CollatzResearch.WordTrace tailWord_364617 prefixEnd_364617 187223775800505168010663 := by
  unfold tailWord_364617
  simp only [CollatzResearch.WordTrace]
  refine ⟨13298674520062355471012105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8865783013374903647341403 13298674520062355471012105)
  ·
    refine ⟨9974005890046766603259079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13298674520062355471012105 9974005890046766603259079)
    ·
      refine ⟨14961008835070149904888619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9974005890046766603259079 14961008835070149904888619)
      ·
        refine ⟨22441513252605224857332929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14961008835070149904888619 22441513252605224857332929)
        ·
          refine ⟨16831134939453918642999697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22441513252605224857332929 16831134939453918642999697)
          ·
            refine ⟨12623351204590438982249773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16831134939453918642999697 12623351204590438982249773)
            ·
              refine ⟨4733756701721414618343665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12623351204590438982249773 4733756701721414618343665)
              ·
                refine ⟨3550317526291060963757749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4733756701721414618343665 3550317526291060963757749)
                ·
                  refine ⟨332842268089786965352289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3550317526291060963757749 332842268089786965352289)
                  ·
                    refine ⟨249631701067340224014217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 332842268089786965352289 249631701067340224014217)
                    ·
                      refine ⟨187223775800505168010663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249631701067340224014217 187223775800505168010663)
                      ·
                        rfl

theorem cell23_364617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 2, 2].length) (baseStart_364617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364617 prefixEnd_364617 := by exact prefixLift 364617
  have htrace : WordTrace (prefixWord ++ tailWord_364617) baseStart_364617 baseEnd_364617 := by
    simpa [prefixWord, tailWord_364617, baseEnd_364617] using wordTrace_append hprefix tailTrace_364617
  have hstable : (prefixWord ++ tailWord_364617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364617).length < 2 ^ (prefixWord ++ tailWord_364617).sum := by decide
  have hdescent : baseEnd_364617 < baseStart_364617 := by decide
  rcases family_descends (prefixWord ++ tailWord_364617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364634 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2]
def baseStart_364634 : Nat := 118140960795 + 364634 * 2 ^ 59
def prefixEnd_364634 : Nat := 4983230072969 + 3 ^ 40 * 364634 * 2
def baseEnd_364634 : Nat := 187232504971631601498085

theorem tailTrace_364634 : CollatzResearch.WordTrace tailWord_364634 prefixEnd_364634 187232504971631601498085 := by
  unfold tailWord_364634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3324823640250191843595239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8866196374000511582920637 3324823640250191843595239)
  ·
    refine ⟨4987235460375287765392859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3324823640250191843595239 4987235460375287765392859)
    ·
      refine ⟨7480853190562931648089289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4987235460375287765392859 7480853190562931648089289)
      ·
        refine ⟨5610639892922198736066967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7480853190562931648089289 5610639892922198736066967)
        ·
          refine ⟨8415959839383298104100451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5610639892922198736066967 8415959839383298104100451)
          ·
            refine ⟨12623939759074947156150677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8415959839383298104100451 12623939759074947156150677)
            ·
              refine ⟨591747176206638147944563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12623939759074947156150677 591747176206638147944563)
              ·
                refine ⟨887620764309957221916845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591747176206638147944563 887620764309957221916845)
                ·
                  refine ⟨332857786616233958218817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887620764309957221916845 332857786616233958218817)
                  ·
                    refine ⟨249643339962175468664113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 332857786616233958218817 249643339962175468664113)
                    ·
                      refine ⟨187232504971631601498085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249643339962175468664113 187232504971631601498085)
                      ·
                        rfl

theorem cell23_364634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_364634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364634 prefixEnd_364634 := by exact prefixLift 364634
  have htrace : WordTrace (prefixWord ++ tailWord_364634) baseStart_364634 baseEnd_364634 := by
    simpa [prefixWord, tailWord_364634, baseEnd_364634] using wordTrace_append hprefix tailTrace_364634
  have hstable : (prefixWord ++ tailWord_364634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364634).length < 2 ^ (prefixWord ++ tailWord_364634).sum := by decide
  have hdescent : baseEnd_364634 < baseStart_364634 := by decide
  rcases family_descends (prefixWord ++ tailWord_364634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364637 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_364637 : Nat := 118140960795 + 364637 * 2 ^ 59
def prefixEnd_364637 : Nat := 4983230072969 + 3 ^ 40 * 364637 * 2
def baseEnd_364637 : Nat := 187234045413595089760571

theorem tailTrace_364637 : CollatzResearch.WordTrace tailWord_364637 prefixEnd_364637 187234045413595089760571 := by
  unfold tailWord_364637
  simp only [CollatzResearch.WordTrace]
  refine ⟨13299403979989898886740165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8866269319993265924493443 13299403979989898886740165)
  ·
    refine ⟨2493638246248106041263781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13299403979989898886740165 2493638246248106041263781)
    ·
      refine ⟨467557171171519882736959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2493638246248106041263781 467557171171519882736959)
      ·
        refine ⟨701335756757279824105439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467557171171519882736959 701335756757279824105439)
        ·
          refine ⟨1052003635135919736158159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701335756757279824105439 1052003635135919736158159)
          ·
            refine ⟨1578005452703879604237239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052003635135919736158159 1578005452703879604237239)
            ·
              refine ⟨2367008179055819406355859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578005452703879604237239 2367008179055819406355859)
              ·
                refine ⟨3550512268583729109533789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2367008179055819406355859 3550512268583729109533789)
                ·
                  refine ⟨1331442100718898416075171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3550512268583729109533789 1331442100718898416075171)
                  ·
                    refine ⟨1997163151078347624112757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1331442100718898416075171 1997163151078347624112757)
                    ·
                      refine ⟨187234045413595089760571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1997163151078347624112757 187234045413595089760571)
                      ·
                        rfl

theorem cell23_364637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_364637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364637 prefixEnd_364637 := by exact prefixLift 364637
  have htrace : WordTrace (prefixWord ++ tailWord_364637) baseStart_364637 baseEnd_364637 := by
    simpa [prefixWord, tailWord_364637, baseEnd_364637] using wordTrace_append hprefix tailTrace_364637
  have hstable : (prefixWord ++ tailWord_364637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364637).length < 2 ^ (prefixWord ++ tailWord_364637).sum := by decide
  have hdescent : baseEnd_364637 < baseStart_364637 := by decide
  rcases family_descends (prefixWord ++ tailWord_364637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364654 : List Nat := [4, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_364654 : Nat := 118140960795 + 364654 * 2 ^ 59
def prefixEnd_364654 : Nat := 4983230072969 + 3 ^ 40 * 364654 * 2
def baseEnd_364654 : Nat := 187242774584721523247993

theorem tailTrace_364654 : CollatzResearch.WordTrace tailWord_364654 prefixEnd_364654 187242774584721523247993 := by
  unfold tailWord_364654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662503002616038848763627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8866682680618873860072677 1662503002616038848763627)
  ·
    refine ⟨2493754503924058273145441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1662503002616038848763627 2493754503924058273145441)
    ·
      refine ⟨1870315877943043704859081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2493754503924058273145441 1870315877943043704859081)
      ·
        refine ⟨1402736908457282778644311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1870315877943043704859081 1402736908457282778644311)
        ·
          refine ⟨2104105362685924167966467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402736908457282778644311 2104105362685924167966467)
          ·
            refine ⟨3156158044028886251949701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104105362685924167966467 3156158044028886251949701)
            ·
              refine ⟨591779633255416172240569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3156158044028886251949701 591779633255416172240569)
              ·
                refine ⟨443834724941562129180427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591779633255416172240569 443834724941562129180427)
                ·
                  refine ⟨665752087412343193770641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443834724941562129180427 665752087412343193770641)
                  ·
                    refine ⟨499314065559257395327981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 665752087412343193770641 499314065559257395327981)
                    ·
                      refine ⟨187242774584721523247993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 499314065559257395327981 187242774584721523247993)
                      ·
                        rfl

theorem cell23_364654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_364654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364654 prefixEnd_364654 := by exact prefixLift 364654
  have htrace : WordTrace (prefixWord ++ tailWord_364654) baseStart_364654 baseEnd_364654 := by
    simpa [prefixWord, tailWord_364654, baseEnd_364654] using wordTrace_append hprefix tailTrace_364654
  have hstable : (prefixWord ++ tailWord_364654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364654).length < 2 ^ (prefixWord ++ tailWord_364654).sum := by decide
  have hdescent : baseEnd_364654 < baseStart_364654 := by decide
  rcases family_descends (prefixWord ++ tailWord_364654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364668 : List Nat := [2, 2, 2, 1, 1, 6, 1, 3, 1, 2, 2]
def baseStart_364668 : Nat := 118140960795 + 364668 * 2 ^ 59
def prefixEnd_364668 : Nat := 4983230072969 + 3 ^ 40 * 364668 * 2
def baseEnd_364668 : Nat := 187249963313884468472929

theorem tailTrace_364668 : CollatzResearch.WordTrace tailWord_364668 prefixEnd_364668 187249963313884468472929 := by
  unfold tailWord_364668
  simp only [CollatzResearch.WordTrace]
  refine ⟨6650267321438795590559329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8867023095251727454079105 6650267321438795590559329)
  ·
    refine ⟨4987700491079096692919497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6650267321438795590559329 4987700491079096692919497)
    ·
      refine ⟨3740775368309322519689623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4987700491079096692919497 3740775368309322519689623)
      ·
        refine ⟨5611163052463983779534435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3740775368309322519689623 5611163052463983779534435)
        ·
          refine ⟨8416744578695975669301653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5611163052463983779534435 8416744578695975669301653)
          ·
            refine ⟨394534902126373859498515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8416744578695975669301653 394534902126373859498515)
            ·
              refine ⟨591802353189560789247773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394534902126373859498515 591802353189560789247773)
              ·
                refine ⟨221925882446085295967915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 591802353189560789247773 221925882446085295967915)
                ·
                  refine ⟨332888823669127943951873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221925882446085295967915 332888823669127943951873)
                  ·
                    refine ⟨249666617751845957963905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 332888823669127943951873 249666617751845957963905)
                    ·
                      refine ⟨187249963313884468472929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249666617751845957963905 187249963313884468472929)
                      ·
                        rfl

theorem cell23_364668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_364668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364668 prefixEnd_364668 := by exact prefixLift 364668
  have htrace : WordTrace (prefixWord ++ tailWord_364668) baseStart_364668 baseEnd_364668 := by
    simpa [prefixWord, tailWord_364668, baseEnd_364668] using wordTrace_append hprefix tailTrace_364668
  have hstable : (prefixWord ++ tailWord_364668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364668).length < 2 ^ (prefixWord ++ tailWord_364668).sum := by decide
  have hdescent : baseEnd_364668 < baseStart_364668 := by decide
  rcases family_descends (prefixWord ++ tailWord_364668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364700 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 1, 8]
def baseStart_364700 : Nat := 118140960795 + 364700 * 2 ^ 59
def prefixEnd_364700 : Nat := 4983230072969 + 3 ^ 40 * 364700 * 2
def baseEnd_364700 : Nat := 62422131564942781090927

theorem tailTrace_364700 : CollatzResearch.WordTrace tailWord_364700 prefixEnd_364700 62422131564942781090927 := by
  unfold tailWord_364700
  simp only [CollatzResearch.WordTrace]
  refine ⟨6650850889380830323141777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8867801185841107097522369 6650850889380830323141777)
  ·
    refine ⟨4988138167035622742356333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6650850889380830323141777 4988138167035622742356333)
    ·
      refine ⟨1870551812638358528383625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4988138167035622742356333 1870551812638358528383625)
      ·
        refine ⟨1402913859478768896287719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1870551812638358528383625 1402913859478768896287719)
        ·
          refine ⟨2104370789218153344431579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402913859478768896287719 2104370789218153344431579)
          ·
            refine ⟨3156556183827230016647369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104370789218153344431579 3156556183827230016647369)
            ·
              refine ⟨2367417137870422512485527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3156556183827230016647369 2367417137870422512485527)
              ·
                refine ⟨3551125706805633768728291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2367417137870422512485527 3551125706805633768728291)
                ·
                  refine ⟨5326688560208450653092437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551125706805633768728291 5326688560208450653092437)
                  ·
                    refine ⟨62422131564942781090927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5326688560208450653092437 62422131564942781090927)
                    ·
                      rfl

theorem cell23_364700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_364700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364700 prefixEnd_364700 := by exact prefixLift 364700
  have htrace : WordTrace (prefixWord ++ tailWord_364700) baseStart_364700 baseEnd_364700 := by
    simpa [prefixWord, tailWord_364700, baseEnd_364700] using wordTrace_append hprefix tailTrace_364700
  have hstable : (prefixWord ++ tailWord_364700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364700).length < 2 ^ (prefixWord ++ tailWord_364700).sum := by decide
  have hdescent : baseEnd_364700 < baseStart_364700 := by decide
  rcases family_descends (prefixWord ++ tailWord_364700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364701 : List Nat := [1, 4, 2, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_364701 : Nat := 118140960795 + 364701 * 2 ^ 59
def prefixEnd_364701 : Nat := 4983230072969 + 3 ^ 40 * 364701 * 2
def baseEnd_364701 : Nat := 187266908175482839360277

theorem tailTrace_364701 : CollatzResearch.WordTrace tailWord_364701 prefixEnd_364701 187266908175482839360277 := by
  unfold tailWord_364701
  simp only [CollatzResearch.WordTrace]
  refine ⟨13301738251758037817069957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8867825501172025211379971 13301738251758037817069957)
  ·
    refine ⟨2494075922204632090700617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13301738251758037817069957 2494075922204632090700617)
    ·
      refine ⟨1870556941653474068025463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2494075922204632090700617 1870556941653474068025463)
      ·
        refine ⟨2805835412480211102038195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1870556941653474068025463 2805835412480211102038195)
        ·
          refine ⟨4208753118720316653057293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2805835412480211102038195 4208753118720316653057293)
          ·
            refine ⟨1578282419520118744896485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4208753118720316653057293 1578282419520118744896485)
            ·
              refine ⟨295927953660022264668091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1578282419520118744896485 295927953660022264668091)
              ·
                refine ⟨443891930490033397002137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295927953660022264668091 443891930490033397002137)
                ·
                  refine ⟨332918947867525047751603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443891930490033397002137 332918947867525047751603)
                  ·
                    refine ⟨499378421801287571627405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 332918947867525047751603 499378421801287571627405)
                    ·
                      refine ⟨187266908175482839360277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 499378421801287571627405 187266908175482839360277)
                      ·
                        rfl

theorem cell23_364701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_364701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364701 prefixEnd_364701 := by exact prefixLift 364701
  have htrace : WordTrace (prefixWord ++ tailWord_364701) baseStart_364701 baseEnd_364701 := by
    simpa [prefixWord, tailWord_364701, baseEnd_364701] using wordTrace_append hprefix tailTrace_364701
  have hstable : (prefixWord ++ tailWord_364701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364701).length < 2 ^ (prefixWord ++ tailWord_364701).sum := by decide
  have hdescent : baseEnd_364701 < baseStart_364701 := by decide
  rcases family_descends (prefixWord ++ tailWord_364701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364711 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_364711 : Nat := 118140960795 + 364711 * 2 ^ 59
def prefixEnd_364711 : Nat := 4983230072969 + 3 ^ 40 * 364711 * 2
def baseEnd_364711 : Nat := 187272042982027800235231

theorem tailTrace_364711 : CollatzResearch.WordTrace tailWord_364711 prefixEnd_364711 187272042982027800235231 := by
  unfold tailWord_364711
  simp only [CollatzResearch.WordTrace]
  refine ⟨13302102981721809524933987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8868068654481206349955991 13302102981721809524933987)
  ·
    refine ⟨19953154472582714287400981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13302102981721809524933987 19953154472582714287400981)
    ·
      refine ⟨935304115902314732221921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19953154472582714287400981 935304115902314732221921)
      ·
        refine ⟨701478086926736049166441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 935304115902314732221921 701478086926736049166441)
        ·
          refine ⟨526108565195052036874831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701478086926736049166441 526108565195052036874831)
          ·
            refine ⟨789162847792578055312247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526108565195052036874831 789162847792578055312247)
            ·
              refine ⟨1183744271688867082968371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789162847792578055312247 1183744271688867082968371)
              ·
                refine ⟨1775616407533300624452557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1183744271688867082968371 1775616407533300624452557)
                ·
                  refine ⟨665856152824987734169709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1775616407533300624452557 665856152824987734169709)
                  ·
                    refine ⟨249696057309370400313641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 665856152824987734169709 249696057309370400313641)
                    ·
                      refine ⟨187272042982027800235231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249696057309370400313641 187272042982027800235231)
                      ·
                        rfl

theorem cell23_364711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_364711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364711 prefixEnd_364711 := by exact prefixLift 364711
  have htrace : WordTrace (prefixWord ++ tailWord_364711) baseStart_364711 baseEnd_364711 := by
    simpa [prefixWord, tailWord_364711, baseEnd_364711] using wordTrace_append hprefix tailTrace_364711
  have hstable : (prefixWord ++ tailWord_364711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364711).length < 2 ^ (prefixWord ++ tailWord_364711).sum := by decide
  have hdescent : baseEnd_364711 < baseStart_364711 := by decide
  rcases family_descends (prefixWord ++ tailWord_364711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364747 : List Nat := [1, 1, 1, 1, 3, 2, 5, 4, 5]
def baseStart_364747 : Nat := 118140960795 + 364747 * 2 ^ 59
def prefixEnd_364747 : Nat := 4983230072969 + 3 ^ 40 * 364747 * 2
def baseEnd_364747 : Nat := 20810058698398851042785

theorem tailTrace_364747 : CollatzResearch.WordTrace tailWord_364747 prefixEnd_364747 20810058698398851042785 := by
  unfold tailWord_364747
  simp only [CollatzResearch.WordTrace]
  refine ⟨13303416009591387673244495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8868944006394258448829663 13303416009591387673244495)
  ·
    refine ⟨19955124014387081509866743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13303416009591387673244495 19955124014387081509866743)
    ·
      refine ⟨29932686021580622264800115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19955124014387081509866743 29932686021580622264800115)
      ·
        refine ⟨44899029032370933397200173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29932686021580622264800115 44899029032370933397200173)
        ·
          refine ⟨16837135887139100023950065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44899029032370933397200173 16837135887139100023950065)
          ·
            refine ⟨12627851915354325017962549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16837135887139100023950065 12627851915354325017962549)
            ·
              refine ⟨1183861117064467970433989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12627851915354325017962549 1183861117064467970433989)
              ·
                refine ⟨221973959449587744456373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1183861117064467970433989 221973959449587744456373)
                ·
                  refine ⟨20810058698398851042785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221973959449587744456373 20810058698398851042785)
                  ·
                    rfl

theorem cell23_364747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 5].length) (baseStart_364747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364747 prefixEnd_364747 := by exact prefixLift 364747
  have htrace : WordTrace (prefixWord ++ tailWord_364747) baseStart_364747 baseEnd_364747 := by
    simpa [prefixWord, tailWord_364747, baseEnd_364747] using wordTrace_append hprefix tailTrace_364747
  have hstable : (prefixWord ++ tailWord_364747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364747).length < 2 ^ (prefixWord ++ tailWord_364747).sum := by decide
  have hdescent : baseEnd_364747 < baseStart_364747 := by decide
  rcases family_descends (prefixWord ++ tailWord_364747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364758 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_364758 : Nat := 118140960795 + 364758 * 2 ^ 59
def prefixEnd_364758 : Nat := 4983230072969 + 3 ^ 40 * 364758 * 2
def baseEnd_364758 : Nat := 187296176572789116347515

theorem tailTrace_364758 : CollatzResearch.WordTrace tailWord_364758 prefixEnd_364758 187296176572789116347515 := by
  unfold tailWord_364758
  simp only [CollatzResearch.WordTrace]
  refine ⟨831488575784471034493433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8869211475034357701263285 831488575784471034493433)
  ·
    refine ⟨623616431838353275870075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 831488575784471034493433 623616431838353275870075)
    ·
      refine ⟨935424647757529913805113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623616431838353275870075 935424647757529913805113)
      ·
        refine ⟨701568485818147435353835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 935424647757529913805113 701568485818147435353835)
        ·
          refine ⟨1052352728727221153030753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701568485818147435353835 1052352728727221153030753)
          ·
            refine ⟨789264546545415864773065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052352728727221153030753 789264546545415864773065)
            ·
              refine ⟨591948409909061898579799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789264546545415864773065 591948409909061898579799)
              ·
                refine ⟨887922614863592847869699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591948409909061898579799 887922614863592847869699)
                ·
                  refine ⟨1331883922295389271804549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887922614863592847869699 1331883922295389271804549)
                  ·
                    refine ⟨249728235430385488463353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1331883922295389271804549 249728235430385488463353)
                    ·
                      refine ⟨187296176572789116347515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249728235430385488463353 187296176572789116347515)
                      ·
                        rfl

theorem cell23_364758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_364758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364758 prefixEnd_364758 := by exact prefixLift 364758
  have htrace : WordTrace (prefixWord ++ tailWord_364758) baseStart_364758 baseEnd_364758 := by
    simpa [prefixWord, tailWord_364758, baseEnd_364758] using wordTrace_append hprefix tailTrace_364758
  have hstable : (prefixWord ++ tailWord_364758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364758).length < 2 ^ (prefixWord ++ tailWord_364758).sum := by decide
  have hdescent : baseEnd_364758 < baseStart_364758 := by decide
  rcases family_descends (prefixWord ++ tailWord_364758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364767 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 4, 5, 2]
def baseStart_364767 : Nat := 118140960795 + 364767 * 2 ^ 59
def prefixEnd_364767 : Nat := 4983230072969 + 3 ^ 40 * 364767 * 2
def baseEnd_364767 : Nat := 187300797898679581134973

theorem tailTrace_364767 : CollatzResearch.WordTrace tailWord_364767 prefixEnd_364767 187300797898679581134973 := by
  unfold tailWord_364767
  simp only [CollatzResearch.WordTrace]
  refine ⟨13304145469518931088972555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8869430313012620725981703 13304145469518931088972555)
  ·
    refine ⟨19956218204278396633458833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13304145469518931088972555 19956218204278396633458833)
    ·
      refine ⟨14967163653208797475094125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19956218204278396633458833 14967163653208797475094125)
      ·
        refine ⟨5612686369953299053160297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14967163653208797475094125 5612686369953299053160297)
        ·
          refine ⟨4209514777464974289870223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5612686369953299053160297 4209514777464974289870223)
          ·
            refine ⟨6314272166197461434805335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4209514777464974289870223 6314272166197461434805335)
            ·
              refine ⟨9471408249296192152208003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6314272166197461434805335 9471408249296192152208003)
              ·
                refine ⟨14207112373944288228312005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9471408249296192152208003 14207112373944288228312005)
                ·
                  refine ⟨2663833570114554042808501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14207112373944288228312005 2663833570114554042808501)
                  ·
                    refine ⟨249734397198239441513297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2663833570114554042808501 249734397198239441513297)
                    ·
                      refine ⟨187300797898679581134973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249734397198239441513297 187300797898679581134973)
                      ·
                        rfl

theorem cell23_364767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_364767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364767 prefixEnd_364767 := by exact prefixLift 364767
  have htrace : WordTrace (prefixWord ++ tailWord_364767) baseStart_364767 baseEnd_364767 := by
    simpa [prefixWord, tailWord_364767, baseEnd_364767] using wordTrace_append hprefix tailTrace_364767
  have hstable : (prefixWord ++ tailWord_364767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364767).length < 2 ^ (prefixWord ++ tailWord_364767).sum := by decide
  have hdescent : baseEnd_364767 < baseStart_364767 := by decide
  rcases family_descends (prefixWord ++ tailWord_364767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364781 : List Nat := [1, 5, 1, 2, 3, 1, 2, 3, 5]
def baseStart_364781 : Nat := 118140960795 + 364781 * 2 ^ 59
def prefixEnd_364781 : Nat := 4983230072969 + 3 ^ 40 * 364781 * 2
def baseEnd_364781 : Nat := 20811998514204725151101

theorem tailTrace_364781 : CollatzResearch.WordTrace tailWord_364781 prefixEnd_364781 20811998514204725151101 := by
  unfold tailWord_364781
  simp only [CollatzResearch.WordTrace]
  refine ⟨13304656091468211479982197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8869770727645474319988131 13304656091468211479982197)
  ·
    refine ⟨1247311508575144826248331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13304656091468211479982197 1247311508575144826248331)
    ·
      refine ⟨1870967262862717239372497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1247311508575144826248331 1870967262862717239372497)
      ·
        refine ⟨1403225447147037929529373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1870967262862717239372497 1403225447147037929529373)
        ·
          refine ⟨526209542680139223573515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1403225447147037929529373 526209542680139223573515)
          ·
            refine ⟨789314314020208835360273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526209542680139223573515 789314314020208835360273)
            ·
              refine ⟨591985735515156626520205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789314314020208835360273 591985735515156626520205)
              ·
                refine ⟨221994650818183734945077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 591985735515156626520205 221994650818183734945077)
                ·
                  refine ⟨20811998514204725151101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221994650818183734945077 20811998514204725151101)
                  ·
                    rfl

theorem cell23_364781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_364781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364781 prefixEnd_364781 := by exact prefixLift 364781
  have htrace : WordTrace (prefixWord ++ tailWord_364781) baseStart_364781 baseEnd_364781 := by
    simpa [prefixWord, tailWord_364781, baseEnd_364781] using wordTrace_append hprefix tailTrace_364781
  have hstable : (prefixWord ++ tailWord_364781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364781).length < 2 ^ (prefixWord ++ tailWord_364781).sum := by decide
  have hdescent : baseEnd_364781 < baseStart_364781 := by decide
  rcases family_descends (prefixWord ++ tailWord_364781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364797 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_364797 : Nat := 118140960795 + 364797 * 2 ^ 59
def prefixEnd_364797 : Nat := 4983230072969 + 3 ^ 40 * 364797 * 2
def baseEnd_364797 : Nat := 187316202318314463759835

theorem tailTrace_364797 : CollatzResearch.WordTrace tailWord_364797 prefixEnd_364797 187316202318314463759835 := by
  unfold tailWord_364797
  simp only [CollatzResearch.WordTrace]
  refine ⟨13305239659410246212564645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8870159772940164141709763 13305239659410246212564645)
  ·
    refine ⟨2494732436139421164855871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13305239659410246212564645 2494732436139421164855871)
    ·
      refine ⟨3742098654209131747283807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2494732436139421164855871 3742098654209131747283807)
      ·
        refine ⟨5613147981313697620925711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3742098654209131747283807 5613147981313697620925711)
        ·
          refine ⟨8419721971970546431388567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5613147981313697620925711 8419721971970546431388567)
          ·
            refine ⟨12629582957955819647082851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8419721971970546431388567 12629582957955819647082851)
            ·
              refine ⟨18944374436933729470624277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12629582957955819647082851 18944374436933729470624277)
              ·
                refine ⟨888017551731268568935513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18944374436933729470624277 888017551731268568935513)
                ·
                  refine ⟨666013163798451426701635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 888017551731268568935513 666013163798451426701635)
                  ·
                    refine ⟨999019745697677140052453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 666013163798451426701635 999019745697677140052453)
                    ·
                      refine ⟨187316202318314463759835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 999019745697677140052453 187316202318314463759835)
                      ·
                        rfl

theorem cell23_364797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_364797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364797 prefixEnd_364797 := by exact prefixLift 364797
  have htrace : WordTrace (prefixWord ++ tailWord_364797) baseStart_364797 baseEnd_364797 := by
    simpa [prefixWord, tailWord_364797, baseEnd_364797] using wordTrace_append hprefix tailTrace_364797
  have hstable : (prefixWord ++ tailWord_364797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364797).length < 2 ^ (prefixWord ++ tailWord_364797).sum := by decide
  have hdescent : baseEnd_364797 < baseStart_364797 := by decide
  rcases family_descends (prefixWord ++ tailWord_364797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364800 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 5]
def baseStart_364800 : Nat := 118140960795 + 364800 * 2 ^ 59
def prefixEnd_364800 : Nat := 4983230072969 + 3 ^ 40 * 364800 * 2
def baseEnd_364800 : Nat := 187317742760277952022321

theorem tailTrace_364800 : CollatzResearch.WordTrace tailWord_364800 prefixEnd_364800 187317742760277952022321 := by
  unfold tailWord_364800
  simp only [CollatzResearch.WordTrace]
  refine ⟨6652674539199688862461927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8870232718932918483282569 6652674539199688862461927)
  ·
    refine ⟨9979011808799533293692891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6652674539199688862461927 9979011808799533293692891)
    ·
      refine ⟨14968517713199299940539337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9979011808799533293692891 14968517713199299940539337)
      ·
        refine ⟨11226388284899474955404503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14968517713199299940539337 11226388284899474955404503)
        ·
          refine ⟨16839582427349212433106755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11226388284899474955404503 16839582427349212433106755)
          ·
            refine ⟨25259373641023818649660133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16839582427349212433106755 25259373641023818649660133)
            ·
              refine ⟨4736132557691965996811275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25259373641023818649660133 4736132557691965996811275)
              ·
                refine ⟨7104198836537948995216913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736132557691965996811275 7104198836537948995216913)
                ·
                  refine ⟨5328149127403461746412685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7104198836537948995216913 5328149127403461746412685)
                  ·
                    refine ⟨1998055922776298154904757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5328149127403461746412685 1998055922776298154904757)
                    ·
                      refine ⟨187317742760277952022321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1998055922776298154904757 187317742760277952022321)
                      ·
                        rfl

theorem cell23_364800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_364800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364800 prefixEnd_364800 := by exact prefixLift 364800
  have htrace : WordTrace (prefixWord ++ tailWord_364800) baseStart_364800 baseEnd_364800 := by
    simpa [prefixWord, tailWord_364800, baseEnd_364800] using wordTrace_append hprefix tailTrace_364800
  have hstable : (prefixWord ++ tailWord_364800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364800).length < 2 ^ (prefixWord ++ tailWord_364800).sum := by decide
  have hdescent : baseEnd_364800 < baseStart_364800 := by decide
  rcases family_descends (prefixWord ++ tailWord_364800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364814 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2]
def baseStart_364814 : Nat := 118140960795 + 364814 * 2 ^ 59
def prefixEnd_364814 : Nat := 4983230072969 + 3 ^ 40 * 364814 * 2
def baseEnd_364814 : Nat := 187324931489440897247257

theorem tailTrace_364814 : CollatzResearch.WordTrace tailWord_364814 prefixEnd_364814 187324931489440897247257 := by
  unfold tailWord_364814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1663232462543582264491687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8870573133565772077288997 1663232462543582264491687)
  ·
    refine ⟨2494848693815373396737531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1663232462543582264491687 2494848693815373396737531)
    ·
      refine ⟨3742273040723060095106297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2494848693815373396737531 3742273040723060095106297)
      ·
        refine ⟨2806704780542295071329723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3742273040723060095106297 2806704780542295071329723)
        ·
          refine ⟨4210057170813442606994585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2806704780542295071329723 4210057170813442606994585)
          ·
            refine ⟨3157542878110081955245939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4210057170813442606994585 3157542878110081955245939)
            ·
              refine ⟨4736314317165122932868909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157542878110081955245939 4736314317165122932868909)
              ·
                refine ⟨1776117868936921099825841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4736314317165122932868909 1776117868936921099825841)
                ·
                  refine ⟨1332088401702690824869381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1776117868936921099825841 1332088401702690824869381)
                  ·
                    refine ⟨249766575319254529663009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1332088401702690824869381 249766575319254529663009)
                    ·
                      refine ⟨187324931489440897247257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249766575319254529663009 187324931489440897247257)
                      ·
                        rfl

theorem cell23_364814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_364814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364814 prefixEnd_364814 := by exact prefixLift 364814
  have htrace : WordTrace (prefixWord ++ tailWord_364814) baseStart_364814 baseEnd_364814 := by
    simpa [prefixWord, tailWord_364814, baseEnd_364814] using wordTrace_append hprefix tailTrace_364814
  have hstable : (prefixWord ++ tailWord_364814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364814).length < 2 ^ (prefixWord ++ tailWord_364814).sum := by decide
  have hdescent : baseEnd_364814 < baseStart_364814 := by decide
  rcases family_descends (prefixWord ++ tailWord_364814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364817 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 3]
def baseStart_364817 : Nat := 118140960795 + 364817 * 2 ^ 59
def prefixEnd_364817 : Nat := 4983230072969 + 3 ^ 40 * 364817 * 2
def baseEnd_364817 : Nat := 187326471931404385509743

theorem tailTrace_364817 : CollatzResearch.WordTrace tailWord_364817 prefixEnd_364817 187326471931404385509743 := by
  unfold tailWord_364817
  simp only [CollatzResearch.WordTrace]
  refine ⟨13305969119337789628292705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8870646079558526418861803 13305969119337789628292705)
  ·
    refine ⟨9979476839503342221219529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13305969119337789628292705 9979476839503342221219529)
    ·
      refine ⟨7484607629627506665914647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9979476839503342221219529 7484607629627506665914647)
      ·
        refine ⟨11226911444441259998871971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7484607629627506665914647 11226911444441259998871971)
        ·
          refine ⟨16840367166661889998307957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11226911444441259998871971 16840367166661889998307957)
          ·
            refine ⟨1578784421874552187341371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16840367166661889998307957 1578784421874552187341371)
            ·
              refine ⟨2368176632811828281012057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578784421874552187341371 2368176632811828281012057)
              ·
                refine ⟨1776132474608871210759043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2368176632811828281012057 1776132474608871210759043)
                ·
                  refine ⟨2664198711913306816138565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776132474608871210759043 2664198711913306816138565)
                  ·
                    refine ⟨499537258483745028025981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2664198711913306816138565 499537258483745028025981)
                    ·
                      refine ⟨187326471931404385509743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 499537258483745028025981 187326471931404385509743)
                      ·
                        rfl

theorem cell23_364817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_364817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364817 prefixEnd_364817 := by exact prefixLift 364817
  have htrace : WordTrace (prefixWord ++ tailWord_364817) baseStart_364817 baseEnd_364817 := by
    simpa [prefixWord, tailWord_364817, baseEnd_364817] using wordTrace_append hprefix tailTrace_364817
  have hstable : (prefixWord ++ tailWord_364817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364817).length < 2 ^ (prefixWord ++ tailWord_364817).sum := by decide
  have hdescent : baseEnd_364817 < baseStart_364817 := by decide
  rcases family_descends (prefixWord ++ tailWord_364817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364834 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_364834 : Nat := 118140960795 + 364834 * 2 ^ 59
def prefixEnd_364834 : Nat := 4983230072969 + 3 ^ 40 * 364834 * 2
def baseEnd_364834 : Nat := 187335201102530818997165

theorem tailTrace_364834 : CollatzResearch.WordTrace tailWord_364834 prefixEnd_364834 187335201102530818997165 := by
  unfold tailWord_364834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3326647290069050382915389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8871059440184134354441037 3326647290069050382915389)
  ·
    refine ⟨1247492733775893893593271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3326647290069050382915389 1247492733775893893593271)
    ·
      refine ⟨1871239100663840840389907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1247492733775893893593271 1871239100663840840389907)
      ·
        refine ⟨2806858650995761260584861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1871239100663840840389907 2806858650995761260584861)
        ·
          refine ⟨1052571994123410472719323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2806858650995761260584861 1052571994123410472719323)
          ·
            refine ⟨1578857991185115709078985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052571994123410472719323 1578857991185115709078985)
            ·
              refine ⟨1184143493388836781809239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1578857991185115709078985 1184143493388836781809239)
              ·
                refine ⟨1776215240083255172713859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184143493388836781809239 1776215240083255172713859)
                ·
                  refine ⟨2664322860124882759070789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776215240083255172713859 2664322860124882759070789)
                  ·
                    refine ⟨499560536273415517325773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2664322860124882759070789 499560536273415517325773)
                    ·
                      refine ⟨187335201102530818997165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 499560536273415517325773 187335201102530818997165)
                      ·
                        rfl

theorem cell23_364834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_364834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364834 prefixEnd_364834 := by exact prefixLift 364834
  have htrace : WordTrace (prefixWord ++ tailWord_364834) baseStart_364834 baseEnd_364834 := by
    simpa [prefixWord, tailWord_364834, baseEnd_364834] using wordTrace_append hprefix tailTrace_364834
  have hstable : (prefixWord ++ tailWord_364834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364834).length < 2 ^ (prefixWord ++ tailWord_364834).sum := by decide
  have hdescent : baseEnd_364834 < baseStart_364834 := by decide
  rcases family_descends (prefixWord ++ tailWord_364834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364858 : List Nat := [3, 1, 1, 1, 4, 3, 3, 2, 1, 4]
def baseStart_364858 : Nat := 118140960795 + 364858 * 2 ^ 59
def prefixEnd_364858 : Nat := 4983230072969 + 3 ^ 40 * 364858 * 2
def baseEnd_364858 : Nat := 62449174879412908365685

theorem tailTrace_364858 : CollatzResearch.WordTrace tailWord_364858 prefixEnd_364858 62449174879412908365685 := by
  unfold tailWord_364858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3326866128047313407633807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8871643008126169087023485 3326866128047313407633807)
  ·
    refine ⟨4990299192070970111450711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3326866128047313407633807 4990299192070970111450711)
    ·
      refine ⟨7485448788106455167176067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4990299192070970111450711 7485448788106455167176067)
      ·
        refine ⟨11228173182159682750764101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7485448788106455167176067 11228173182159682750764101)
        ·
          refine ⟨2105282471654940515768269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11228173182159682750764101 2105282471654940515768269)
          ·
            refine ⟨789480926870602693413101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2105282471654940515768269 789480926870602693413101)
            ·
              refine ⟨296055347576476010029913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 789480926870602693413101 296055347576476010029913)
              ·
                refine ⟨222041510682357007522435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296055347576476010029913 222041510682357007522435)
                ·
                  refine ⟨333062266023535511283653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222041510682357007522435 333062266023535511283653)
                  ·
                    refine ⟨62449174879412908365685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 333062266023535511283653 62449174879412908365685)
                    ·
                      rfl

theorem cell23_364858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_364858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364858 prefixEnd_364858 := by exact prefixLift 364858
  have htrace : WordTrace (prefixWord ++ tailWord_364858) baseStart_364858 baseEnd_364858 := by
    simpa [prefixWord, tailWord_364858, baseEnd_364858] using wordTrace_append hprefix tailTrace_364858
  have hstable : (prefixWord ++ tailWord_364858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364858).length < 2 ^ (prefixWord ++ tailWord_364858).sum := by decide
  have hdescent : baseEnd_364858 < baseStart_364858 := by decide
  rcases family_descends (prefixWord ++ tailWord_364858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364864 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 3, 1, 3]
def baseStart_364864 : Nat := 118140960795 + 364864 * 2 ^ 59
def prefixEnd_364864 : Nat := 4983230072969 + 3 ^ 40 * 364864 * 2
def baseEnd_364864 : Nat := 187350605522165701622027

theorem tailTrace_364864 : CollatzResearch.WordTrace tailWord_364864 prefixEnd_364864 187350605522165701622027 := by
  unfold tailWord_364864
  simp only [CollatzResearch.WordTrace]
  refine ⟨6653841675083758327626823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8871788900111677770169097 6653841675083758327626823)
  ·
    refine ⟨9980762512625637491440235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6653841675083758327626823 9980762512625637491440235)
    ·
      refine ⟨14971143768938456237160353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9980762512625637491440235 14971143768938456237160353)
      ·
        refine ⟨11228357826703842177870265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14971143768938456237160353 11228357826703842177870265)
        ·
          refine ⟨8421268370027881633402699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11228357826703842177870265 8421268370027881633402699)
          ·
            refine ⟨12631902555041822450104049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8421268370027881633402699 12631902555041822450104049)
            ·
              refine ⟨9473926916281366837578037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12631902555041822450104049 9473926916281366837578037)
              ·
                refine ⟨888180648401378141022941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9473926916281366837578037 888180648401378141022941)
                ·
                  refine ⟨333067743150516802883603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888180648401378141022941 333067743150516802883603)
                  ·
                    refine ⟨499601614725775204325405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 333067743150516802883603 499601614725775204325405)
                    ·
                      refine ⟨187350605522165701622027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 499601614725775204325405 187350605522165701622027)
                      ·
                        rfl

theorem cell23_364864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_364864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364864 prefixEnd_364864 := by exact prefixLift 364864
  have htrace : WordTrace (prefixWord ++ tailWord_364864) baseStart_364864 baseEnd_364864 := by
    simpa [prefixWord, tailWord_364864, baseEnd_364864] using wordTrace_append hprefix tailTrace_364864
  have hstable : (prefixWord ++ tailWord_364864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364864).length < 2 ^ (prefixWord ++ tailWord_364864).sum := by decide
  have hdescent : baseEnd_364864 < baseStart_364864 := by decide
  rcases family_descends (prefixWord ++ tailWord_364864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364884 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_364884 : Nat := 118140960795 + 364884 * 2 ^ 59
def prefixEnd_364884 : Nat := 4983230072969 + 3 ^ 40 * 364884 * 2
def baseEnd_364884 : Nat := 62453625045085207790645

theorem tailTrace_364884 : CollatzResearch.WordTrace tailWord_364884 prefixEnd_364884 62453625045085207790645 := by
  unfold tailWord_364884
  simp only [CollatzResearch.WordTrace]
  refine ⟨6654206405047530035490853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8872275206730040047321137 6654206405047530035490853)
  ·
    refine ⟨1247663700946411881654535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6654206405047530035490853 1247663700946411881654535)
    ·
      refine ⟨1871495551419617822481803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1247663700946411881654535 1871495551419617822481803)
      ·
        refine ⟨2807243327129426733722705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1871495551419617822481803 2807243327129426733722705)
        ·
          refine ⟨2105432495347070050292029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2807243327129426733722705 2105432495347070050292029)
          ·
            refine ⟨789537185755151268859511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2105432495347070050292029 789537185755151268859511)
            ·
              refine ⟨1184305778632726903289267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789537185755151268859511 1184305778632726903289267)
              ·
                refine ⟨1776458667949090354933901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184305778632726903289267 1776458667949090354933901)
                ·
                  refine ⟨666172000480908883100213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1776458667949090354933901 666172000480908883100213)
                  ·
                    refine ⟨62453625045085207790645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 666172000480908883100213 62453625045085207790645)
                    ·
                      rfl

theorem cell23_364884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_364884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364884 prefixEnd_364884 := by exact prefixLift 364884
  have htrace : WordTrace (prefixWord ++ tailWord_364884) baseStart_364884 baseEnd_364884 := by
    simpa [prefixWord, tailWord_364884, baseEnd_364884] using wordTrace_append hprefix tailTrace_364884
  have hstable : (prefixWord ++ tailWord_364884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364884).length < 2 ^ (prefixWord ++ tailWord_364884).sum := by decide
  have hdescent : baseEnd_364884 < baseStart_364884 := by decide
  rcases family_descends (prefixWord ++ tailWord_364884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364901 : List Nat := [1, 3, 1, 3, 1, 4, 3, 1, 1, 5]
def baseStart_364901 : Nat := 118140960795 + 364901 * 2 ^ 59
def prefixEnd_364901 : Nat := 4983230072969 + 3 ^ 40 * 364901 * 2
def baseEnd_364901 : Nat := 62456534768794018953119

theorem tailTrace_364901 : CollatzResearch.WordTrace tailWord_364901 prefixEnd_364901 62456534768794018953119 := by
  unfold tailWord_364901
  simp only [CollatzResearch.WordTrace]
  refine ⟨13309032851033471974350557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8872688567355647982900371 13309032851033471974350557)
  ·
    refine ⟨4990887319137551990381459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13309032851033471974350557 4990887319137551990381459)
    ·
      refine ⟨7486330978706327985572189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4990887319137551990381459 7486330978706327985572189)
      ·
        refine ⟨2807374117014872994589571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7486330978706327985572189 2807374117014872994589571)
        ·
          refine ⟨4211061175522309491884357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807374117014872994589571 4211061175522309491884357)
          ·
            refine ⟨789573970410433029728317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4211061175522309491884357 789573970410433029728317)
            ·
              refine ⟨296090238903912386148119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 789573970410433029728317 296090238903912386148119)
              ·
                refine ⟨444135358355868579222179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296090238903912386148119 444135358355868579222179)
                ·
                  refine ⟨666203037533802868833269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444135358355868579222179 666203037533802868833269)
                  ·
                    refine ⟨62456534768794018953119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 666203037533802868833269 62456534768794018953119)
                    ·
                      rfl

theorem cell23_364901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_364901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364901 prefixEnd_364901 := by exact prefixLift 364901
  have htrace : WordTrace (prefixWord ++ tailWord_364901) baseStart_364901 baseEnd_364901 := by
    simpa [prefixWord, tailWord_364901, baseEnd_364901] using wordTrace_append hprefix tailTrace_364901
  have hstable : (prefixWord ++ tailWord_364901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364901).length < 2 ^ (prefixWord ++ tailWord_364901).sum := by decide
  have hdescent : baseEnd_364901 < baseStart_364901 := by decide
  rcases family_descends (prefixWord ++ tailWord_364901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364921 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 3, 2, 2]
def baseStart_364921 : Nat := 118140960795 + 364921 * 2 ^ 59
def prefixEnd_364921 : Nat := 4983230072969 + 3 ^ 40 * 364921 * 2
def baseEnd_364921 : Nat := 187379873919471978609265

theorem tailTrace_364921 : CollatzResearch.WordTrace tailWord_364921 prefixEnd_364921 187379873919471978609265 := by
  unfold tailWord_364921
  simp only [CollatzResearch.WordTrace]
  refine ⟨13309762310961015390078617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8873174873974010260052411 13309762310961015390078617)
  ·
    refine ⟨9982321733220761542558963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13309762310961015390078617 9982321733220761542558963)
    ·
      refine ⟨14973482599831142313838445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9982321733220761542558963 14973482599831142313838445)
      ·
        refine ⟨5615055974936678367689417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14973482599831142313838445 5615055974936678367689417)
        ·
          refine ⟨4211291981202508775767063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5615055974936678367689417 4211291981202508775767063)
          ·
            refine ⟨6316937971803763163650595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4211291981202508775767063 6316937971803763163650595)
            ·
              refine ⟨9475406957705644745475893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6316937971803763163650595 9475406957705644745475893)
              ·
                refine ⟨888319402284904194888365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9475406957705644745475893 888319402284904194888365)
                ·
                  refine ⟨333119775856839073083137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888319402284904194888365 333119775856839073083137)
                  ·
                    refine ⟨249839831892629304812353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 333119775856839073083137 249839831892629304812353)
                    ·
                      refine ⟨187379873919471978609265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249839831892629304812353 187379873919471978609265)
                      ·
                        rfl

theorem cell23_364921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_364921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364921 prefixEnd_364921 := by exact prefixLift 364921
  have htrace : WordTrace (prefixWord ++ tailWord_364921) baseStart_364921 baseEnd_364921 := by
    simpa [prefixWord, tailWord_364921, baseEnd_364921] using wordTrace_append hprefix tailTrace_364921
  have hstable : (prefixWord ++ tailWord_364921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364921).length < 2 ^ (prefixWord ++ tailWord_364921).sum := by decide
  have hdescent : baseEnd_364921 < baseStart_364921 := by decide
  rcases family_descends (prefixWord ++ tailWord_364921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364988 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_364988 : Nat := 118140960795 + 364988 * 2 ^ 59
def prefixEnd_364988 : Nat := 4983230072969 + 3 ^ 40 * 364988 * 2
def baseEnd_364988 : Nat := 187414277123323216471457

theorem tailTrace_364988 : CollatzResearch.WordTrace tailWord_364988 prefixEnd_364988 187414277123323216471457 := by
  unfold tailWord_364988
  simp only [CollatzResearch.WordTrace]
  refine ⟨6656103000859142916383809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8874804001145523888511745 6656103000859142916383809)
  ·
    refine ⟨4992077250644357187287857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6656103000859142916383809 4992077250644357187287857)
    ·
      refine ⟨3744057937983267890465893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4992077250644357187287857 3744057937983267890465893)
      ·
        refine ⟨702010863371862729462355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3744057937983267890465893 702010863371862729462355)
        ·
          refine ⟨1053016295057794094193533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702010863371862729462355 1053016295057794094193533)
          ·
            refine ⟨394881110646672785322575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1053016295057794094193533 394881110646672785322575)
            ·
              refine ⟨592321665970009177983863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394881110646672785322575 592321665970009177983863)
              ·
                refine ⟨888482498955013766975795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592321665970009177983863 888482498955013766975795)
                ·
                  refine ⟨1332723748432520650463693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888482498955013766975795 1332723748432520650463693)
                  ·
                    refine ⟨499771405662195243923885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1332723748432520650463693 499771405662195243923885)
                    ·
                      refine ⟨187414277123323216471457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 499771405662195243923885 187414277123323216471457)
                      ·
                        rfl

theorem cell23_364988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_364988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364988 prefixEnd_364988 := by exact prefixLift 364988
  have htrace : WordTrace (prefixWord ++ tailWord_364988) baseStart_364988 baseEnd_364988 := by
    simpa [prefixWord, tailWord_364988, baseEnd_364988] using wordTrace_append hprefix tailTrace_364988
  have hstable : (prefixWord ++ tailWord_364988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364988).length < 2 ^ (prefixWord ++ tailWord_364988).sum := by decide
  have hdescent : baseEnd_364988 < baseStart_364988 := by decide
  rcases family_descends (prefixWord ++ tailWord_364988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364997 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_364997 : Nat := 118140960795 + 364997 * 2 ^ 59
def prefixEnd_364997 : Nat := 4983230072969 + 3 ^ 40 * 364997 * 2
def baseEnd_364997 : Nat := 187418898449213681258915

theorem tailTrace_364997 : CollatzResearch.WordTrace tailWord_364997 prefixEnd_364997 187418898449213681258915 := by
  unfold tailWord_364997
  simp only [CollatzResearch.WordTrace]
  refine ⟨13312534258685680369845245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8875022839123786913230163 13312534258685680369845245)
  ·
    refine ⟨4992200347007130138691967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13312534258685680369845245 4992200347007130138691967)
    ·
      refine ⟨7488300520510695208037951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4992200347007130138691967 7488300520510695208037951)
      ·
        refine ⟨11232450780766042812056927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7488300520510695208037951 11232450780766042812056927)
        ·
          refine ⟨16848676171149064218085391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11232450780766042812056927 16848676171149064218085391)
          ·
            refine ⟨25273014256723596327128087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16848676171149064218085391 25273014256723596327128087)
            ·
              refine ⟨37909521385085394490692131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25273014256723596327128087 37909521385085394490692131)
              ·
                refine ⟨56864282077628091736038197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37909521385085394490692131 56864282077628091736038197)
                ·
                  refine ⟨5331026444777633600253581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56864282077628091736038197 5331026444777633600253581)
                  ·
                    refine ⟨1999134916791612600095093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5331026444777633600253581 1999134916791612600095093)
                    ·
                      refine ⟨187418898449213681258915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1999134916791612600095093 187418898449213681258915)
                      ·
                        rfl

theorem cell23_364997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_364997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_364997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_364997 prefixEnd_364997 := by exact prefixLift 364997
  have htrace : WordTrace (prefixWord ++ tailWord_364997) baseStart_364997 baseEnd_364997 := by
    simpa [prefixWord, tailWord_364997, baseEnd_364997] using wordTrace_append hprefix tailTrace_364997
  have hstable : (prefixWord ++ tailWord_364997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364997).length < 2 ^ (prefixWord ++ tailWord_364997).sum := by decide
  have hdescent : baseEnd_364997 < baseStart_364997 := by decide
  rcases family_descends (prefixWord ++ tailWord_364997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365062 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_365062 : Nat := 118140960795 + 365062 * 2 ^ 59
def prefixEnd_365062 : Nat := 4983230072969 + 3 ^ 40 * 365062 * 2
def baseEnd_365062 : Nat := 187452274691755926946117

theorem tailTrace_365062 : CollatzResearch.WordTrace tailWord_365062 prefixEnd_365062 187452274691755926946117 := by
  unfold tailWord_365062
  simp only [CollatzResearch.WordTrace]
  refine ⟨416090781357818639717545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8876603335633464313974293 416090781357818639717545)
  ·
    refine ⟨312068086018363979788159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 416090781357818639717545 312068086018363979788159)
    ·
      refine ⟨468102129027545969682239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312068086018363979788159 468102129027545969682239)
      ·
        refine ⟨702153193541318954523359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468102129027545969682239 702153193541318954523359)
        ·
          refine ⟨1053229790311978431785039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702153193541318954523359 1053229790311978431785039)
          ·
            refine ⟨1579844685467967647677559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053229790311978431785039 1579844685467967647677559)
            ·
              refine ⟨2369767028201951471516339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579844685467967647677559 2369767028201951471516339)
              ·
                refine ⟨3554650542302927207274509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369767028201951471516339 3554650542302927207274509)
                ·
                  refine ⟨1332993953363597702727941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3554650542302927207274509 1332993953363597702727941)
                  ·
                    refine ⟨249936366255674569261489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1332993953363597702727941 249936366255674569261489)
                    ·
                      refine ⟨187452274691755926946117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 249936366255674569261489 187452274691755926946117)
                      ·
                        rfl

theorem cell23_365062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_365062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365062 prefixEnd_365062 := by exact prefixLift 365062
  have htrace : WordTrace (prefixWord ++ tailWord_365062) baseStart_365062 baseEnd_365062 := by
    simpa [prefixWord, tailWord_365062, baseEnd_365062] using wordTrace_append hprefix tailTrace_365062
  have hstable : (prefixWord ++ tailWord_365062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365062).length < 2 ^ (prefixWord ++ tailWord_365062).sum := by decide
  have hdescent : baseEnd_365062 < baseStart_365062 := by decide
  rcases family_descends (prefixWord ++ tailWord_365062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365085 : List Nat := [1, 4, 2, 2, 1, 4, 2, 2, 5]
def baseStart_365085 : Nat := 118140960795 + 365085 * 2 ^ 59
def prefixEnd_365085 : Nat := 4983230072969 + 3 ^ 40 * 365085 * 2
def baseEnd_365085 : Nat := 20829342749645481884279

theorem tailTrace_365085 : CollatzResearch.WordTrace tailWord_365085 prefixEnd_365085 20829342749645481884279 := by
  unfold tailWord_365085
  simp only [CollatzResearch.WordTrace]
  refine ⟨13315743882366871399048709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8877162588244580932699139 13315743882366871399048709)
  ·
    refine ⟨2496701977943788387321633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13315743882366871399048709 2496701977943788387321633)
    ·
      refine ⟨1872526483457841290491225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2496701977943788387321633 1872526483457841290491225)
      ·
        refine ⟨1404394862593380967868419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1872526483457841290491225 1404394862593380967868419)
        ·
          refine ⟨2106592293890071451802629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404394862593380967868419 2106592293890071451802629)
          ·
            refine ⟨394986055104388397212993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2106592293890071451802629 394986055104388397212993)
            ·
              refine ⟨296239541328291297909745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394986055104388397212993 296239541328291297909745)
              ·
                refine ⟨222179655996218473432309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296239541328291297909745 222179655996218473432309)
                ·
                  refine ⟨20829342749645481884279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222179655996218473432309 20829342749645481884279)
                  ·
                    rfl

theorem cell23_365085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_365085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365085 prefixEnd_365085 := by exact prefixLift 365085
  have htrace : WordTrace (prefixWord ++ tailWord_365085) baseStart_365085 baseEnd_365085 := by
    simpa [prefixWord, tailWord_365085, baseEnd_365085] using wordTrace_append hprefix tailTrace_365085
  have hstable : (prefixWord ++ tailWord_365085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365085).length < 2 ^ (prefixWord ++ tailWord_365085).sum := by decide
  have hdescent : baseEnd_365085 < baseStart_365085 := by decide
  rcases family_descends (prefixWord ++ tailWord_365085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365095 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_365095 : Nat := 118140960795 + 365095 * 2 ^ 59
def prefixEnd_365095 : Nat := 4983230072969 + 3 ^ 40 * 365095 * 2
def baseEnd_365095 : Nat := 187469219553354297833465

theorem tailTrace_365095 : CollatzResearch.WordTrace tailWord_365095 prefixEnd_365095 187469219553354297833465 := by
  unfold tailWord_365095
  simp only [CollatzResearch.WordTrace]
  refine ⟨13316108612330643106912739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8877405741553762071275159 13316108612330643106912739)
  ·
    refine ⟨19974162918495964660369109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13316108612330643106912739 19974162918495964660369109)
    ·
      refine ⟨468144443402249171727401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 19974162918495964660369109 468144443402249171727401)
      ·
        refine ⟨351108332551686878795551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468144443402249171727401 351108332551686878795551)
        ·
          refine ⟨526662498827530318193327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351108332551686878795551 526662498827530318193327)
          ·
            refine ⟨789993748241295477289991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526662498827530318193327 789993748241295477289991)
            ·
              refine ⟨1184990622361943215934987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789993748241295477289991 1184990622361943215934987)
              ·
                refine ⟨1777485933542914823902481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184990622361943215934987 1777485933542914823902481)
                ·
                  refine ⟨1333114450157186117926861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1777485933542914823902481 1333114450157186117926861)
                  ·
                    refine ⟨499917918808944794222573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1333114450157186117926861 499917918808944794222573)
                    ·
                      refine ⟨187469219553354297833465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 499917918808944794222573 187469219553354297833465)
                      ·
                        rfl

theorem cell23_365095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_365095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365095 prefixEnd_365095 := by exact prefixLift 365095
  have htrace : WordTrace (prefixWord ++ tailWord_365095) baseStart_365095 baseEnd_365095 := by
    simpa [prefixWord, tailWord_365095, baseEnd_365095] using wordTrace_append hprefix tailTrace_365095
  have hstable : (prefixWord ++ tailWord_365095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365095).length < 2 ^ (prefixWord ++ tailWord_365095).sum := by decide
  have hdescent : baseEnd_365095 < baseStart_365095 := by decide
  rcases family_descends (prefixWord ++ tailWord_365095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365111 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 3, 4]
def baseStart_365111 : Nat := 118140960795 + 365111 * 2 ^ 59
def prefixEnd_365111 : Nat := 4983230072969 + 3 ^ 40 * 365111 * 2
def baseEnd_365111 : Nat := 62492478414608745077797

theorem tailTrace_365111 : CollatzResearch.WordTrace tailWord_365111 prefixEnd_365111 62492478414608745077797 := by
  unfold tailWord_365111
  simp only [CollatzResearch.WordTrace]
  refine ⟨13316692180272677839495187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8877794786848451892996791 13316692180272677839495187)
  ·
    refine ⟨19975038270409016759242781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13316692180272677839495187 19975038270409016759242781)
    ·
      refine ⟨7490639351403381284716043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19975038270409016759242781 7490639351403381284716043)
      ·
        refine ⟨11235959027105071927074065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7490639351403381284716043 11235959027105071927074065)
        ·
          refine ⟨8426969270328803945305549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11235959027105071927074065 8426969270328803945305549)
          ·
            refine ⟨3160113476373301479489581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8426969270328803945305549 3160113476373301479489581)
            ·
              refine ⟨1185042553639988054808593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3160113476373301479489581 1185042553639988054808593)
              ·
                refine ⟨888781915229991041106445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185042553639988054808593 888781915229991041106445)
                ·
                  refine ⟨333293218211246640414917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888781915229991041106445 333293218211246640414917)
                  ·
                    refine ⟨62492478414608745077797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 333293218211246640414917 62492478414608745077797)
                    ·
                      rfl

theorem cell23_365111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_365111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365111 prefixEnd_365111 := by exact prefixLift 365111
  have htrace : WordTrace (prefixWord ++ tailWord_365111) baseStart_365111 baseEnd_365111 := by
    simpa [prefixWord, tailWord_365111, baseEnd_365111] using wordTrace_append hprefix tailTrace_365111
  have hstable : (prefixWord ++ tailWord_365111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365111).length < 2 ^ (prefixWord ++ tailWord_365111).sum := by decide
  have hdescent : baseEnd_365111 < baseStart_365111 := by decide
  rcases family_descends (prefixWord ++ tailWord_365111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365141 : List Nat := [1, 3, 2, 2, 1, 1, 5, 2, 6]
def baseStart_365141 : Nat := 118140960795 + 365141 * 2 ^ 59
def prefixEnd_365141 : Nat := 4983230072969 + 3 ^ 40 * 365141 * 2
def baseEnd_365141 : Nat := 20832537740384568650917

theorem tailTrace_365141 : CollatzResearch.WordTrace tailWord_365141 prefixEnd_365141 20832537740384568650917 := by
  unfold tailWord_365141
  simp only [CollatzResearch.WordTrace]
  refine ⟨13317786370163992963087277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8878524246775995308724851 13317786370163992963087277)
  ·
    refine ⟨4994169888811497361157729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13317786370163992963087277 4994169888811497361157729)
    ·
      refine ⟨3745627416608623020868297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4994169888811497361157729 3745627416608623020868297)
      ·
        refine ⟨2809220562456467265651223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3745627416608623020868297 2809220562456467265651223)
        ·
          refine ⟨4213830843684700898476835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809220562456467265651223 4213830843684700898476835)
          ·
            refine ⟨6320746265527051347715253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213830843684700898476835 6320746265527051347715253)
            ·
              refine ⟨592569962393161063848305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6320746265527051347715253 592569962393161063848305)
              ·
                refine ⟨444427471794870797886229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 592569962393161063848305 444427471794870797886229)
                ·
                  refine ⟨20832537740384568650917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 444427471794870797886229 20832537740384568650917)
                  ·
                    rfl

theorem cell23_365141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_365141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365141 prefixEnd_365141 := by exact prefixLift 365141
  have htrace : WordTrace (prefixWord ++ tailWord_365141) baseStart_365141 baseEnd_365141 := by
    simpa [prefixWord, tailWord_365141, baseEnd_365141] using wordTrace_append hprefix tailTrace_365141
  have hstable : (prefixWord ++ tailWord_365141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365141).length < 2 ^ (prefixWord ++ tailWord_365141).sum := by decide
  have hdescent : baseEnd_365141 < baseStart_365141 := by decide
  rcases family_descends (prefixWord ++ tailWord_365141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365144 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_365144 : Nat := 118140960795 + 365144 * 2 ^ 59
def prefixEnd_365144 : Nat := 4983230072969 + 3 ^ 40 * 365144 * 2
def baseEnd_365144 : Nat := 187494380105424606120739

theorem tailTrace_365144 : CollatzResearch.WordTrace tailWord_365144 prefixEnd_365144 187494380105424606120739 := by
  unfold tailWord_365144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6658947894576562237723243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8878597192768749650297657 6658947894576562237723243)
  ·
    refine ⟨9988421841864843356584865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6658947894576562237723243 9988421841864843356584865)
    ·
      refine ⟨7491316381398632517438649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9988421841864843356584865 7491316381398632517438649)
      ·
        refine ⟨5618487286048974388078987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7491316381398632517438649 5618487286048974388078987)
        ·
          refine ⟨8427730929073461582118481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5618487286048974388078987 8427730929073461582118481)
          ·
            refine ⟨6320798196805096186588861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8427730929073461582118481 6320798196805096186588861)
            ·
              refine ⟨2370299323801911069970823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6320798196805096186588861 2370299323801911069970823)
              ·
                refine ⟨3555448985702866604956235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370299323801911069970823 3555448985702866604956235)
                ·
                  refine ⟨5333173478554299907434353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3555448985702866604956235 5333173478554299907434353)
                  ·
                    refine ⟨3999880108915724930575765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5333173478554299907434353 3999880108915724930575765)
                    ·
                      refine ⟨187494380105424606120739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3999880108915724930575765 187494380105424606120739)
                      ·
                        rfl

theorem cell23_365144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_365144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365144 prefixEnd_365144 := by exact prefixLift 365144
  have htrace : WordTrace (prefixWord ++ tailWord_365144) baseStart_365144 baseEnd_365144 := by
    simpa [prefixWord, tailWord_365144, baseEnd_365144] using wordTrace_append hprefix tailTrace_365144
  have hstable : (prefixWord ++ tailWord_365144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365144).length < 2 ^ (prefixWord ++ tailWord_365144).sum := by decide
  have hdescent : baseEnd_365144 < baseStart_365144 := by decide
  rcases family_descends (prefixWord ++ tailWord_365144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365164 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_365164 : Nat := 118140960795 + 365164 * 2 ^ 59
def prefixEnd_365164 : Nat := 4983230072969 + 3 ^ 40 * 365164 * 2
def baseEnd_365164 : Nat := 187504649718514527870647

theorem tailTrace_365164 : CollatzResearch.WordTrace tailWord_365164 prefixEnd_365164 187504649718514527870647 := by
  unfold tailWord_365164
  simp only [CollatzResearch.WordTrace]
  refine ⟨6659312624540333945587273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8879083499387111927449697 6659312624540333945587273)
  ·
    refine ⟨4994484468405250459190455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6659312624540333945587273 4994484468405250459190455)
    ·
      refine ⟨7491726702607875688785683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4994484468405250459190455 7491726702607875688785683)
      ·
        refine ⟨11237590053911813533178525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7491726702607875688785683 11237590053911813533178525)
        ·
          refine ⟨4214096270216930074941947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11237590053911813533178525 4214096270216930074941947)
          ·
            refine ⟨6321144405325395112412921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4214096270216930074941947 6321144405325395112412921)
            ·
              refine ⟨4740858303994046334309691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6321144405325395112412921 4740858303994046334309691)
              ·
                refine ⟨7111287455991069501464537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4740858303994046334309691 7111287455991069501464537)
                ·
                  refine ⟨5333465591993302126098403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7111287455991069501464537 5333465591993302126098403)
                  ·
                    refine ⟨8000198387989953189147605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5333465591993302126098403 8000198387989953189147605)
                    ·
                      refine ⟨187504649718514527870647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8000198387989953189147605 187504649718514527870647)
                      ·
                        rfl

theorem cell23_365164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_365164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365164 prefixEnd_365164 := by exact prefixLift 365164
  have htrace : WordTrace (prefixWord ++ tailWord_365164) baseStart_365164 baseEnd_365164 := by
    simpa [prefixWord, tailWord_365164, baseEnd_365164] using wordTrace_append hprefix tailTrace_365164
  have hstable : (prefixWord ++ tailWord_365164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365164).length < 2 ^ (prefixWord ++ tailWord_365164).sum := by decide
  have hdescent : baseEnd_365164 < baseStart_365164 := by decide
  rcases family_descends (prefixWord ++ tailWord_365164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365188 : List Nat := [2, 3, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_365188 : Nat := 118140960795 + 365188 * 2 ^ 59
def prefixEnd_365188 : Nat := 4983230072969 + 3 ^ 40 * 365188 * 2
def baseEnd_365188 : Nat := 62505657751407477990179

theorem tailTrace_365188 : CollatzResearch.WordTrace tailWord_365188 prefixEnd_365188 62505657751407477990179 := by
  unfold tailWord_365188
  simp only [CollatzResearch.WordTrace]
  refine ⟨6659750300496859995024109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8879667067329146660032145 6659750300496859995024109)
  ·
    refine ⟨2497406362686322498134041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6659750300496859995024109 2497406362686322498134041)
    ·
      refine ⟨1873054772014741873600531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2497406362686322498134041 1873054772014741873600531)
      ·
        refine ⟨2809582158022112810400797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1873054772014741873600531 2809582158022112810400797)
        ·
          refine ⟨1053593309258292303900299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2809582158022112810400797 1053593309258292303900299)
          ·
            refine ⟨1580389963887438455850449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053593309258292303900299 1580389963887438455850449)
            ·
              refine ⟨1185292472915578841887837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1580389963887438455850449 1185292472915578841887837)
              ·
                refine ⟨444484677343342065707939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1185292472915578841887837 444484677343342065707939)
                ·
                  refine ⟨666727016015013098561909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444484677343342065707939 666727016015013098561909)
                  ·
                    refine ⟨62505657751407477990179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 666727016015013098561909 62505657751407477990179)
                    ·
                      rfl

theorem cell23_365188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_365188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365188 prefixEnd_365188 := by exact prefixLift 365188
  have htrace : WordTrace (prefixWord ++ tailWord_365188) baseStart_365188 baseEnd_365188 := by
    simpa [prefixWord, tailWord_365188, baseEnd_365188] using wordTrace_append hprefix tailTrace_365188
  have hstable : (prefixWord ++ tailWord_365188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365188).length < 2 ^ (prefixWord ++ tailWord_365188).sum := by decide
  have hdescent : baseEnd_365188 < baseStart_365188 := by decide
  rcases family_descends (prefixWord ++ tailWord_365188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365202 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_365202 : Nat := 118140960795 + 365202 * 2 ^ 59
def prefixEnd_365202 : Nat := 4983230072969 + 3 ^ 40 * 365202 * 2
def baseEnd_365202 : Nat := 187524161983385379195473

theorem tailTrace_365202 : CollatzResearch.WordTrace tailWord_365202 prefixEnd_365202 187524161983385379195473 := by
  unfold tailWord_365202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330002805735750095264465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8880007481962000254038573 3330002805735750095264465)
  ·
    refine ⟨2497502104301812571448349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3330002805735750095264465 2497502104301812571448349)
    ·
      refine ⟨936563289113179714293131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2497502104301812571448349 936563289113179714293131)
      ·
        refine ⟨1404844933669769571439697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936563289113179714293131 1404844933669769571439697)
        ·
          refine ⟨1053633700252327178579773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1404844933669769571439697 1053633700252327178579773)
          ·
            refine ⟨395112637594622691967415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1053633700252327178579773 395112637594622691967415)
            ·
              refine ⟨592668956391934037951123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395112637594622691967415 592668956391934037951123)
              ·
                refine ⟨889003434587901056926685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592668956391934037951123 889003434587901056926685)
                ·
                  refine ⟨333376287970462896347507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889003434587901056926685 333376287970462896347507)
                  ·
                    refine ⟨500064431955694344521261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 333376287970462896347507 500064431955694344521261)
                    ·
                      refine ⟨187524161983385379195473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 500064431955694344521261 187524161983385379195473)
                      ·
                        rfl

theorem cell23_365202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_365202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365202 prefixEnd_365202 := by exact prefixLift 365202
  have htrace : WordTrace (prefixWord ++ tailWord_365202) baseStart_365202 baseEnd_365202 := by
    simpa [prefixWord, tailWord_365202, baseEnd_365202] using wordTrace_append hprefix tailTrace_365202
  have hstable : (prefixWord ++ tailWord_365202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365202).length < 2 ^ (prefixWord ++ tailWord_365202).sum := by decide
  have hdescent : baseEnd_365202 < baseStart_365202 := by decide
  rcases family_descends (prefixWord ++ tailWord_365202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365221 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_365221 : Nat := 118140960795 + 365221 * 2 ^ 59
def prefixEnd_365221 : Nat := 4983230072969 + 3 ^ 40 * 365221 * 2
def baseEnd_365221 : Nat := 187533918115820804857885

theorem tailTrace_365221 : CollatzResearch.WordTrace tailWord_365221 prefixEnd_365221 187533918115820804857885 := by
  unfold tailWord_365221
  simp only [CollatzResearch.WordTrace]
  refine ⟨13320704209874166625999517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8880469473249444417333011 13320704209874166625999517)
  ·
    refine ⟨4995264078702812484749819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13320704209874166625999517 4995264078702812484749819)
    ·
      refine ⟨7492896118054218727124729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4995264078702812484749819 7492896118054218727124729)
      ·
        refine ⟨5619672088540664045343547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7492896118054218727124729 5619672088540664045343547)
        ·
          refine ⟨8429508132810996068015321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5619672088540664045343547 8429508132810996068015321)
          ·
            refine ⟨6322131099608247051011491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8429508132810996068015321 6322131099608247051011491)
            ·
              refine ⟨9483196649412370576517237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6322131099608247051011491 9483196649412370576517237)
              ·
                refine ⟨889049685882409741548491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9483196649412370576517237 889049685882409741548491)
                ·
                  refine ⟨1333574528823614612322737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889049685882409741548491 1333574528823614612322737)
                  ·
                    refine ⟨1000180896617710959242053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1333574528823614612322737 1000180896617710959242053)
                    ·
                      refine ⟨187533918115820804857885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1000180896617710959242053 187533918115820804857885)
                      ·
                        rfl

theorem cell23_365221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_365221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365221 prefixEnd_365221 := by exact prefixLift 365221
  have htrace : WordTrace (prefixWord ++ tailWord_365221) baseStart_365221 baseEnd_365221 := by
    simpa [prefixWord, tailWord_365221, baseEnd_365221] using wordTrace_append hprefix tailTrace_365221
  have hstable : (prefixWord ++ tailWord_365221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365221).length < 2 ^ (prefixWord ++ tailWord_365221).sum := by decide
  have hdescent : baseEnd_365221 < baseStart_365221 := by decide
  rcases family_descends (prefixWord ++ tailWord_365221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365242 : List Nat := [3, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2]
def baseStart_365242 : Nat := 118140960795 + 365242 * 2 ^ 59
def prefixEnd_365242 : Nat := 4983230072969 + 3 ^ 40 * 365242 * 2
def baseEnd_365242 : Nat := 187544701209565222695289

theorem tailTrace_365242 : CollatzResearch.WordTrace tailWord_365242 prefixEnd_365242 187544701209565222695289 := by
  unfold tailWord_365242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330367535699521803128495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8880980095198724808342653 3330367535699521803128495)
  ·
    refine ⟨4995551303549282704692743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3330367535699521803128495 4995551303549282704692743)
    ·
      refine ⟨7493326955323924057039115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4995551303549282704692743 7493326955323924057039115)
      ·
        refine ⟨11239990432985886085558673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7493326955323924057039115 11239990432985886085558673)
        ·
          refine ⟨8429992824739414564169005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11239990432985886085558673 8429992824739414564169005)
          ·
            refine ⟨3161247309277280461563377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8429992824739414564169005 3161247309277280461563377)
            ·
              refine ⟨2370935481957960346172533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3161247309277280461563377 2370935481957960346172533)
              ·
                refine ⟨222275201433558782453675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2370935481957960346172533 222275201433558782453675)
                ·
                  refine ⟨333412802150338173680513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222275201433558782453675 333412802150338173680513)
                  ·
                    refine ⟨250059601612753630260385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 333412802150338173680513 250059601612753630260385)
                    ·
                      refine ⟨187544701209565222695289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250059601612753630260385 187544701209565222695289)
                      ·
                        rfl

theorem cell23_365242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2].length) (baseStart_365242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365242 prefixEnd_365242 := by exact prefixLift 365242
  have htrace : WordTrace (prefixWord ++ tailWord_365242) baseStart_365242 baseEnd_365242 := by
    simpa [prefixWord, tailWord_365242, baseEnd_365242] using wordTrace_append hprefix tailTrace_365242
  have hstable : (prefixWord ++ tailWord_365242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365242).length < 2 ^ (prefixWord ++ tailWord_365242).sum := by decide
  have hdescent : baseEnd_365242 < baseStart_365242 := by decide
  rcases family_descends (prefixWord ++ tailWord_365242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365285 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 3, 3, 2]
def baseStart_365285 : Nat := 118140960795 + 365285 * 2 ^ 59
def prefixEnd_365285 : Nat := 4983230072969 + 3 ^ 40 * 365285 * 2
def baseEnd_365285 : Nat := 187566780877708554457591

theorem tailTrace_365285 : CollatzResearch.WordTrace tailWord_365285 prefixEnd_365285 187566780877708554457591 := by
  unfold tailWord_365285
  simp only [CollatzResearch.WordTrace]
  refine ⟨13323038481642305556329309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8882025654428203704219539 13323038481642305556329309)
  ·
    refine ⟨4996139430615864583623491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13323038481642305556329309 4996139430615864583623491)
    ·
      refine ⟨7494209145923796875435237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4996139430615864583623491 7494209145923796875435237)
      ·
        refine ⟨1405164214860711914144107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7494209145923796875435237 1405164214860711914144107)
        ·
          refine ⟨2107746322291067871216161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405164214860711914144107 2107746322291067871216161)
          ·
            refine ⟨1580809741718300903412121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2107746322291067871216161 1580809741718300903412121)
            ·
              refine ⟨1185607306288725677559091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1580809741718300903412121 1185607306288725677559091)
              ·
                refine ⟨1778410959433088516338637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185607306288725677559091 1778410959433088516338637)
                ·
                  refine ⟨666904109787408193626989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1778410959433088516338637 666904109787408193626989)
                  ·
                    refine ⟨250089041170278072610121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 666904109787408193626989 250089041170278072610121)
                    ·
                      refine ⟨187566780877708554457591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250089041170278072610121 187566780877708554457591)
                      ·
                        rfl

theorem cell23_365285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_365285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365285 prefixEnd_365285 := by exact prefixLift 365285
  have htrace : WordTrace (prefixWord ++ tailWord_365285) baseStart_365285 baseEnd_365285 := by
    simpa [prefixWord, tailWord_365285, baseEnd_365285] using wordTrace_append hprefix tailTrace_365285
  have hstable : (prefixWord ++ tailWord_365285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365285).length < 2 ^ (prefixWord ++ tailWord_365285).sum := by decide
  have hdescent : baseEnd_365285 < baseStart_365285 := by decide
  rcases family_descends (prefixWord ++ tailWord_365285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365302 : List Nat := [5, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_365302 : Nat := 118140960795 + 365302 * 2 ^ 59
def prefixEnd_365302 : Nat := 4983230072969 + 3 ^ 40 * 365302 * 2
def baseEnd_365302 : Nat := 187575510048834987945013

theorem tailTrace_365302 : CollatzResearch.WordTrace tailWord_365302 prefixEnd_365302 187575510048834987945013 := by
  unfold tailWord_365302
  simp only [CollatzResearch.WordTrace]
  refine ⟨832728657661294841231135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8882439015053811639798773 832728657661294841231135)
  ·
    refine ⟨1249092986491942261846703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 832728657661294841231135 1249092986491942261846703)
    ·
      refine ⟨1873639479737913392770055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1249092986491942261846703 1873639479737913392770055)
      ·
        refine ⟨2810459219606870089155083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1873639479737913392770055 2810459219606870089155083)
        ·
          refine ⟨4215688829410305133732625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2810459219606870089155083 4215688829410305133732625)
          ·
            refine ⟨3161766622057728850299469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4215688829410305133732625 3161766622057728850299469)
            ·
              refine ⟨1185662483271648318862301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3161766622057728850299469 1185662483271648318862301)
              ·
                refine ⟨444623431226868119573363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1185662483271648318862301 444623431226868119573363)
                ·
                  refine ⟨666935146840302179360045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444623431226868119573363 666935146840302179360045)
                  ·
                    refine ⟨250100680065113317260017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 666935146840302179360045 250100680065113317260017)
                    ·
                      refine ⟨187575510048834987945013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250100680065113317260017 187575510048834987945013)
                      ·
                        rfl

theorem cell23_365302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_365302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365302 prefixEnd_365302 := by exact prefixLift 365302
  have htrace : WordTrace (prefixWord ++ tailWord_365302) baseStart_365302 baseEnd_365302 := by
    simpa [prefixWord, tailWord_365302, baseEnd_365302] using wordTrace_append hprefix tailTrace_365302
  have hstable : (prefixWord ++ tailWord_365302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365302).length < 2 ^ (prefixWord ++ tailWord_365302).sum := by decide
  have hdescent : baseEnd_365302 < baseStart_365302 := by decide
  rcases family_descends (prefixWord ++ tailWord_365302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365321 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 7]
def baseStart_365321 : Nat := 118140960795 + 365321 * 2 ^ 59
def prefixEnd_365321 : Nat := 4983230072969 + 3 ^ 40 * 365321 * 2
def baseEnd_365321 : Nat := 20842807353474490400825

theorem tailTrace_365321 : CollatzResearch.WordTrace tailWord_365321 prefixEnd_365321 20842807353474490400825 := by
  unfold tailWord_365321
  simp only [CollatzResearch.WordTrace]
  refine ⟨13324351509511883704639817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8882901006341255803093211 13324351509511883704639817)
  ·
    refine ⟨9993263632133912778479863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13324351509511883704639817 9993263632133912778479863)
    ·
      refine ⟨14989895448200869167719795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9993263632133912778479863 14989895448200869167719795)
      ·
        refine ⟨22484843172301303751579693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14989895448200869167719795 22484843172301303751579693)
        ·
          refine ⟨8431816189612988906842385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22484843172301303751579693 8431816189612988906842385)
          ·
            refine ⟨6323862142209741680131789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8431816189612988906842385 6323862142209741680131789)
            ·
              refine ⟨2371448303328653130049421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6323862142209741680131789 2371448303328653130049421)
              ·
                refine ⟨889293113748244923768533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2371448303328653130049421 889293113748244923768533)
                ·
                  refine ⟨20842807353474490400825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 889293113748244923768533 20842807353474490400825)
                  ·
                    rfl

theorem cell23_365321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 7].length) (baseStart_365321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365321 prefixEnd_365321 := by exact prefixLift 365321
  have htrace : WordTrace (prefixWord ++ tailWord_365321) baseStart_365321 baseEnd_365321 := by
    simpa [prefixWord, tailWord_365321, baseEnd_365321] using wordTrace_append hprefix tailTrace_365321
  have hstable : (prefixWord ++ tailWord_365321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365321).length < 2 ^ (prefixWord ++ tailWord_365321).sum := by decide
  have hdescent : baseEnd_365321 < baseStart_365321 := by decide
  rcases family_descends (prefixWord ++ tailWord_365321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365368 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 2, 5]
def baseStart_365368 : Nat := 118140960795 + 365368 * 2 ^ 59
def prefixEnd_365368 : Nat := 4983230072969 + 3 ^ 40 * 365368 * 2
def baseEnd_365368 : Nat := 62536466590677243239903

theorem tailTrace_365368 : CollatzResearch.WordTrace tailWord_365368 prefixEnd_365368 62536466590677243239903 := by
  unfold tailWord_365368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663032870170805365800379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8884043826894407154400505 6663032870170805365800379)
  ·
    refine ⟨9994549305256208048700569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6663032870170805365800379 9994549305256208048700569)
    ·
      refine ⟨7495911978942156036525427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9994549305256208048700569 7495911978942156036525427)
      ·
        refine ⟨11243867968413234054788141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7495911978942156036525427 11243867968413234054788141)
        ·
          refine ⟨4216450488154962770545553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11243867968413234054788141 4216450488154962770545553)
          ·
            refine ⟨3162337866116222077909165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4216450488154962770545553 3162337866116222077909165)
            ·
              refine ⟨1185876699793583279215937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3162337866116222077909165 1185876699793583279215937)
              ·
                refine ⟨889407524845187459411953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185876699793583279215937 889407524845187459411953)
                ·
                  refine ⟨667055643633890594558965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 889407524845187459411953 667055643633890594558965)
                  ·
                    refine ⟨62536466590677243239903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 667055643633890594558965 62536466590677243239903)
                    ·
                      rfl

theorem cell23_365368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_365368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365368 prefixEnd_365368 := by exact prefixLift 365368
  have htrace : WordTrace (prefixWord ++ tailWord_365368) baseStart_365368 baseEnd_365368 := by
    simpa [prefixWord, tailWord_365368, baseEnd_365368] using wordTrace_append hprefix tailTrace_365368
  have hstable : (prefixWord ++ tailWord_365368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365368).length < 2 ^ (prefixWord ++ tailWord_365368).sum := by decide
  have hdescent : baseEnd_365368 < baseStart_365368 := by decide
  rcases family_descends (prefixWord ++ tailWord_365368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365371 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 4]
def baseStart_365371 : Nat := 118140960795 + 365371 * 2 ^ 59
def prefixEnd_365371 : Nat := 4983230072969 + 3 ^ 40 * 365371 * 2
def baseEnd_365371 : Nat := 187610940213995217982195

theorem tailTrace_365371 : CollatzResearch.WordTrace tailWord_365371 prefixEnd_365371 187610940213995217982195 := by
  unfold tailWord_365371
  simp only [CollatzResearch.WordTrace]
  refine ⟨13326175159330742243959967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8884116772887161495973311 13326175159330742243959967)
  ·
    refine ⟨19989262738996113365939951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13326175159330742243959967 19989262738996113365939951)
    ·
      refine ⟨29983894108494170048909927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19989262738996113365939951 29983894108494170048909927)
      ·
        refine ⟨44975841162741255073364891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29983894108494170048909927 44975841162741255073364891)
        ·
          refine ⟨67463761744111882610047337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44975841162741255073364891 67463761744111882610047337)
          ·
            refine ⟨50597821308083911957535503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67463761744111882610047337 50597821308083911957535503)
            ·
              refine ⟨75896731962125867936303255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50597821308083911957535503 75896731962125867936303255)
              ·
                refine ⟨113845097943188801904454883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75896731962125867936303255 113845097943188801904454883)
                ·
                  refine ⟨170767646914783202856682325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113845097943188801904454883 170767646914783202856682325)
                  ·
                    refine ⟨1000591681141307829238373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 170767646914783202856682325 1000591681141307829238373)
                    ·
                      refine ⟨187610940213995217982195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1000591681141307829238373 187610940213995217982195)
                      ·
                        rfl

theorem cell23_365371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 4].length) (baseStart_365371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365371 prefixEnd_365371 := by exact prefixLift 365371
  have htrace : WordTrace (prefixWord ++ tailWord_365371) baseStart_365371 baseEnd_365371 := by
    simpa [prefixWord, tailWord_365371, baseEnd_365371] using wordTrace_append hprefix tailTrace_365371
  have hstable : (prefixWord ++ tailWord_365371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365371).length < 2 ^ (prefixWord ++ tailWord_365371).sum := by decide
  have hdescent : baseEnd_365371 < baseStart_365371 := by decide
  rcases family_descends (prefixWord ++ tailWord_365371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365381 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 2, 8]
def baseStart_365381 : Nat := 118140960795 + 365381 * 2 ^ 59
def prefixEnd_365381 : Nat := 4983230072969 + 3 ^ 40 * 365381 * 2
def baseEnd_365381 : Nat := 62538691673513392952383

theorem tailTrace_365381 : CollatzResearch.WordTrace tailWord_365381 prefixEnd_365381 62538691673513392952383 := by
  unfold tailWord_365381
  simp only [CollatzResearch.WordTrace]
  refine ⟨13326539889294513951823997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8884359926196342634549331 13326539889294513951823997)
  ·
    refine ⟨4997452458485442731933999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13326539889294513951823997 4997452458485442731933999)
    ·
      refine ⟨7496178687728164097900999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4997452458485442731933999 7496178687728164097900999)
      ·
        refine ⟨11244268031592246146851499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7496178687728164097900999 11244268031592246146851499)
        ·
          refine ⟨16866402047388369220277249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11244268031592246146851499 16866402047388369220277249)
          ·
            refine ⟨12649801535541276915207937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16866402047388369220277249 12649801535541276915207937)
            ·
              refine ⟨9487351151655957686405953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12649801535541276915207937 9487351151655957686405953)
              ·
                refine ⟨7115513363741968264804465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9487351151655957686405953 7115513363741968264804465)
                ·
                  refine ⟨5336635022806476198603349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7115513363741968264804465 5336635022806476198603349)
                  ·
                    refine ⟨62538691673513392952383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5336635022806476198603349 62538691673513392952383)
                    ·
                      rfl

theorem cell23_365381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_365381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365381 prefixEnd_365381 := by exact prefixLift 365381
  have htrace : WordTrace (prefixWord ++ tailWord_365381) baseStart_365381 baseEnd_365381 := by
    simpa [prefixWord, tailWord_365381, baseEnd_365381] using wordTrace_append hprefix tailTrace_365381
  have hstable : (prefixWord ++ tailWord_365381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365381).length < 2 ^ (prefixWord ++ tailWord_365381).sum := by decide
  have hdescent : baseEnd_365381 < baseStart_365381 := by decide
  rcases family_descends (prefixWord ++ tailWord_365381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365391 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 5]
def baseStart_365391 : Nat := 118140960795 + 365391 * 2 ^ 59
def prefixEnd_365391 : Nat := 4983230072969 + 3 ^ 40 * 365391 * 2
def baseEnd_365391 : Nat := 187621209827085139732103

theorem tailTrace_365391 : CollatzResearch.WordTrace tailWord_365391 prefixEnd_365391 187621209827085139732103 := by
  unfold tailWord_365391
  simp only [CollatzResearch.WordTrace]
  refine ⟨13326904619258285659688027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8884603079505523773125351 13326904619258285659688027)
  ·
    refine ⟨19990356928887428489532041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13326904619258285659688027 19990356928887428489532041)
    ·
      refine ⟨14992767696665571367149031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19990356928887428489532041 14992767696665571367149031)
      ·
        refine ⟨22489151544998357050723547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14992767696665571367149031 22489151544998357050723547)
        ·
          refine ⟨33733727317497535576085321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22489151544998357050723547 33733727317497535576085321)
          ·
            refine ⟨25300295488123151682063991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33733727317497535576085321 25300295488123151682063991)
            ·
              refine ⟨37950443232184727523095987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25300295488123151682063991 37950443232184727523095987)
              ·
                refine ⟨56925664848277091284643981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37950443232184727523095987 56925664848277091284643981)
                ·
                  refine ⟨21347124318103909231741493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56925664848277091284643981 21347124318103909231741493)
                  ·
                    refine ⟨2001292904822241490475765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21347124318103909231741493 2001292904822241490475765)
                    ·
                      refine ⟨187621209827085139732103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2001292904822241490475765 187621209827085139732103)
                      ·
                        rfl

theorem cell23_365391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_365391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365391 prefixEnd_365391 := by exact prefixLift 365391
  have htrace : WordTrace (prefixWord ++ tailWord_365391) baseStart_365391 baseEnd_365391 := by
    simpa [prefixWord, tailWord_365391, baseEnd_365391] using wordTrace_append hprefix tailTrace_365391
  have hstable : (prefixWord ++ tailWord_365391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365391).length < 2 ^ (prefixWord ++ tailWord_365391).sum := by decide
  have hdescent : baseEnd_365391 < baseStart_365391 := by decide
  rcases family_descends (prefixWord ++ tailWord_365391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365425 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 3]
def baseStart_365425 : Nat := 118140960795 + 365425 * 2 ^ 59
def prefixEnd_365425 : Nat := 4983230072969 + 3 ^ 40 * 365425 * 2
def baseEnd_365425 : Nat := 187638668169338006706947

theorem tailTrace_365425 : CollatzResearch.WordTrace tailWord_365425 prefixEnd_365425 187638668169338006706947 := by
  unfold tailWord_365425
  simp only [CollatzResearch.WordTrace]
  refine ⟨13328144701135109466425729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8885429800756739644283819 13328144701135109466425729)
  ·
    refine ⟨9996108525851332099819297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13328144701135109466425729 9996108525851332099819297)
    ·
      refine ⟨7497081394388499074864473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9996108525851332099819297 7497081394388499074864473)
      ·
        refine ⟨5622811045791374306148355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7497081394388499074864473 5622811045791374306148355)
        ·
          refine ⟨8434216568687061459222533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622811045791374306148355 8434216568687061459222533)
          ·
            refine ⟨1581415606628824023604225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8434216568687061459222533 1581415606628824023604225)
            ·
              refine ⟨1186061704971618017703169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1581415606628824023604225 1186061704971618017703169)
              ·
                refine ⟨889546278728713513277377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1186061704971618017703169 889546278728713513277377)
                ·
                  refine ⟨667159709046535134958033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 889546278728713513277377 667159709046535134958033)
                  ·
                    refine ⟨500369781784901351218525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 667159709046535134958033 500369781784901351218525)
                    ·
                      refine ⟨187638668169338006706947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 500369781784901351218525 187638668169338006706947)
                      ·
                        rfl

theorem cell23_365425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_365425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365425 prefixEnd_365425 := by exact prefixLift 365425
  have htrace : WordTrace (prefixWord ++ tailWord_365425) baseStart_365425 baseEnd_365425 := by
    simpa [prefixWord, tailWord_365425, baseEnd_365425] using wordTrace_append hprefix tailTrace_365425
  have hstable : (prefixWord ++ tailWord_365425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365425).length < 2 ^ (prefixWord ++ tailWord_365425).sum := by decide
  have hdescent : baseEnd_365425 < baseStart_365425 := by decide
  rcases family_descends (prefixWord ++ tailWord_365425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365479 : List Nat := [1, 1, 6, 1, 4, 1, 1, 2, 6]
def baseStart_365479 : Nat := 118140960795 + 365479 * 2 ^ 59
def prefixEnd_365479 : Nat := 4983230072969 + 3 ^ 40 * 365479 * 2
def baseEnd_365479 : Nat := 20851821791631199492411

theorem tailTrace_365479 : CollatzResearch.WordTrace tailWord_365479 prefixEnd_365479 20851821791631199492411 := by
  unfold tailWord_365479
  simp only [CollatzResearch.WordTrace]
  refine ⟨13330114242939476688891491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8886742828626317792594327 13330114242939476688891491)
  ·
    refine ⟨19995171364409215033337237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13330114242939476688891491 19995171364409215033337237)
    ·
      refine ⟨937273657706681954687683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19995171364409215033337237 937273657706681954687683)
      ·
        refine ⟨1405910486560022932031525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937273657706681954687683 1405910486560022932031525)
        ·
          refine ⟨263608216230004299755911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1405910486560022932031525 263608216230004299755911)
          ·
            refine ⟨395412324345006449633867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263608216230004299755911 395412324345006449633867)
            ·
              refine ⟨593118486517509674450801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395412324345006449633867 593118486517509674450801)
              ·
                refine ⟨444838864888132255838101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593118486517509674450801 444838864888132255838101)
                ·
                  refine ⟨20851821791631199492411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 444838864888132255838101 20851821791631199492411)
                  ·
                    rfl

theorem cell23_365479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 6].length) (baseStart_365479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365479 prefixEnd_365479 := by exact prefixLift 365479
  have htrace : WordTrace (prefixWord ++ tailWord_365479) baseStart_365479 baseEnd_365479 := by
    simpa [prefixWord, tailWord_365479, baseEnd_365479] using wordTrace_append hprefix tailTrace_365479
  have hstable : (prefixWord ++ tailWord_365479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365479).length < 2 ^ (prefixWord ++ tailWord_365479).sum := by decide
  have hdescent : baseEnd_365479 < baseStart_365479 := by decide
  rcases family_descends (prefixWord ++ tailWord_365479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365489 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 3, 1, 3]
def baseStart_365489 : Nat := 118140960795 + 365489 * 2 ^ 59
def prefixEnd_365489 : Nat := 4983230072969 + 3 ^ 40 * 365489 * 2
def baseEnd_365489 : Nat := 187671530931225756306653

theorem tailTrace_365489 : CollatzResearch.WordTrace tailWord_365489 prefixEnd_365489 187671530931225756306653 := by
  unfold tailWord_365489
  simp only [CollatzResearch.WordTrace]
  refine ⟨13330478972903248396755521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8886985981935498931170347 13330478972903248396755521)
  ·
    refine ⟨9997859229677436297566641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13330478972903248396755521 9997859229677436297566641)
    ·
      refine ⟨7498394422258077223174981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9997859229677436297566641 7498394422258077223174981)
      ·
        refine ⟨1405948954173389479345309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7498394422258077223174981 1405948954173389479345309)
        ·
          refine ⟨527230857815021054754491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1405948954173389479345309 527230857815021054754491)
          ·
            refine ⟨790846286722531582131737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527230857815021054754491 790846286722531582131737)
            ·
              refine ⟨593134715041898686598803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790846286722531582131737 593134715041898686598803)
              ·
                refine ⟨889702072562848029898205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593134715041898686598803 889702072562848029898205)
                ·
                  refine ⟨333638277211068011211827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889702072562848029898205 333638277211068011211827)
                  ·
                    refine ⟨500457415816602016817741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 333638277211068011211827 500457415816602016817741)
                    ·
                      refine ⟨187671530931225756306653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 500457415816602016817741 187671530931225756306653)
                      ·
                        rfl

theorem cell23_365489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_365489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365489 prefixEnd_365489 := by exact prefixLift 365489
  have htrace : WordTrace (prefixWord ++ tailWord_365489) baseStart_365489 baseEnd_365489 := by
    simpa [prefixWord, tailWord_365489, baseEnd_365489] using wordTrace_append hprefix tailTrace_365489
  have hstable : (prefixWord ++ tailWord_365489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365489).length < 2 ^ (prefixWord ++ tailWord_365489).sum := by decide
  have hdescent : baseEnd_365489 < baseStart_365489 := by decide
  rcases family_descends (prefixWord ++ tailWord_365489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365517 : List Nat := [1, 6, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_365517 : Nat := 118140960795 + 365517 * 2 ^ 59
def prefixEnd_365517 : Nat := 4983230072969 + 3 ^ 40 * 365517 * 2
def baseEnd_365517 : Nat := 62561969463183882252175

theorem tailTrace_365517 : CollatzResearch.WordTrace tailWord_365517 prefixEnd_365517 62561969463183882252175 := by
  unfold tailWord_365517
  simp only [CollatzResearch.WordTrace]
  refine ⟨13331500216801809178774805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8887666811201206119183203 13331500216801809178774805)
  ·
    refine ⟨624914072662584805255069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13331500216801809178774805 624914072662584805255069)
    ·
      refine ⟨234342777248469301970651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 624914072662584805255069 234342777248469301970651)
      ·
        refine ⟨351514165872703952955977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234342777248469301970651 351514165872703952955977)
        ·
          refine ⟨263635624404527964716983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351514165872703952955977 263635624404527964716983)
          ·
            refine ⟨395453436606791947075475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263635624404527964716983 395453436606791947075475)
            ·
              refine ⟨593180154910187920613213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395453436606791947075475 593180154910187920613213)
              ·
                refine ⟨222442558091320470229955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 593180154910187920613213 222442558091320470229955)
                ·
                  refine ⟨333663837136980705344933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222442558091320470229955 333663837136980705344933)
                  ·
                    refine ⟨62561969463183882252175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 333663837136980705344933 62561969463183882252175)
                    ·
                      rfl

theorem cell23_365517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_365517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365517 prefixEnd_365517 := by exact prefixLift 365517
  have htrace : WordTrace (prefixWord ++ tailWord_365517) baseStart_365517 baseEnd_365517 := by
    simpa [prefixWord, tailWord_365517, baseEnd_365517] using wordTrace_append hprefix tailTrace_365517
  have hstable : (prefixWord ++ tailWord_365517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365517).length < 2 ^ (prefixWord ++ tailWord_365517).sum := by decide
  have hdescent : baseEnd_365517 < baseStart_365517 := by decide
  rcases family_descends (prefixWord ++ tailWord_365517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365522 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_365522 : Nat := 118140960795 + 365522 * 2 ^ 59
def prefixEnd_365522 : Nat := 4983230072969 + 3 ^ 40 * 365522 * 2
def baseEnd_365522 : Nat := 62562825264274709064667

theorem tailTrace_365522 : CollatzResearch.WordTrace tailWord_365522 prefixEnd_365522 62562825264274709064667 := by
  unfold tailWord_365522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3332920645445923758176705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8887788387855796688471213 3332920645445923758176705)
  ·
    refine ⟨2499690484084442818632529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3332920645445923758176705 2499690484084442818632529)
    ·
      refine ⟨1874767863063332113974397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2499690484084442818632529 1874767863063332113974397)
      ·
        refine ⟨703037948648749542740399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1874767863063332113974397 703037948648749542740399)
        ·
          refine ⟨1054556922973124314110599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703037948648749542740399 1054556922973124314110599)
          ·
            refine ⟨1581835384459686471165899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054556922973124314110599 1581835384459686471165899)
            ·
              refine ⟨2372753076689529706748849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581835384459686471165899 2372753076689529706748849)
              ·
                refine ⟨1779564807517147280061637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372753076689529706748849 1779564807517147280061637)
                ·
                  refine ⟨333668401409465115011557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779564807517147280061637 333668401409465115011557)
                  ·
                    refine ⟨62562825264274709064667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 333668401409465115011557 62562825264274709064667)
                    ·
                      rfl

theorem cell23_365522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_365522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365522 prefixEnd_365522 := by exact prefixLift 365522
  have htrace : WordTrace (prefixWord ++ tailWord_365522) baseStart_365522 baseEnd_365522 := by
    simpa [prefixWord, tailWord_365522, baseEnd_365522] using wordTrace_append hprefix tailTrace_365522
  have hstable : (prefixWord ++ tailWord_365522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365522).length < 2 ^ (prefixWord ++ tailWord_365522).sum := by decide
  have hdescent : baseEnd_365522 < baseStart_365522 := by decide
  rcases family_descends (prefixWord ++ tailWord_365522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365535 : List Nat := [1, 1, 2, 3, 5, 2, 9]
def baseStart_365535 : Nat := 118140960795 + 365535 * 2 ^ 59
def prefixEnd_365535 : Nat := 4983230072969 + 3 ^ 40 * 365535 * 2
def baseEnd_365535 : Nat := 2317224086930031806561

theorem tailTrace_365535 : CollatzResearch.WordTrace tailWord_365535 prefixEnd_365535 2317224086930031806561 := by
  unfold tailWord_365535
  simp only [CollatzResearch.WordTrace]
  refine ⟨13332156730736598252930059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8888104487157732168620039 13332156730736598252930059)
  ·
    refine ⟨19998235096104897379395089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13332156730736598252930059 19998235096104897379395089)
    ·
      refine ⟨14998676322078673034546317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19998235096104897379395089 14998676322078673034546317)
      ·
        refine ⟨5624503620779502387954869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14998676322078673034546317 5624503620779502387954869)
        ·
          refine ⟨527297214448078348870769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5624503620779502387954869 527297214448078348870769)
          ·
            refine ⟨395472910836058761653077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527297214448078348870769 395472910836058761653077)
            ·
              refine ⟨2317224086930031806561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 395472910836058761653077 2317224086930031806561)
              ·
                rfl

theorem cell23_365535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 9].length) (baseStart_365535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365535 prefixEnd_365535 := by exact prefixLift 365535
  have htrace : WordTrace (prefixWord ++ tailWord_365535) baseStart_365535 baseEnd_365535 := by
    simpa [prefixWord, tailWord_365535, baseEnd_365535] using wordTrace_append hprefix tailTrace_365535
  have hstable : (prefixWord ++ tailWord_365535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365535).length < 2 ^ (prefixWord ++ tailWord_365535).sum := by decide
  have hdescent : baseEnd_365535 < baseStart_365535 := by decide
  rcases family_descends (prefixWord ++ tailWord_365535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365546 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_365546 : Nat := 118140960795 + 365546 * 2 ^ 59
def prefixEnd_365546 : Nat := 4983230072969 + 3 ^ 40 * 365546 * 2
def baseEnd_365546 : Nat := 187700799328532033293891

theorem tailTrace_365546 : CollatzResearch.WordTrace tailWord_365546 prefixEnd_365546 187700799328532033293891 := by
  unfold tailWord_365546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333139483424186782895123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8888371955797831421053661 3333139483424186782895123)
  ·
    refine ⟨4999709225136280174342685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3333139483424186782895123 4999709225136280174342685)
    ·
      refine ⟨1874890959426105065378507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4999709225136280174342685 1874890959426105065378507)
      ·
        refine ⟨2812336439139157598067761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874890959426105065378507 2812336439139157598067761)
        ·
          refine ⟨2109252329354368198550821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2812336439139157598067761 2109252329354368198550821)
          ·
            refine ⟨395484811753944037228279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2109252329354368198550821 395484811753944037228279)
            ·
              refine ⟨593227217630916055842419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395484811753944037228279 593227217630916055842419)
              ·
                refine ⟨889840826446374083763629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593227217630916055842419 889840826446374083763629)
                ·
                  refine ⟨333690309917390281411361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889840826446374083763629 333690309917390281411361)
                  ·
                    refine ⟨250267732438042711058521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 333690309917390281411361 250267732438042711058521)
                    ·
                      refine ⟨187700799328532033293891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250267732438042711058521 187700799328532033293891)
                      ·
                        rfl

theorem cell23_365546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_365546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365546 prefixEnd_365546 := by exact prefixLift 365546
  have htrace : WordTrace (prefixWord ++ tailWord_365546) baseStart_365546 baseEnd_365546 := by
    simpa [prefixWord, tailWord_365546, baseEnd_365546] using wordTrace_append hprefix tailTrace_365546
  have hstable : (prefixWord ++ tailWord_365546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365546).length < 2 ^ (prefixWord ++ tailWord_365546).sum := by decide
  have hdescent : baseEnd_365546 < baseStart_365546 := by decide
  rcases family_descends (prefixWord ++ tailWord_365546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365555 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 1, 9, 2]
def baseStart_365555 : Nat := 118140960795 + 365555 * 2 ^ 59
def prefixEnd_365555 : Nat := 4983230072969 + 3 ^ 40 * 365555 * 2
def baseEnd_365555 : Nat := 187705420654422498081349

theorem tailTrace_365555 : CollatzResearch.WordTrace tailWord_365555 prefixEnd_365555 187705420654422498081349 := by
  unfold tailWord_365555
  simp only [CollatzResearch.WordTrace]
  refine ⟨13332886190664141668658119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8888590793776094445772079 13332886190664141668658119)
  ·
    refine ⟨19999329285996212502987179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13332886190664141668658119 19999329285996212502987179)
    ·
      refine ⟨29998993928994318754480769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19999329285996212502987179 29998993928994318754480769)
      ·
        refine ⟨22499245446745739065860577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29998993928994318754480769 22499245446745739065860577)
        ·
          refine ⟨16874434085059304299395433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22499245446745739065860577 16874434085059304299395433)
          ·
            refine ⟨12655825563794478224546575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16874434085059304299395433 12655825563794478224546575)
            ·
              refine ⟨18983738345691717336819863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12655825563794478224546575 18983738345691717336819863)
              ·
                refine ⟨28475607518537576005229795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18983738345691717336819863 28475607518537576005229795)
                ·
                  refine ⟨42713411277806364007844693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28475607518537576005229795 42713411277806364007844693)
                  ·
                    refine ⟨250273894205896664108465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 42713411277806364007844693 250273894205896664108465)
                    ·
                      refine ⟨187705420654422498081349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250273894205896664108465 187705420654422498081349)
                      ·
                        rfl

theorem cell23_365555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 9, 2].length) (baseStart_365555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365555 prefixEnd_365555 := by exact prefixLift 365555
  have htrace : WordTrace (prefixWord ++ tailWord_365555) baseStart_365555 baseEnd_365555 := by
    simpa [prefixWord, tailWord_365555, baseEnd_365555] using wordTrace_append hprefix tailTrace_365555
  have hstable : (prefixWord ++ tailWord_365555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365555).length < 2 ^ (prefixWord ++ tailWord_365555).sum := by decide
  have hdescent : baseEnd_365555 < baseStart_365555 := by decide
  rcases family_descends (prefixWord ++ tailWord_365555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365596 : List Nat := [2, 2, 3, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_365596 : Nat := 118140960795 + 365596 * 2 ^ 59
def prefixEnd_365596 : Nat := 4983230072969 + 3 ^ 40 * 365596 * 2
def baseEnd_365596 : Nat := 187726473361256837668661

theorem tailTrace_365596 : CollatzResearch.WordTrace tailWord_365596 prefixEnd_365596 187726473361256837668661 := by
  unfold tailWord_365596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6667190791757802835450321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8889587722343737113933761 6667190791757802835450321)
  ·
    refine ⟨5000393093818352126587741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6667190791757802835450321 5000393093818352126587741)
    ·
      refine ⟨1875147410181882047470403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5000393093818352126587741 1875147410181882047470403)
      ·
        refine ⟨2812721115272823071205605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875147410181882047470403 2812721115272823071205605)
        ·
          refine ⟨527385209113654325851051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2812721115272823071205605 527385209113654325851051)
          ·
            refine ⟨791077813670481488776577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527385209113654325851051 791077813670481488776577)
            ·
              refine ⟨593308360252861116582433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791077813670481488776577 593308360252861116582433)
              ·
                refine ⟨444981270189645837436825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593308360252861116582433 444981270189645837436825)
                ·
                  refine ⟨333735952642234378077619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444981270189645837436825 333735952642234378077619)
                  ·
                    refine ⟨500603928963351567116429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 333735952642234378077619 500603928963351567116429)
                    ·
                      refine ⟨187726473361256837668661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 500603928963351567116429 187726473361256837668661)
                      ·
                        rfl

theorem cell23_365596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_365596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365596 prefixEnd_365596 := by exact prefixLift 365596
  have htrace : WordTrace (prefixWord ++ tailWord_365596) baseStart_365596 baseEnd_365596 := by
    simpa [prefixWord, tailWord_365596, baseEnd_365596] using wordTrace_append hprefix tailTrace_365596
  have hstable : (prefixWord ++ tailWord_365596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365596).length < 2 ^ (prefixWord ++ tailWord_365596).sum := by decide
  have hdescent : baseEnd_365596 < baseStart_365596 := by decide
  rcases family_descends (prefixWord ++ tailWord_365596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365597 : List Nat := [1, 4, 2, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_365597 : Nat := 118140960795 + 365597 * 2 ^ 59
def prefixEnd_365597 : Nat := 4983230072969 + 3 ^ 40 * 365597 * 2
def baseEnd_365597 : Nat := 187726986841911333756157

theorem tailTrace_365597 : CollatzResearch.WordTrace tailWord_365597 prefixEnd_365597 187726986841911333756157 := by
  unfold tailWord_365597
  simp only [CollatzResearch.WordTrace]
  refine ⟨13334418056511982841687045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8889612037674655227791363 13334418056511982841687045)
  ·
    refine ⟨2500203385595996782816321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13334418056511982841687045 2500203385595996782816321)
    ·
      refine ⟨1875152539196997587112241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2500203385595996782816321 1875152539196997587112241)
      ·
        refine ⟨1406364404397748190334181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1875152539196997587112241 1406364404397748190334181)
        ·
          refine ⟨263693325824577785687659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1406364404397748190334181 263693325824577785687659)
          ·
            refine ⟨395539988736866678531489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263693325824577785687659 395539988736866678531489)
            ·
              refine ⟨296654991552650008898617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395539988736866678531489 296654991552650008898617)
              ·
                refine ⟨222491243664487506673963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296654991552650008898617 222491243664487506673963)
                ·
                  refine ⟨333736865496731260010945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222491243664487506673963 333736865496731260010945)
                  ·
                    refine ⟨250302649122548445008209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 333736865496731260010945 250302649122548445008209)
                    ·
                      refine ⟨187726986841911333756157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250302649122548445008209 187726986841911333756157)
                      ·
                        rfl

theorem cell23_365597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_365597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365597 prefixEnd_365597 := by exact prefixLift 365597
  have htrace : WordTrace (prefixWord ++ tailWord_365597) baseStart_365597 baseEnd_365597 := by
    simpa [prefixWord, tailWord_365597, baseEnd_365597] using wordTrace_append hprefix tailTrace_365597
  have hstable : (prefixWord ++ tailWord_365597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365597).length < 2 ^ (prefixWord ++ tailWord_365597).sum := by decide
  have hdescent : baseEnd_365597 < baseStart_365597 := by decide
  rcases family_descends (prefixWord ++ tailWord_365597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365605 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 1, 6, 3]
def baseStart_365605 : Nat := 118140960795 + 365605 * 2 ^ 59
def prefixEnd_365605 : Nat := 4983230072969 + 3 ^ 40 * 365605 * 2
def baseEnd_365605 : Nat := 187731094687147302456119

theorem tailTrace_365605 : CollatzResearch.WordTrace tailWord_365605 prefixEnd_365605 187731094687147302456119 := by
  unfold tailWord_365605
  simp only [CollatzResearch.WordTrace]
  refine ⟨13334709840483000207978269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8889806560322000138652179 13334709840483000207978269)
  ·
    refine ⟨5000516190181125077991851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13334709840483000207978269 5000516190181125077991851)
    ·
      refine ⟨7500774285271687616987777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5000516190181125077991851 7500774285271687616987777)
      ·
        refine ⟨5625580713953765712740833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7500774285271687616987777 5625580713953765712740833)
        ·
          refine ⟨4219185535465324284555625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5625580713953765712740833 4219185535465324284555625)
          ·
            refine ⟨3164389151598993213416719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4219185535465324284555625 3164389151598993213416719)
            ·
              refine ⟨4746583727398489820125079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164389151598993213416719 4746583727398489820125079)
              ·
                refine ⟨7119875591097734730187619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4746583727398489820125079 7119875591097734730187619)
                ·
                  refine ⟨10679813386646602095281429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7119875591097734730187619 10679813386646602095281429)
                  ·
                    refine ⟨500616252499059473216317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10679813386646602095281429 500616252499059473216317)
                    ·
                      refine ⟨187731094687147302456119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 500616252499059473216317 187731094687147302456119)
                      ·
                        rfl

theorem cell23_365605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_365605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365605 prefixEnd_365605 := by exact prefixLift 365605
  have htrace : WordTrace (prefixWord ++ tailWord_365605) baseStart_365605 baseEnd_365605 := by
    simpa [prefixWord, tailWord_365605, baseEnd_365605] using wordTrace_append hprefix tailTrace_365605
  have hstable : (prefixWord ++ tailWord_365605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365605).length < 2 ^ (prefixWord ++ tailWord_365605).sum := by decide
  have hdescent : baseEnd_365605 < baseStart_365605 := by decide
  rcases family_descends (prefixWord ++ tailWord_365605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365625 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 9]
def baseStart_365625 : Nat := 118140960795 + 365625 * 2 ^ 59
def prefixEnd_365625 : Nat := 4983230072969 + 3 ^ 40 * 365625 * 2
def baseEnd_365625 : Nat := 20860151588915247134003

theorem tailTrace_365625 : CollatzResearch.WordTrace tailWord_365625 prefixEnd_365625 20860151588915247134003 := by
  unfold tailWord_365625
  simp only [CollatzResearch.WordTrace]
  refine ⟨13335439300410543623706329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8890292866940362415804219 13335439300410543623706329)
  ·
    refine ⟨10001579475307907717779747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13335439300410543623706329 10001579475307907717779747)
    ·
      refine ⟨15002369212961861576669621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10001579475307907717779747 15002369212961861576669621)
      ·
        refine ⟨1406472113715174522812777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15002369212961861576669621 1406472113715174522812777)
        ·
          refine ⟨1054854085286380892109583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1406472113715174522812777 1054854085286380892109583)
          ·
            refine ⟨1582281127929571338164375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054854085286380892109583 1582281127929571338164375)
            ·
              refine ⟨2373421691894357007246563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582281127929571338164375 2373421691894357007246563)
              ·
                refine ⟨3560132537841535510869845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373421691894357007246563 3560132537841535510869845)
                ·
                  refine ⟨20860151588915247134003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3560132537841535510869845 20860151588915247134003)
                  ·
                    rfl

theorem cell23_365625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 9].length) (baseStart_365625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365625 prefixEnd_365625 := by exact prefixLift 365625
  have htrace : WordTrace (prefixWord ++ tailWord_365625) baseStart_365625 baseEnd_365625 := by
    simpa [prefixWord, tailWord_365625, baseEnd_365625] using wordTrace_append hprefix tailTrace_365625
  have hstable : (prefixWord ++ tailWord_365625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365625).length < 2 ^ (prefixWord ++ tailWord_365625).sum := by decide
  have hdescent : baseEnd_365625 < baseStart_365625 := by decide
  rcases family_descends (prefixWord ++ tailWord_365625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365635 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 3]
def baseStart_365635 : Nat := 118140960795 + 365635 * 2 ^ 59
def prefixEnd_365635 : Nat := 4983230072969 + 3 ^ 40 * 365635 * 2
def baseEnd_365635 : Nat := 187746499106782185080981

theorem tailTrace_365635 : CollatzResearch.WordTrace tailWord_365635 prefixEnd_365635 187746499106782185080981 := by
  unfold tailWord_365635
  simp only [CollatzResearch.WordTrace]
  refine ⟨13335804030374315331570359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8890536020249543554380239 13335804030374315331570359)
  ·
    refine ⟨20003706045561472997355539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13335804030374315331570359 20003706045561472997355539)
    ·
      refine ⟨30005559068342209496033309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20003706045561472997355539 30005559068342209496033309)
      ·
        refine ⟨11252084650628328561012491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30005559068342209496033309 11252084650628328561012491)
        ·
          refine ⟨16878126975942492841518737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11252084650628328561012491 16878126975942492841518737)
          ·
            refine ⟨12658595231956869631139053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16878126975942492841518737 12658595231956869631139053)
            ·
              refine ⟨4746973211983826111677145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12658595231956869631139053 4746973211983826111677145)
              ·
                refine ⟨3560229908987869583757859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4746973211983826111677145 3560229908987869583757859)
                ·
                  refine ⟨5340344863481804375636789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3560229908987869583757859 5340344863481804375636789)
                  ·
                    refine ⟨500657330951419160215949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5340344863481804375636789 500657330951419160215949)
                    ·
                      refine ⟨187746499106782185080981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 500657330951419160215949 187746499106782185080981)
                      ·
                        rfl

theorem cell23_365635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_365635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365635 prefixEnd_365635 := by exact prefixLift 365635
  have htrace : WordTrace (prefixWord ++ tailWord_365635) baseStart_365635 baseEnd_365635 := by
    simpa [prefixWord, tailWord_365635, baseEnd_365635] using wordTrace_append hprefix tailTrace_365635
  have hstable : (prefixWord ++ tailWord_365635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365635).length < 2 ^ (prefixWord ++ tailWord_365635).sum := by decide
  have hdescent : baseEnd_365635 < baseStart_365635 := by decide
  rcases family_descends (prefixWord ++ tailWord_365635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365642 : List Nat := [3, 1, 2, 1, 1, 2, 3, 5, 5]
def baseStart_365642 : Nat := 118140960795 + 365642 * 2 ^ 59
def prefixEnd_365642 : Nat := 4983230072969 + 3 ^ 40 * 365642 * 2
def baseEnd_365642 : Nat := 20861121496818184188161

theorem tailTrace_365642 : CollatzResearch.WordTrace tailWord_365642 prefixEnd_365642 20861121496818184188161 := by
  unfold tailWord_365642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334014835337238881768795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8890706227565970351383453 3334014835337238881768795)
  ·
    refine ⟨5001022253005858322653193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3334014835337238881768795 5001022253005858322653193)
    ·
      refine ⟨3750766689754393741989895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5001022253005858322653193 3750766689754393741989895)
      ·
        refine ⟨5626150034631590612984843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3750766689754393741989895 5626150034631590612984843)
        ·
          refine ⟨8439225051947385919477265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626150034631590612984843 8439225051947385919477265)
          ·
            refine ⟨6329418788960539439607949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8439225051947385919477265 6329418788960539439607949)
            ·
              refine ⟨2373532045860202289852981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6329418788960539439607949 2373532045860202289852981)
              ·
                refine ⟨222518629299393964673717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2373532045860202289852981 222518629299393964673717)
                ·
                  refine ⟨20861121496818184188161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222518629299393964673717 20861121496818184188161)
                  ·
                    rfl

theorem cell23_365642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_365642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365642 prefixEnd_365642 := by exact prefixLift 365642
  have htrace : WordTrace (prefixWord ++ tailWord_365642) baseStart_365642 baseEnd_365642 := by
    simpa [prefixWord, tailWord_365642, baseEnd_365642] using wordTrace_append hprefix tailTrace_365642
  have hstable : (prefixWord ++ tailWord_365642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365642).length < 2 ^ (prefixWord ++ tailWord_365642).sum := by decide
  have hdescent : baseEnd_365642 < baseStart_365642 := by decide
  rcases family_descends (prefixWord ++ tailWord_365642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365652 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_365652 : Nat := 118140960795 + 365652 * 2 ^ 59
def prefixEnd_365652 : Nat := 4983230072969 + 3 ^ 40 * 365652 * 2
def baseEnd_365652 : Nat := 187755228277908618568403

theorem tailTrace_365652 : CollatzResearch.WordTrace tailWord_365652 prefixEnd_365652 187755228277908618568403 := by
  unfold tailWord_365652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668212035656363617469605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8890949380875151489959473 6668212035656363617469605)
  ·
    refine ⟨1250289756685568178275551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6668212035656363617469605 1250289756685568178275551)
    ·
      refine ⟨1875434635028352267413327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250289756685568178275551 1875434635028352267413327)
      ·
        refine ⟨2813151952542528401119991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875434635028352267413327 2813151952542528401119991)
        ·
          refine ⟨4219727928813792601679987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2813151952542528401119991 4219727928813792601679987)
          ·
            refine ⟨6329591893220688902519981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4219727928813792601679987 6329591893220688902519981)
            ·
              refine ⟨2373596959957758338444993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6329591893220688902519981 2373596959957758338444993)
              ·
                refine ⟨1780197719968318753833745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2373596959957758338444993 1780197719968318753833745)
                ·
                  refine ⟨1335148289976239065375309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1780197719968318753833745 1335148289976239065375309)
                  ·
                    refine ⟨500680608741089649515741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1335148289976239065375309 500680608741089649515741)
                    ·
                      refine ⟨187755228277908618568403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 500680608741089649515741 187755228277908618568403)
                      ·
                        rfl

theorem cell23_365652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_365652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365652 prefixEnd_365652 := by exact prefixLift 365652
  have htrace : WordTrace (prefixWord ++ tailWord_365652) baseStart_365652 baseEnd_365652 := by
    simpa [prefixWord, tailWord_365652, baseEnd_365652] using wordTrace_append hprefix tailTrace_365652
  have hstable : (prefixWord ++ tailWord_365652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365652).length < 2 ^ (prefixWord ++ tailWord_365652).sum := by decide
  have hdescent : baseEnd_365652 < baseStart_365652 := by decide
  rcases family_descends (prefixWord ++ tailWord_365652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365655 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 4, 5]
def baseStart_365655 : Nat := 118140960795 + 365655 * 2 ^ 59
def prefixEnd_365655 : Nat := 4983230072969 + 3 ^ 40 * 365655 * 2
def baseEnd_365655 : Nat := 62585589573290702276963

theorem tailTrace_365655 : CollatzResearch.WordTrace tailWord_365655 prefixEnd_365655 62585589573290702276963 := by
  unfold tailWord_365655
  simp only [CollatzResearch.WordTrace]
  refine ⟨13336533490301858747298419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8891022326867905831532279 13336533490301858747298419)
  ·
    refine ⟨20004800235452788120947629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13336533490301858747298419 20004800235452788120947629)
    ·
      refine ⟨7501800088294795545355361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20004800235452788120947629 7501800088294795545355361)
      ·
        refine ⟨5626350066221096659016521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7501800088294795545355361 5626350066221096659016521)
        ·
          refine ⟨4219762549665822494262391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5626350066221096659016521 4219762549665822494262391)
          ·
            refine ⟨6329643824498733741393587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4219762549665822494262391 6329643824498733741393587)
            ·
              refine ⟨9494465736748100612090381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6329643824498733741393587 9494465736748100612090381)
              ·
                refine ⟨3560424651280537729533893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9494465736748100612090381 3560424651280537729533893)
                ·
                  refine ⟨667579622115100824287605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3560424651280537729533893 667579622115100824287605)
                  ·
                    refine ⟨62585589573290702276963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 667579622115100824287605 62585589573290702276963)
                    ·
                      rfl

theorem cell23_365655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_365655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365655 prefixEnd_365655 := by exact prefixLift 365655
  have htrace : WordTrace (prefixWord ++ tailWord_365655) baseStart_365655 baseEnd_365655 := by
    simpa [prefixWord, tailWord_365655, baseEnd_365655] using wordTrace_append hprefix tailTrace_365655
  have hstable : (prefixWord ++ tailWord_365655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365655).length < 2 ^ (prefixWord ++ tailWord_365655).sum := by decide
  have hdescent : baseEnd_365655 < baseStart_365655 := by decide
  rcases family_descends (prefixWord ++ tailWord_365655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365665 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_365665 : Nat := 118140960795 + 365665 * 2 ^ 59
def prefixEnd_365665 : Nat := 4983230072969 + 3 ^ 40 * 365665 * 2
def baseEnd_365665 : Nat := 187761903526417067705843

theorem tailTrace_365665 : CollatzResearch.WordTrace tailWord_365665 prefixEnd_365665 187761903526417067705843 := by
  unfold tailWord_365665
  simp only [CollatzResearch.WordTrace]
  refine ⟨13336898220265630455162449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8891265480177086970108299 13336898220265630455162449)
  ·
    refine ⟨10002673665199222841371837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13336898220265630455162449 10002673665199222841371837)
    ·
      refine ⟨3751002624449708565514439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10002673665199222841371837 3751002624449708565514439)
      ·
        refine ⟨5626503936674562848271659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751002624449708565514439 5626503936674562848271659)
        ·
          refine ⟨8439755905011844272407489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626503936674562848271659 8439755905011844272407489)
          ·
            refine ⟨6329816928758883204305617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8439755905011844272407489 6329816928758883204305617)
            ·
              refine ⟨4747362696569162403229213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6329816928758883204305617 4747362696569162403229213)
              ·
                refine ⟨1780261011213435901210955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4747362696569162403229213 1780261011213435901210955)
                ·
                  refine ⟨2670391516820153851816433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780261011213435901210955 2670391516820153851816433)
                  ·
                    refine ⟨2002793637615115388862325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2670391516820153851816433 2002793637615115388862325)
                    ·
                      refine ⟨187761903526417067705843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2002793637615115388862325 187761903526417067705843)
                      ·
                        rfl

theorem cell23_365665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_365665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365665 prefixEnd_365665 := by exact prefixLift 365665
  have htrace : WordTrace (prefixWord ++ tailWord_365665) baseStart_365665 baseEnd_365665 := by
    simpa [prefixWord, tailWord_365665, baseEnd_365665] using wordTrace_append hprefix tailTrace_365665
  have hstable : (prefixWord ++ tailWord_365665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365665).length < 2 ^ (prefixWord ++ tailWord_365665).sum := by decide
  have hdescent : baseEnd_365665 < baseStart_365665 := by decide
  rcases family_descends (prefixWord ++ tailWord_365665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365692 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_365692 : Nat := 118140960795 + 365692 * 2 ^ 59
def prefixEnd_365692 : Nat := 4983230072969 + 3 ^ 40 * 365692 * 2
def baseEnd_365692 : Nat := 187775767504088462068219

theorem tailTrace_365692 : CollatzResearch.WordTrace tailWord_365692 prefixEnd_365692 187775767504088462068219 := by
  unfold tailWord_365692
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668941495583907033197665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8891921994111876044263553 6668941495583907033197665)
  ·
    refine ⟨5001706121687930274898249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6668941495583907033197665 5001706121687930274898249)
    ·
      refine ⟨3751279591265947706173687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5001706121687930274898249 3751279591265947706173687)
      ·
        refine ⟨5626919386898921559260531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751279591265947706173687 5626919386898921559260531)
        ·
          refine ⟨8440379080348382338890797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626919386898921559260531 8440379080348382338890797)
          ·
            refine ⟨3165142155130643377084049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8440379080348382338890797 3165142155130643377084049)
            ·
              refine ⟨2373856616347982532813037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3165142155130643377084049 2373856616347982532813037)
              ·
                refine ⟨890196231130493449804889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2373856616347982532813037 890196231130493449804889)
                ·
                  refine ⟨667647173347870087353667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 890196231130493449804889 667647173347870087353667)
                  ·
                    refine ⟨1001470760021805131030501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 667647173347870087353667 1001470760021805131030501)
                    ·
                      refine ⟨187775767504088462068219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1001470760021805131030501 187775767504088462068219)
                      ·
                        rfl

theorem cell23_365692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_365692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365692 prefixEnd_365692 := by exact prefixLift 365692
  have htrace : WordTrace (prefixWord ++ tailWord_365692) baseStart_365692 baseEnd_365692 := by
    simpa [prefixWord, tailWord_365692, baseEnd_365692] using wordTrace_append hprefix tailTrace_365692
  have hstable : (prefixWord ++ tailWord_365692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365692).length < 2 ^ (prefixWord ++ tailWord_365692).sum := by decide
  have hdescent : baseEnd_365692 < baseStart_365692 := by decide
  rcases family_descends (prefixWord ++ tailWord_365692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365715 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 8]
def baseStart_365715 : Nat := 118140960795 + 365715 * 2 ^ 59
def prefixEnd_365715 : Nat := 4983230072969 + 3 ^ 40 * 365715 * 2
def baseEnd_365715 : Nat := 20865286395460208008957

theorem tailTrace_365715 : CollatzResearch.WordTrace tailWord_365715 prefixEnd_365715 20865286395460208008957 := by
  unfold tailWord_365715
  simp only [CollatzResearch.WordTrace]
  refine ⟨13338721870084488994482599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8892481246722992662988399 13338721870084488994482599)
  ·
    refine ⟨20008082805126733491723899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13338721870084488994482599 20008082805126733491723899)
    ·
      refine ⟨30012124207690100237585849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20008082805126733491723899 30012124207690100237585849)
      ·
        refine ⟨22509093155767575178189387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30012124207690100237585849 22509093155767575178189387)
        ·
          refine ⟨33763639733651362767284081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22509093155767575178189387 33763639733651362767284081)
          ·
            refine ⟨25322729800238522075463061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33763639733651362767284081 25322729800238522075463061)
            ·
              refine ⟨1187002959386180722287331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25322729800238522075463061 1187002959386180722287331)
              ·
                refine ⟨1780504439079271083430997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187002959386180722287331 1780504439079271083430997)
                ·
                  refine ⟨20865286395460208008957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1780504439079271083430997 20865286395460208008957)
                  ·
                    rfl

theorem cell23_365715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 8].length) (baseStart_365715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365715 prefixEnd_365715 := by exact prefixLift 365715
  have htrace : WordTrace (prefixWord ++ tailWord_365715) baseStart_365715 baseEnd_365715 := by
    simpa [prefixWord, tailWord_365715, baseEnd_365715] using wordTrace_append hprefix tailTrace_365715
  have hstable : (prefixWord ++ tailWord_365715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365715).length < 2 ^ (prefixWord ++ tailWord_365715).sum := by decide
  have hdescent : baseEnd_365715 < baseStart_365715 := by decide
  rcases family_descends (prefixWord ++ tailWord_365715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365719 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 3, 4]
def baseStart_365719 : Nat := 118140960795 + 365719 * 2 ^ 59
def prefixEnd_365719 : Nat := 4983230072969 + 3 ^ 40 * 365719 * 2
def baseEnd_365719 : Nat := 62596543827253285476865

theorem tailTrace_365719 : CollatzResearch.WordTrace tailWord_365719 prefixEnd_365719 62596543827253285476865 := by
  unfold tailWord_365719
  simp only [CollatzResearch.WordTrace]
  refine ⟨13338867762069997677628211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8892578508046665118418807 13338867762069997677628211)
  ·
    refine ⟨20008301643104996516442317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13338867762069997677628211 20008301643104996516442317)
    ·
      refine ⟨7503113116164373693665869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20008301643104996516442317 7503113116164373693665869)
      ·
        refine ⟨2813667418561640135124701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7503113116164373693665869 2813667418561640135124701)
        ·
          refine ⟨1055125281960615050671763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2813667418561640135124701 1055125281960615050671763)
          ·
            refine ⟨1582687922940922576007645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055125281960615050671763 1582687922940922576007645)
            ·
              refine ⟨593507971102845966002867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1582687922940922576007645 593507971102845966002867)
              ·
                refine ⟨890261956654268949004301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593507971102845966002867 890261956654268949004301)
                ·
                  refine ⟨333848233745350855876613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890261956654268949004301 333848233745350855876613)
                  ·
                    refine ⟨62596543827253285476865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 333848233745350855876613 62596543827253285476865)
                    ·
                      rfl

theorem cell23_365719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_365719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365719 prefixEnd_365719 := by exact prefixLift 365719
  have htrace : WordTrace (prefixWord ++ tailWord_365719) baseStart_365719 baseEnd_365719 := by
    simpa [prefixWord, tailWord_365719, baseEnd_365719] using wordTrace_append hprefix tailTrace_365719
  have hstable : (prefixWord ++ tailWord_365719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365719).length < 2 ^ (prefixWord ++ tailWord_365719).sum := by decide
  have hdescent : baseEnd_365719 < baseStart_365719 := by decide
  rcases family_descends (prefixWord ++ tailWord_365719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365755 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 5]
def baseStart_365755 : Nat := 118140960795 + 365755 * 2 ^ 59
def prefixEnd_365755 : Nat := 4983230072969 + 3 ^ 40 * 365755 * 2
def baseEnd_365755 : Nat := 187808116785321715580429

theorem tailTrace_365755 : CollatzResearch.WordTrace tailWord_365755 prefixEnd_365755 187808116785321715580429 := by
  unfold tailWord_365755
  simp only [CollatzResearch.WordTrace]
  refine ⟨13340180789939575825938719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8893453859959717217292479 13340180789939575825938719)
  ·
    refine ⟨20010271184909363738908079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13340180789939575825938719 20010271184909363738908079)
    ·
      refine ⟨30015406777364045608362119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20010271184909363738908079 30015406777364045608362119)
      ·
        refine ⟨45023110166046068412543179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30015406777364045608362119 45023110166046068412543179)
        ·
          refine ⟨67534665249069102618814769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45023110166046068412543179 67534665249069102618814769)
          ·
            refine ⟨50650998936801826964111077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67534665249069102618814769 50650998936801826964111077)
            ·
              refine ⟨9497062300650342555770827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50650998936801826964111077 9497062300650342555770827)
              ·
                refine ⟨14245593450975513833656241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9497062300650342555770827 14245593450975513833656241)
                ·
                  refine ⟨10684195088231635375242181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14245593450975513833656241 10684195088231635375242181)
                  ·
                    refine ⟨2003286579043431632857909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10684195088231635375242181 2003286579043431632857909)
                    ·
                      refine ⟨187808116785321715580429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2003286579043431632857909 187808116785321715580429)
                      ·
                        rfl

theorem cell23_365755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_365755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365755 prefixEnd_365755 := by exact prefixLift 365755
  have htrace : WordTrace (prefixWord ++ tailWord_365755) baseStart_365755 baseEnd_365755 := by
    simpa [prefixWord, tailWord_365755, baseEnd_365755] using wordTrace_append hprefix tailTrace_365755
  have hstable : (prefixWord ++ tailWord_365755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365755).length < 2 ^ (prefixWord ++ tailWord_365755).sum := by decide
  have hdescent : baseEnd_365755 < baseStart_365755 := by decide
  rcases family_descends (prefixWord ++ tailWord_365755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365792 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 1, 6]
def baseStart_365792 : Nat := 118140960795 + 365792 * 2 ^ 59
def prefixEnd_365792 : Nat := 4983230072969 + 3 ^ 40 * 365792 * 2
def baseEnd_365792 : Nat := 62609038523179356939253

theorem tailTrace_365792 : CollatzResearch.WordTrace tailWord_365792 prefixEnd_365792 62609038523179356939253 := by
  unfold tailWord_365792
  simp only [CollatzResearch.WordTrace]
  refine ⟨6670765145402765572517815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8894353527203687430023753 6670765145402765572517815)
  ·
    refine ⟨10006147718104148358776723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6670765145402765572517815 10006147718104148358776723)
    ·
      refine ⟨15009221577156222538165085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10006147718104148358776723 15009221577156222538165085)
      ·
        refine ⟨5628458091433583451811907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15009221577156222538165085 5628458091433583451811907)
        ·
          refine ⟨8442687137150375177717861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5628458091433583451811907 8442687137150375177717861)
          ·
            refine ⟨1583003838215695345822099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8442687137150375177717861 1583003838215695345822099)
            ·
              refine ⟨2374505757323543018733149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583003838215695345822099 2374505757323543018733149)
              ·
                refine ⟨890439658996328632024931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2374505757323543018733149 890439658996328632024931)
                ·
                  refine ⟨1335659488494492948037397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 890439658996328632024931 1335659488494492948037397)
                  ·
                    refine ⟨62609038523179356939253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1335659488494492948037397 62609038523179356939253)
                    ·
                      rfl

theorem cell23_365792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_365792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365792 prefixEnd_365792 := by exact prefixLift 365792
  have htrace : WordTrace (prefixWord ++ tailWord_365792) baseStart_365792 baseEnd_365792 := by
    simpa [prefixWord, tailWord_365792, baseEnd_365792] using wordTrace_append hprefix tailTrace_365792
  have hstable : (prefixWord ++ tailWord_365792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365792).length < 2 ^ (prefixWord ++ tailWord_365792).sum := by decide
  have hdescent : baseEnd_365792 < baseStart_365792 := by decide
  rcases family_descends (prefixWord ++ tailWord_365792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365810 : List Nat := [3, 2, 1, 3, 3, 1, 2, 3, 1, 1, 3]
def baseStart_365810 : Nat := 118140960795 + 365810 * 2 ^ 59
def prefixEnd_365810 : Nat := 4983230072969 + 3 ^ 40 * 365810 * 2
def baseEnd_365810 : Nat := 187836358221319000392677

theorem tailTrace_365810 : CollatzResearch.WordTrace tailWord_365810 prefixEnd_365810 187836358221319000392677 := by
  unfold tailWord_365810
  simp only [CollatzResearch.WordTrace]
  refine ⟨3335546701185080054797721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8894791203160213479460589 3335546701185080054797721)
  ·
    refine ⟨2501660025888810041098291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3335546701185080054797721 2501660025888810041098291)
    ·
      refine ⟨3752490038833215061647437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2501660025888810041098291 3752490038833215061647437)
      ·
        refine ⟨1407183764562455648117789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3752490038833215061647437 1407183764562455648117789)
        ·
          refine ⟨527693911710920868044171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1407183764562455648117789 527693911710920868044171)
          ·
            refine ⟨791540867566381302066257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527693911710920868044171 791540867566381302066257)
            ·
              refine ⟨593655650674785976549693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791540867566381302066257 593655650674785976549693)
              ·
                refine ⟨222620869003044741206135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 593655650674785976549693 222620869003044741206135)
                ·
                  refine ⟨333931303504567111809203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222620869003044741206135 333931303504567111809203)
                  ·
                    refine ⟨500896955256850667713805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 333931303504567111809203 500896955256850667713805)
                    ·
                      refine ⟨187836358221319000392677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 500896955256850667713805 187836358221319000392677)
                      ·
                        rfl

theorem cell23_365810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_365810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365810 prefixEnd_365810 := by exact prefixLift 365810
  have htrace : WordTrace (prefixWord ++ tailWord_365810) baseStart_365810 baseEnd_365810 := by
    simpa [prefixWord, tailWord_365810, baseEnd_365810] using wordTrace_append hprefix tailTrace_365810
  have hstable : (prefixWord ++ tailWord_365810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365810).length < 2 ^ (prefixWord ++ tailWord_365810).sum := by decide
  have hdescent : baseEnd_365810 < baseStart_365810 := by decide
  rcases family_descends (prefixWord ++ tailWord_365810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365833 : List Nat := [1, 2, 1, 1, 3, 3, 1, 6, 1, 2, 2]
def baseStart_365833 : Nat := 118140960795 + 365833 * 2 ^ 59
def prefixEnd_365833 : Nat := 4983230072969 + 3 ^ 40 * 365833 * 2
def baseEnd_365833 : Nat := 187848168276372410405071

theorem tailTrace_365833 : CollatzResearch.WordTrace tailWord_365833 prefixEnd_365833 187848168276372410405071 := by
  unfold tailWord_365833
  simp only [CollatzResearch.WordTrace]
  refine ⟨13343025683656995147278153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8895350455771330098185435 13343025683656995147278153)
  ·
    refine ⟨10007269262742746360458615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13343025683656995147278153 10007269262742746360458615)
    ·
      refine ⟨15010903894114119540687923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10007269262742746360458615 15010903894114119540687923)
      ·
        refine ⟨22516355841171179311031885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15010903894114119540687923 22516355841171179311031885)
        ·
          refine ⟨8443633440439192241636957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22516355841171179311031885 8443633440439192241636957)
          ·
            refine ⟨3166362540164697090613859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8443633440439192241636957 3166362540164697090613859)
            ·
              refine ⟨4749543810247045635920789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166362540164697090613859 4749543810247045635920789)
              ·
                refine ⟨222634866105330264183787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4749543810247045635920789 222634866105330264183787)
                ·
                  refine ⟨333952299157995396275681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222634866105330264183787 333952299157995396275681)
                  ·
                    refine ⟨250464224368496547206761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 333952299157995396275681 250464224368496547206761)
                    ·
                      refine ⟨187848168276372410405071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250464224368496547206761 187848168276372410405071)
                      ·
                        rfl

theorem cell23_365833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 1, 2, 2].length) (baseStart_365833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365833 prefixEnd_365833 := by exact prefixLift 365833
  have htrace : WordTrace (prefixWord ++ tailWord_365833) baseStart_365833 baseEnd_365833 := by
    simpa [prefixWord, tailWord_365833, baseEnd_365833] using wordTrace_append hprefix tailTrace_365833
  have hstable : (prefixWord ++ tailWord_365833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365833).length < 2 ^ (prefixWord ++ tailWord_365833).sum := by decide
  have hdescent : baseEnd_365833 < baseStart_365833 := by decide
  rcases family_descends (prefixWord ++ tailWord_365833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365852 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 2, 7]
def baseStart_365852 : Nat := 118140960795 + 365852 * 2 ^ 59
def prefixEnd_365852 : Nat := 4983230072969 + 3 ^ 40 * 365852 * 2
def baseEnd_365852 : Nat := 62619308136269278689161

theorem tailTrace_365852 : CollatzResearch.WordTrace tailWord_365852 prefixEnd_365852 62619308136269278689161 := by
  unfold tailWord_365852
  simp only [CollatzResearch.WordTrace]
  refine ⟨6671859335294080696109905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8895812447058774261479873 6671859335294080696109905)
  ·
    refine ⟨5003894501470560522082429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6671859335294080696109905 5003894501470560522082429)
    ·
      refine ⟨1876460438051460195780911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5003894501470560522082429 1876460438051460195780911)
      ·
        refine ⟨2814690657077190293671367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876460438051460195780911 2814690657077190293671367)
        ·
          refine ⟨4222035985615785440507051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2814690657077190293671367 4222035985615785440507051)
          ·
            refine ⟨6333053978423678160760577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222035985615785440507051 6333053978423678160760577)
            ·
              refine ⟨4749790483817758620570433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6333053978423678160760577 4749790483817758620570433)
              ·
                refine ⟨3562342862863318965427825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4749790483817758620570433 3562342862863318965427825)
                ·
                  refine ⟨2671757147147489224070869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3562342862863318965427825 2671757147147489224070869)
                  ·
                    refine ⟨62619308136269278689161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2671757147147489224070869 62619308136269278689161)
                    ·
                      rfl

theorem cell23_365852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_365852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365852 prefixEnd_365852 := by exact prefixLift 365852
  have htrace : WordTrace (prefixWord ++ tailWord_365852) baseStart_365852 baseEnd_365852 := by
    simpa [prefixWord, tailWord_365852, baseEnd_365852] using wordTrace_append hprefix tailTrace_365852
  have hstable : (prefixWord ++ tailWord_365852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365852).length < 2 ^ (prefixWord ++ tailWord_365852).sum := by decide
  have hdescent : baseEnd_365852 < baseStart_365852 := by decide
  rcases family_descends (prefixWord ++ tailWord_365852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365853 : List Nat := [1, 4, 2, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_365853 : Nat := 118140960795 + 365853 * 2 ^ 59
def prefixEnd_365853 : Nat := 4983230072969 + 3 ^ 40 * 365853 * 2
def baseEnd_365853 : Nat := 187858437889462332154979

theorem tailTrace_365853 : CollatzResearch.WordTrace tailWord_365853 prefixEnd_365853 187858437889462332154979 := by
  unfold tailWord_365853
  simp only [CollatzResearch.WordTrace]
  refine ⟨13343755143584538563006213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8895836762389692375337475 13343755143584538563006213)
  ·
    refine ⟨2501954089422100980563665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13343755143584538563006213 2501954089422100980563665)
    ·
      refine ⟨1876465567066575735422749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2501954089422100980563665 1876465567066575735422749)
      ·
        refine ⟨703674587649965900783531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1876465567066575735422749 703674587649965900783531)
        ·
          refine ⟨1055511881474948851175297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703674587649965900783531 1055511881474948851175297)
          ·
            refine ⟨791633911106211638381473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1055511881474948851175297 791633911106211638381473)
            ·
              refine ⟨593725433329658728786105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791633911106211638381473 593725433329658728786105)
              ·
                refine ⟨445294074997244046589579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593725433329658728786105 445294074997244046589579)
                ·
                  refine ⟨667941112495866069884369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445294074997244046589579 667941112495866069884369)
                  ·
                    refine ⟨500955834371899552413277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 667941112495866069884369 500955834371899552413277)
                    ·
                      refine ⟨187858437889462332154979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 500955834371899552413277 187858437889462332154979)
                      ·
                        rfl

theorem cell23_365853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_365853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365853 prefixEnd_365853 := by exact prefixLift 365853
  have htrace : WordTrace (prefixWord ++ tailWord_365853) baseStart_365853 baseEnd_365853 := by
    simpa [prefixWord, tailWord_365853, baseEnd_365853] using wordTrace_append hprefix tailTrace_365853
  have hstable : (prefixWord ++ tailWord_365853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365853).length < 2 ^ (prefixWord ++ tailWord_365853).sum := by decide
  have hdescent : baseEnd_365853 < baseStart_365853 := by decide
  rcases family_descends (prefixWord ++ tailWord_365853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365856 : List Nat := [2, 1, 1, 5, 3, 2, 2, 7]
def baseStart_365856 : Nat := 118140960795 + 365856 * 2 ^ 59
def prefixEnd_365856 : Nat := 4983230072969 + 3 ^ 40 * 365856 * 2
def baseEnd_365856 : Nat := 6957776975237993348795

theorem tailTrace_365856 : CollatzResearch.WordTrace tailWord_365856 prefixEnd_365856 6957776975237993348795 := by
  unfold tailWord_365856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6671932281286835037682711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8895909708382446716910281 6671932281286835037682711)
  ·
    refine ⟨10007898421930252556524067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6671932281286835037682711 10007898421930252556524067)
    ·
      refine ⟨15011847632895378834786101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10007898421930252556524067 15011847632895378834786101)
      ·
        refine ⟨1407360715583941765761197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15011847632895378834786101 1407360715583941765761197)
        ·
          refine ⟨527760268343978162160449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1407360715583941765761197 527760268343978162160449)
          ·
            refine ⟨395820201257983621620337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527760268343978162160449 395820201257983621620337)
            ·
              refine ⟨296865150943487716215253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395820201257983621620337 296865150943487716215253)
              ·
                refine ⟨6957776975237993348795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 296865150943487716215253 6957776975237993348795)
                ·
                  rfl

theorem cell23_365856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 7].length) (baseStart_365856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365856 prefixEnd_365856 := by exact prefixLift 365856
  have htrace : WordTrace (prefixWord ++ tailWord_365856) baseStart_365856 baseEnd_365856 := by
    simpa [prefixWord, tailWord_365856, baseEnd_365856] using wordTrace_append hprefix tailTrace_365856
  have hstable : (prefixWord ++ tailWord_365856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365856).length < 2 ^ (prefixWord ++ tailWord_365856).sum := by decide
  have hdescent : baseEnd_365856 < baseStart_365856 := by decide
  rcases family_descends (prefixWord ++ tailWord_365856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365894 : List Nat := [6, 1, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_365894 : Nat := 118140960795 + 365894 * 2 ^ 59
def prefixEnd_365894 : Nat := 4983230072969 + 3 ^ 40 * 365894 * 2
def baseEnd_365894 : Nat := 62626496865432223914097

theorem tailTrace_365894 : CollatzResearch.WordTrace tailWord_365894 prefixEnd_365894 62626496865432223914097 := by
  unfold tailWord_365894
  simp only [CollatzResearch.WordTrace]
  refine ⟨417039079263625080164023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8896833690957335043499157 417039079263625080164023)
  ·
    refine ⟨625558618895437620246035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 417039079263625080164023 625558618895437620246035)
    ·
      refine ⟨938337928343156430369053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 625558618895437620246035 938337928343156430369053)
      ·
        refine ⟨351876723128683661388395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 938337928343156430369053 351876723128683661388395)
        ·
          refine ⟨527815084693025492082593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351876723128683661388395 527815084693025492082593)
          ·
            refine ⟨395861313519769119061945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527815084693025492082593 395861313519769119061945)
            ·
              refine ⟨296895985139826839296459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395861313519769119061945 296895985139826839296459)
              ·
                refine ⟨445343977709740258944689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296895985139826839296459 445343977709740258944689)
                ·
                  refine ⟨334007983282305194208517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445343977709740258944689 334007983282305194208517)
                  ·
                    refine ⟨62626496865432223914097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 334007983282305194208517 62626496865432223914097)
                    ·
                      rfl

theorem cell23_365894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_365894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365894 prefixEnd_365894 := by exact prefixLift 365894
  have htrace : WordTrace (prefixWord ++ tailWord_365894) baseStart_365894 baseEnd_365894 := by
    simpa [prefixWord, tailWord_365894, baseEnd_365894] using wordTrace_append hprefix tailTrace_365894
  have hstable : (prefixWord ++ tailWord_365894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365894).length < 2 ^ (prefixWord ++ tailWord_365894).sum := by decide
  have hdescent : baseEnd_365894 < baseStart_365894 := by decide
  rcases family_descends (prefixWord ++ tailWord_365894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365900 : List Nat := [2, 2, 1, 3, 2, 4, 2, 1, 2, 1, 3]
def baseStart_365900 : Nat := 118140960795 + 365900 * 2 ^ 59
def prefixEnd_365900 : Nat := 4983230072969 + 3 ^ 40 * 365900 * 2
def baseEnd_365900 : Nat := 187882571480223648267263

theorem tailTrace_365900 : CollatzResearch.WordTrace tailWord_365900 prefixEnd_365900 187882571480223648267263 := by
  unfold tailWord_365900
  simp only [CollatzResearch.WordTrace]
  refine ⟨6672734687207132794983577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8896979582942843726644769 6672734687207132794983577)
  ·
    refine ⟨5004551015405349596237683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6672734687207132794983577 5004551015405349596237683)
    ·
      refine ⟨7506826523108024394356525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5004551015405349596237683 7506826523108024394356525)
      ·
        refine ⟨2815059946165509147883697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7506826523108024394356525 2815059946165509147883697)
        ·
          refine ⟨2111294959624131860912773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2815059946165509147883697 2111294959624131860912773)
          ·
            refine ⟨395867804929524723921145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2111294959624131860912773 395867804929524723921145)
            ·
              refine ⟨296900853697143542940859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395867804929524723921145 296900853697143542940859)
              ·
                refine ⟨445351280545715314411289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296900853697143542940859 445351280545715314411289)
                ·
                  refine ⟨334013460409286485808467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445351280545715314411289 334013460409286485808467)
                  ·
                    refine ⟨501020190613929728712701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 334013460409286485808467 501020190613929728712701)
                    ·
                      refine ⟨187882571480223648267263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 501020190613929728712701 187882571480223648267263)
                      ·
                        rfl

theorem cell23_365900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_365900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365900 prefixEnd_365900 := by exact prefixLift 365900
  have htrace : WordTrace (prefixWord ++ tailWord_365900) baseStart_365900 baseEnd_365900 := by
    simpa [prefixWord, tailWord_365900, baseEnd_365900] using wordTrace_append hprefix tailTrace_365900
  have hstable : (prefixWord ++ tailWord_365900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365900).length < 2 ^ (prefixWord ++ tailWord_365900).sum := by decide
  have hdescent : baseEnd_365900 < baseStart_365900 := by decide
  rcases family_descends (prefixWord ++ tailWord_365900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365906 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_365906 : Nat := 118140960795 + 365906 * 2 ^ 59
def prefixEnd_365906 : Nat := 4983230072969 + 3 ^ 40 * 365906 * 2
def baseEnd_365906 : Nat := 187885652364150624792235

theorem tailTrace_365906 : CollatzResearch.WordTrace tailWord_365906 prefixEnd_365906 187885652364150624792235 := by
  unfold tailWord_365906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3336422053098132153671393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8897125474928352409790381 3336422053098132153671393)
  ·
    refine ⟨2502316539823599115253545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3336422053098132153671393 2502316539823599115253545)
    ·
      refine ⟨1876737404867699336440159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2502316539823599115253545 1876737404867699336440159)
      ·
        refine ⟨2815106107301549004660239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876737404867699336440159 2815106107301549004660239)
        ·
          refine ⟨4222659160952323506990359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815106107301549004660239 4222659160952323506990359)
          ·
            refine ⟨6333988741428485260485539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222659160952323506990359 6333988741428485260485539)
            ·
              refine ⟨9500983112142727890728309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6333988741428485260485539 9500983112142727890728309)
              ·
                refine ⟨890717166763380739755779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9500983112142727890728309 890717166763380739755779)
                ·
                  refine ⟨1336075750145071109633669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 890717166763380739755779 1336075750145071109633669)
                  ·
                    refine ⟨250514203152200833056313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1336075750145071109633669 250514203152200833056313)
                    ·
                      refine ⟨187885652364150624792235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250514203152200833056313 187885652364150624792235)
                      ·
                        rfl

theorem cell23_365906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_365906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365906 prefixEnd_365906 := by exact prefixLift 365906
  have htrace : WordTrace (prefixWord ++ tailWord_365906) baseStart_365906 baseEnd_365906 := by
    simpa [prefixWord, tailWord_365906, baseEnd_365906] using wordTrace_append hprefix tailTrace_365906
  have hstable : (prefixWord ++ tailWord_365906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365906).length < 2 ^ (prefixWord ++ tailWord_365906).sum := by decide
  have hdescent : baseEnd_365906 < baseStart_365906 := by decide
  rcases family_descends (prefixWord ++ tailWord_365906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365909 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_365909 : Nat := 118140960795 + 365909 * 2 ^ 59
def prefixEnd_365909 : Nat := 4983230072969 + 3 ^ 40 * 365909 * 2
def baseEnd_365909 : Nat := 187887192806114113054721

theorem tailTrace_365909 : CollatzResearch.WordTrace tailWord_365909 prefixEnd_365909 187887192806114113054721 := by
  unfold tailWord_365909
  simp only [CollatzResearch.WordTrace]
  refine ⟨13345797631381660127044781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8897198420921106751363187 13345797631381660127044781)
  ·
    refine ⟨5004674111768122547641793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13345797631381660127044781 5004674111768122547641793)
    ·
      refine ⟨3753505583826091910731345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5004674111768122547641793 3753505583826091910731345)
      ·
        refine ⟨2815129187869568933048509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3753505583826091910731345 2815129187869568933048509)
        ·
          refine ⟨1055673445451088349893191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2815129187869568933048509 1055673445451088349893191)
          ·
            refine ⟨1583510168176632524839787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055673445451088349893191 1583510168176632524839787)
            ·
              refine ⟨2375265252264948787259681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583510168176632524839787 2375265252264948787259681)
              ·
                refine ⟨1781448939198711590444761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2375265252264948787259681 1781448939198711590444761)
                ·
                  refine ⟨1336086704399033692833571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1781448939198711590444761 1336086704399033692833571)
                  ·
                    refine ⟨2004130056598550539250357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1336086704399033692833571 2004130056598550539250357)
                    ·
                      refine ⟨187887192806114113054721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2004130056598550539250357 187887192806114113054721)
                      ·
                        rfl

theorem cell23_365909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_365909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365909 prefixEnd_365909 := by exact prefixLift 365909
  have htrace : WordTrace (prefixWord ++ tailWord_365909) baseStart_365909 baseEnd_365909 := by
    simpa [prefixWord, tailWord_365909, baseEnd_365909] using wordTrace_append hprefix tailTrace_365909
  have hstable : (prefixWord ++ tailWord_365909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365909).length < 2 ^ (prefixWord ++ tailWord_365909).sum := by decide
  have hdescent : baseEnd_365909 < baseStart_365909 := by decide
  rcases family_descends (prefixWord ++ tailWord_365909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365912 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 9]
def baseStart_365912 : Nat := 118140960795 + 365912 * 2 ^ 59
def prefixEnd_365912 : Nat := 4983230072969 + 3 ^ 40 * 365912 * 2
def baseEnd_365912 : Nat := 20876525916453066813023

theorem tailTrace_365912 : CollatzResearch.WordTrace tailWord_365912 prefixEnd_365912 20876525916453066813023 := by
  unfold tailWord_365912
  simp only [CollatzResearch.WordTrace]
  refine ⟨6672953525185395819701995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8897271366913861092935993 6672953525185395819701995)
  ·
    refine ⟨10009430287778093729552993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6672953525185395819701995 10009430287778093729552993)
    ·
      refine ⟨7507072715833570297164745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10009430287778093729552993 7507072715833570297164745)
      ·
        refine ⟨5630304536875177722873559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7507072715833570297164745 5630304536875177722873559)
        ·
          refine ⟨8445456805312766584310339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5630304536875177722873559 8445456805312766584310339)
          ·
            refine ⟨12668185207969149876465509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8445456805312766584310339 12668185207969149876465509)
            ·
              refine ⟨2375284726494215601837283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12668185207969149876465509 2375284726494215601837283)
              ·
                refine ⟨3562927089741323402755925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375284726494215601837283 3562927089741323402755925)
                ·
                  refine ⟨20876525916453066813023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3562927089741323402755925 20876525916453066813023)
                  ·
                    rfl

theorem cell23_365912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 9].length) (baseStart_365912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365912 prefixEnd_365912 := by exact prefixLift 365912
  have htrace : WordTrace (prefixWord ++ tailWord_365912) baseStart_365912 baseEnd_365912 := by
    simpa [prefixWord, tailWord_365912, baseEnd_365912] using wordTrace_append hprefix tailTrace_365912
  have hstable : (prefixWord ++ tailWord_365912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365912).length < 2 ^ (prefixWord ++ tailWord_365912).sum := by decide
  have hdescent : baseEnd_365912 < baseStart_365912 := by decide
  rcases family_descends (prefixWord ++ tailWord_365912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365956 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_365956 : Nat := 118140960795 + 365956 * 2 ^ 59
def prefixEnd_365956 : Nat := 4983230072969 + 3 ^ 40 * 365956 * 2
def baseEnd_365956 : Nat := 187911326396875429167005

theorem tailTrace_365956 : CollatzResearch.WordTrace tailWord_365956 prefixEnd_365956 187911326396875429167005 := by
  unfold tailWord_365956
  simp only [CollatzResearch.WordTrace]
  refine ⟨6673755931105693577002861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8898341241474258102670481 6673755931105693577002861)
  ·
    refine ⟨2502658474164635091376073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6673755931105693577002861 2502658474164635091376073)
    ·
      refine ⟨1876993855623476318532055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2502658474164635091376073 1876993855623476318532055)
      ·
        refine ⟨2815490783435214477798083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876993855623476318532055 2815490783435214477798083)
        ·
          refine ⟨4223236175152821716697125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815490783435214477798083 4223236175152821716697125)
          ·
            refine ⟨791856782841154071880711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4223236175152821716697125 791856782841154071880711)
            ·
              refine ⟨1187785174261731107821067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791856782841154071880711 1187785174261731107821067)
              ·
                refine ⟨1781677761392596661731601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187785174261731107821067 1781677761392596661731601)
                ·
                  refine ⟨1336258321044447496298701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1781677761392596661731601 1336258321044447496298701)
                  ·
                    refine ⟨501096870391667811112013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1336258321044447496298701 501096870391667811112013)
                    ·
                      refine ⟨187911326396875429167005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 501096870391667811112013 187911326396875429167005)
                      ·
                        rfl

theorem cell23_365956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_365956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365956 prefixEnd_365956 := by exact prefixLift 365956
  have htrace : WordTrace (prefixWord ++ tailWord_365956) baseStart_365956 baseEnd_365956 := by
    simpa [prefixWord, tailWord_365956, baseEnd_365956] using wordTrace_append hprefix tailTrace_365956
  have hstable : (prefixWord ++ tailWord_365956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365956).length < 2 ^ (prefixWord ++ tailWord_365956).sum := by decide
  have hdescent : baseEnd_365956 < baseStart_365956 := by decide
  rcases family_descends (prefixWord ++ tailWord_365956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365976 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 1, 7]
def baseStart_365976 : Nat := 118140960795 + 365976 * 2 ^ 59
def prefixEnd_365976 : Nat := 4983230072969 + 3 ^ 40 * 365976 * 2
def baseEnd_365976 : Nat := 62640532003321783638971

theorem tailTrace_365976 : CollatzResearch.WordTrace tailWord_365976 prefixEnd_365976 62640532003321783638971 := by
  unfold tailWord_365976
  simp only [CollatzResearch.WordTrace]
  refine ⟨6674120661069465284866891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8898827548092620379822521 6674120661069465284866891)
  ·
    refine ⟨10011180991604197927300337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6674120661069465284866891 10011180991604197927300337)
    ·
      refine ⟨7508385743703148445475253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10011180991604197927300337 7508385743703148445475253)
      ·
        refine ⟨703911163472170166763305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7508385743703148445475253 703911163472170166763305)
        ·
          refine ⟨527933372604127625072479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 703911163472170166763305 527933372604127625072479)
          ·
            refine ⟨791900058906191437608719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527933372604127625072479 791900058906191437608719)
            ·
              refine ⟨1187850088359287156413079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791900058906191437608719 1187850088359287156413079)
              ·
                refine ⟨1781775132538930734619619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187850088359287156413079 1781775132538930734619619)
                ·
                  refine ⟨2672662698808396101929429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781775132538930734619619 2672662698808396101929429)
                  ·
                    refine ⟨62640532003321783638971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2672662698808396101929429 62640532003321783638971)
                    ·
                      rfl

theorem cell23_365976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_365976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365976 prefixEnd_365976 := by exact prefixLift 365976
  have htrace : WordTrace (prefixWord ++ tailWord_365976) baseStart_365976 baseEnd_365976 := by
    simpa [prefixWord, tailWord_365976, baseEnd_365976] using wordTrace_append hprefix tailTrace_365976
  have hstable : (prefixWord ++ tailWord_365976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365976).length < 2 ^ (prefixWord ++ tailWord_365976).sum := by decide
  have hdescent : baseEnd_365976 < baseStart_365976 := by decide
  rcases family_descends (prefixWord ++ tailWord_365976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365980 : List Nat := [2, 2, 3, 4, 1, 1, 2, 3, 5]
def baseStart_365980 : Nat := 118140960795 + 365980 * 2 ^ 59
def prefixEnd_365980 : Nat := 4983230072969 + 3 ^ 40 * 365980 * 2
def baseEnd_365980 : Nat := 20880405548064815029655

theorem tailTrace_365980 : CollatzResearch.WordTrace tailWord_365980 prefixEnd_365980 20880405548064815029655 := by
  unfold tailWord_365980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6674193607062219626439697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8898924809416292835252929 6674193607062219626439697)
  ·
    refine ⟨5005645205296664719829773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6674193607062219626439697 5005645205296664719829773)
    ·
      refine ⟨1877116951986249269936165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5005645205296664719829773 1877116951986249269936165)
      ·
        refine ⟨351959428497421738113031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1877116951986249269936165 351959428497421738113031)
        ·
          refine ⟨527939142746132607169547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351959428497421738113031 527939142746132607169547)
          ·
            refine ⟨791908714119198910754321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527939142746132607169547 791908714119198910754321)
            ·
              refine ⟨593931535589399183065741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791908714119198910754321 593931535589399183065741)
              ·
                refine ⟨222724325846024693649653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 593931535589399183065741 222724325846024693649653)
                ·
                  refine ⟨20880405548064815029655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222724325846024693649653 20880405548064815029655)
                  ·
                    rfl

theorem cell23_365980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_365980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365980 prefixEnd_365980 := by exact prefixLift 365980
  have htrace : WordTrace (prefixWord ++ tailWord_365980) baseStart_365980 baseEnd_365980 := by
    simpa [prefixWord, tailWord_365980, baseEnd_365980] using wordTrace_append hprefix tailTrace_365980
  have hstable : (prefixWord ++ tailWord_365980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365980).length < 2 ^ (prefixWord ++ tailWord_365980).sum := by decide
  have hdescent : baseEnd_365980 < baseStart_365980 := by decide
  rcases family_descends (prefixWord ++ tailWord_365980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365996 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 2, 4, 2]
def baseStart_365996 : Nat := 118140960795 + 365996 * 2 ^ 59
def prefixEnd_365996 : Nat := 4983230072969 + 3 ^ 40 * 365996 * 2
def baseEnd_365996 : Nat := 187931865623055272666821

theorem tailTrace_365996 : CollatzResearch.WordTrace tailWord_365996 prefixEnd_365996 187931865623055272666821 := by
  unfold tailWord_365996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6674485391033236992730921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8899313854710982656974561 6674485391033236992730921)
  ·
    refine ⟨5005864043274927744548191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6674485391033236992730921 5005864043274927744548191)
    ·
      refine ⟨7508796064912391616822287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5005864043274927744548191 7508796064912391616822287)
      ·
        refine ⟨11263194097368587425233431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7508796064912391616822287 11263194097368587425233431)
        ·
          refine ⟨16894791146052881137850147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11263194097368587425233431 16894791146052881137850147)
          ·
            refine ⟨25342186719079321706775221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16894791146052881137850147 25342186719079321706775221)
            ·
              refine ⟨2375830004913686410010177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25342186719079321706775221 2375830004913686410010177)
              ·
                refine ⟨1781872503685264807507633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2375830004913686410010177 1781872503685264807507633)
                ·
                  refine ⟨1336404377763948605630725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1781872503685264807507633 1336404377763948605630725)
                  ·
                    refine ⟨250575820830740363555761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1336404377763948605630725 250575820830740363555761)
                    ·
                      refine ⟨187931865623055272666821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250575820830740363555761 187931865623055272666821)
                      ·
                        rfl

theorem cell23_365996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 4, 2].length) (baseStart_365996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_365996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_365996 prefixEnd_365996 := by exact prefixLift 365996
  have htrace : WordTrace (prefixWord ++ tailWord_365996) baseStart_365996 baseEnd_365996 := by
    simpa [prefixWord, tailWord_365996, baseEnd_365996] using wordTrace_append hprefix tailTrace_365996
  have hstable : (prefixWord ++ tailWord_365996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365996).length < 2 ^ (prefixWord ++ tailWord_365996).sum := by decide
  have hdescent : baseEnd_365996 < baseStart_365996 := by decide
  rcases family_descends (prefixWord ++ tailWord_365996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366019 : List Nat := [1, 1, 1, 3, 1, 1, 4, 5, 6]
def baseStart_366019 : Nat := 118140960795 + 366019 * 2 ^ 59
def prefixEnd_366019 : Nat := 4983230072969 + 3 ^ 40 * 366019 * 2
def baseEnd_366019 : Nat := 20882630630900964742135

theorem tailTrace_366019 : CollatzResearch.WordTrace tailWord_366019 prefixEnd_366019 20882630630900964742135 := by
  unfold tailWord_366019
  simp only [CollatzResearch.WordTrace]
  refine ⟨13349809660983148913549111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8899873107322099275699407 13349809660983148913549111)
  ·
    refine ⟨20024714491474723370323667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13349809660983148913549111 20024714491474723370323667)
    ·
      refine ⟨30037071737212085055485501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20024714491474723370323667 30037071737212085055485501)
      ·
        refine ⟨11263901901454531895807063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30037071737212085055485501 11263901901454531895807063)
        ·
          refine ⟨16895852852181797843710595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11263901901454531895807063 16895852852181797843710595)
          ·
            refine ⟨25343779278272696765565893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16895852852181797843710595 25343779278272696765565893)
            ·
              refine ⟨4751958614676130643543605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25343779278272696765565893 4751958614676130643543605)
              ·
                refine ⟨445496120125887247832213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4751958614676130643543605 445496120125887247832213)
                ·
                  refine ⟨20882630630900964742135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 445496120125887247832213 20882630630900964742135)
                  ·
                    rfl

theorem cell23_366019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 6].length) (baseStart_366019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366019 prefixEnd_366019 := by exact prefixLift 366019
  have htrace : WordTrace (prefixWord ++ tailWord_366019) baseStart_366019 baseEnd_366019 := by
    simpa [prefixWord, tailWord_366019, baseEnd_366019] using wordTrace_append hprefix tailTrace_366019
  have hstable : (prefixWord ++ tailWord_366019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366019).length < 2 ^ (prefixWord ++ tailWord_366019).sum := by decide
  have hdescent : baseEnd_366019 < baseStart_366019 := by decide
  rcases family_descends (prefixWord ++ tailWord_366019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366063 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 3, 1, 3]
def baseStart_366063 : Nat := 118140960795 + 366063 * 2 ^ 59
def prefixEnd_366063 : Nat := 4983230072969 + 3 ^ 40 * 366063 * 2
def baseEnd_366063 : Nat := 187966268826906510529013

theorem tailTrace_366063 : CollatzResearch.WordTrace tailWord_366063 prefixEnd_366063 187966268826906510529013 := by
  unfold tailWord_366063
  simp only [CollatzResearch.WordTrace]
  refine ⟨13351414472823744428150843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8900942981882496285433895 13351414472823744428150843)
  ·
    refine ⟨20027121709235616642226265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13351414472823744428150843 20027121709235616642226265)
    ·
      refine ⟨15020341281926712481669699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20027121709235616642226265 15020341281926712481669699)
      ·
        refine ⟨22530511922890068722504549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15020341281926712481669699 22530511922890068722504549)
        ·
          refine ⟨4224470985541887885469603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22530511922890068722504549 4224470985541887885469603)
          ·
            refine ⟨6336706478312831828204405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4224470985541887885469603 6336706478312831828204405)
            ·
              refine ⟨594066232341827983894163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6336706478312831828204405 594066232341827983894163)
              ·
                refine ⟨891099348512741975841245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594066232341827983894163 891099348512741975841245)
                ·
                  refine ⟨334162255692278240940467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 891099348512741975841245 334162255692278240940467)
                  ·
                    refine ⟨501243383538417361410701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 334162255692278240940467 501243383538417361410701)
                    ·
                      refine ⟨187966268826906510529013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 501243383538417361410701 187966268826906510529013)
                      ·
                        rfl

theorem cell23_366063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 1, 3].length) (baseStart_366063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366063 prefixEnd_366063 := by exact prefixLift 366063
  have htrace : WordTrace (prefixWord ++ tailWord_366063) baseStart_366063 baseEnd_366063 := by
    simpa [prefixWord, tailWord_366063, baseEnd_366063] using wordTrace_append hprefix tailTrace_366063
  have hstable : (prefixWord ++ tailWord_366063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366063).length < 2 ^ (prefixWord ++ tailWord_366063).sum := by decide
  have hdescent : baseEnd_366063 < baseStart_366063 := by decide
  rcases family_descends (prefixWord ++ tailWord_366063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366070 : List Nat := [5, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_366070 : Nat := 118140960795 + 366070 * 2 ^ 59
def prefixEnd_366070 : Nat := 4983230072969 + 3 ^ 40 * 366070 * 2
def baseEnd_366070 : Nat := 20885540354609775904609

theorem tailTrace_366070 : CollatzResearch.WordTrace tailWord_366070 prefixEnd_366070 20885540354609775904609 := by
  unfold tailWord_366070
  simp only [CollatzResearch.WordTrace]
  refine ⟨834479361487399038978479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8901113189198923082437109 834479361487399038978479)
  ·
    refine ⟨1251719042231098558467719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 834479361487399038978479 1251719042231098558467719)
    ·
      refine ⟨1877578563346647837701579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1251719042231098558467719 1877578563346647837701579)
      ·
        refine ⟨2816367845019971756552369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1877578563346647837701579 2816367845019971756552369)
        ·
          refine ⟨2112275883764978817414277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2816367845019971756552369 2112275883764978817414277)
          ·
            refine ⟨396051728205933528265177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2112275883764978817414277 396051728205933528265177)
            ·
              refine ⟨297038796154450146198883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396051728205933528265177 297038796154450146198883)
              ·
                refine ⟨445558194231675219298325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297038796154450146198883 445558194231675219298325)
                ·
                  refine ⟨20885540354609775904609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 445558194231675219298325 20885540354609775904609)
                  ·
                    rfl

theorem cell23_366070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_366070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366070 prefixEnd_366070 := by exact prefixLift 366070
  have htrace : WordTrace (prefixWord ++ tailWord_366070) baseStart_366070 baseEnd_366070 := by
    simpa [prefixWord, tailWord_366070, baseEnd_366070] using wordTrace_append hprefix tailTrace_366070
  have hstable : (prefixWord ++ tailWord_366070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366070).length < 2 ^ (prefixWord ++ tailWord_366070).sum := by decide
  have hdescent : baseEnd_366070 < baseStart_366070 := by decide
  rcases family_descends (prefixWord ++ tailWord_366070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366090 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 2, 3, 2]
def baseStart_366090 : Nat := 118140960795 + 366090 * 2 ^ 59
def prefixEnd_366090 : Nat := 4983230072969 + 3 ^ 40 * 366090 * 2
def baseEnd_366090 : Nat := 187980132804577904891389

theorem tailTrace_366090 : CollatzResearch.WordTrace tailWord_366090 prefixEnd_366090 187980132804577904891389 := by
  unfold tailWord_366090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3338099810931482009845931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8901599495817285359589149 3338099810931482009845931)
  ·
    refine ⟨5007149716397223014768897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3338099810931482009845931 5007149716397223014768897)
    ·
      refine ⟨3755362287297917261076673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5007149716397223014768897 3755362287297917261076673)
      ·
        refine ⟨2816521715473437945807505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3755362287297917261076673 2816521715473437945807505)
        ·
          refine ⟨2112391286605078459355629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2816521715473437945807505 2112391286605078459355629)
          ·
            refine ⟨792146732476904422258361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2112391286605078459355629 792146732476904422258361)
            ·
              refine ⟨594110049357678316693771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792146732476904422258361 594110049357678316693771)
              ·
                refine ⟨891165074036517475040657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594110049357678316693771 891165074036517475040657)
                ·
                  refine ⟨668373805527388106280493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 891165074036517475040657 668373805527388106280493)
                  ·
                    refine ⟨250640177072770539855185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 668373805527388106280493 250640177072770539855185)
                    ·
                      refine ⟨187980132804577904891389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250640177072770539855185 187980132804577904891389)
                      ·
                        rfl

theorem cell23_366090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_366090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366090 prefixEnd_366090 := by exact prefixLift 366090
  have htrace : WordTrace (prefixWord ++ tailWord_366090) baseStart_366090 baseEnd_366090 := by
    simpa [prefixWord, tailWord_366090, baseEnd_366090] using wordTrace_append hprefix tailTrace_366090
  have hstable : (prefixWord ++ tailWord_366090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366090).length < 2 ^ (prefixWord ++ tailWord_366090).sum := by decide
  have hdescent : baseEnd_366090 < baseStart_366090 := by decide
  rcases family_descends (prefixWord ++ tailWord_366090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366113 : List Nat := [1, 2, 3, 2, 2, 2, 1, 4, 2, 4]
def baseStart_366113 : Nat := 118140960795 + 366113 * 2 ^ 59
def prefixEnd_366113 : Nat := 4983230072969 + 3 ^ 40 * 366113 * 2
def baseEnd_366113 : Nat := 62663980953210438301261

theorem tailTrace_366113 : CollatzResearch.WordTrace tailWord_366113 prefixEnd_366113 62663980953210438301261 := by
  unfold tailWord_366113
  simp only [CollatzResearch.WordTrace]
  refine ⟨13353238122642602967470993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8902158748428401978313995 13353238122642602967470993)
  ·
    refine ⟨10014928591981952225603245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13353238122642602967470993 10014928591981952225603245)
    ·
      refine ⟨3755598221993232084601217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10014928591981952225603245 3755598221993232084601217)
      ·
        refine ⟨2816698666494924063450913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3755598221993232084601217 2816698666494924063450913)
        ·
          refine ⟨2112523999871193047588185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2816698666494924063450913 2112523999871193047588185)
          ·
            refine ⟨1584392999903394785691139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2112523999871193047588185 1584392999903394785691139)
            ·
              refine ⟨2376589499855092178536709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584392999903394785691139 2376589499855092178536709)
              ·
                refine ⟨445610531222829783475633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2376589499855092178536709 445610531222829783475633)
                ·
                  refine ⟨334207898417122337606725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445610531222829783475633 334207898417122337606725)
                  ·
                    refine ⟨62663980953210438301261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 334207898417122337606725 62663980953210438301261)
                    ·
                      rfl

theorem cell23_366113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_366113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366113 prefixEnd_366113 := by exact prefixLift 366113
  have htrace : WordTrace (prefixWord ++ tailWord_366113) baseStart_366113 baseEnd_366113 := by
    simpa [prefixWord, tailWord_366113, baseEnd_366113] using wordTrace_append hprefix tailTrace_366113
  have hstable : (prefixWord ++ tailWord_366113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366113).length < 2 ^ (prefixWord ++ tailWord_366113).sum := by decide
  have hdescent : baseEnd_366113 < baseStart_366113 := by decide
  rcases family_descends (prefixWord ++ tailWord_366113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366133 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_366133 : Nat := 118140960795 + 366133 * 2 ^ 59
def prefixEnd_366133 : Nat := 4983230072969 + 3 ^ 40 * 366133 * 2
def baseEnd_366133 : Nat := 188002212472721236653691

theorem tailTrace_366133 : CollatzResearch.WordTrace tailWord_366133 prefixEnd_366133 188002212472721236653691 := by
  unfold tailWord_366133
  simp only [CollatzResearch.WordTrace]
  refine ⟨13353967582570146383199053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8902645055046764255466035 13353967582570146383199053)
  ·
    refine ⟨5007737843463804893699645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13353967582570146383199053 5007737843463804893699645)
    ·
      refine ⟨1877901691298926835137367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5007737843463804893699645 1877901691298926835137367)
      ·
        refine ⟨2816852536948390252706051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1877901691298926835137367 2816852536948390252706051)
        ·
          refine ⟨4225278805422585379059077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2816852536948390252706051 4225278805422585379059077)
          ·
            refine ⟨792239776016734758573577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4225278805422585379059077 792239776016734758573577)
            ·
              refine ⟨594179832012551068930183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792239776016734758573577 594179832012551068930183)
              ·
                refine ⟨891269748018826603395275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594179832012551068930183 891269748018826603395275)
                ·
                  refine ⟨1336904622028239905092913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 891269748018826603395275 1336904622028239905092913)
                  ·
                    refine ⟨1002678466521179928819685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1336904622028239905092913 1002678466521179928819685)
                    ·
                      refine ⟨188002212472721236653691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1002678466521179928819685 188002212472721236653691)
                      ·
                        rfl

theorem cell23_366133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_366133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366133 prefixEnd_366133 := by exact prefixLift 366133
  have htrace : WordTrace (prefixWord ++ tailWord_366133) baseStart_366133 baseEnd_366133 := by
    simpa [prefixWord, tailWord_366133, baseEnd_366133] using wordTrace_append hprefix tailTrace_366133
  have hstable : (prefixWord ++ tailWord_366133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366133).length < 2 ^ (prefixWord ++ tailWord_366133).sum := by decide
  have hdescent : baseEnd_366133 < baseStart_366133 := by decide
  rcases family_descends (prefixWord ++ tailWord_366133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366157 : List Nat := [1, 6, 1, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_366157 : Nat := 118140960795 + 366157 * 2 ^ 59
def prefixEnd_366157 : Nat := 4983230072969 + 3 ^ 40 * 366157 * 2
def baseEnd_366157 : Nat := 188014536008429142753581

theorem tailTrace_366157 : CollatzResearch.WordTrace tailWord_366157 prefixEnd_366157 188014536008429142753581 := by
  unfold tailWord_366157
  simp only [CollatzResearch.WordTrace]
  refine ⟨13354842934483198482072725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8903228622988798988048483 13354842934483198482072725)
  ·
    refine ⟨626008262553899928847159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13354842934483198482072725 626008262553899928847159)
    ·
      refine ⟨939012393830849893270739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626008262553899928847159 939012393830849893270739)
      ·
        refine ⟨1408518590746274839906109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939012393830849893270739 1408518590746274839906109)
        ·
          refine ⟨528194471529853064964791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1408518590746274839906109 528194471529853064964791)
          ·
            refine ⟨792291707294779597447187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528194471529853064964791 792291707294779597447187)
            ·
              refine ⟨1188437560942169396170781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792291707294779597447187 1188437560942169396170781)
              ·
                refine ⟨445664085353313523564043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1188437560942169396170781 445664085353313523564043)
                ·
                  refine ⟨668496128029970285346065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445664085353313523564043 668496128029970285346065)
                  ·
                    refine ⟨501372096022477714009549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 668496128029970285346065 501372096022477714009549)
                    ·
                      refine ⟨188014536008429142753581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 501372096022477714009549 188014536008429142753581)
                      ·
                        rfl

theorem cell23_366157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_366157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366157 prefixEnd_366157 := by exact prefixLift 366157
  have htrace : WordTrace (prefixWord ++ tailWord_366157) baseStart_366157 baseEnd_366157 := by
    simpa [prefixWord, tailWord_366157, baseEnd_366157] using wordTrace_append hprefix tailTrace_366157
  have hstable : (prefixWord ++ tailWord_366157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366157).length < 2 ^ (prefixWord ++ tailWord_366157).sum := by decide
  have hdescent : baseEnd_366157 < baseStart_366157 := by decide
  rcases family_descends (prefixWord ++ tailWord_366157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366197 : List Nat := [1, 3, 4, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_366197 : Nat := 118140960795 + 366197 * 2 ^ 59
def prefixEnd_366197 : Nat := 4983230072969 + 3 ^ 40 * 366197 * 2
def baseEnd_366197 : Nat := 188035075234608986253397

theorem tailTrace_366197 : CollatzResearch.WordTrace tailWord_366197 prefixEnd_366197 188035075234608986253397 := by
  unfold tailWord_366197
  simp only [CollatzResearch.WordTrace]
  refine ⟨13356301854338285313528845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8904201236225523542352563 13356301854338285313528845)
  ·
    refine ⟨5008613195376856992573317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13356301854338285313528845 5008613195376856992573317)
    ·
      refine ⟨939114974133160686107497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5008613195376856992573317 939114974133160686107497)
      ·
        refine ⟨704336230599870514580623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 939114974133160686107497 704336230599870514580623)
        ·
          refine ⟨1056504345899805771870935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704336230599870514580623 1056504345899805771870935)
          ·
            refine ⟨1584756518849708657806403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056504345899805771870935 1584756518849708657806403)
            ·
              refine ⟨2377134778274562986709605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584756518849708657806403 2377134778274562986709605)
              ·
                refine ⟨445712770926480560008051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2377134778274562986709605 445712770926480560008051)
                ·
                  refine ⟨668569156389720840012077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445712770926480560008051 668569156389720840012077)
                  ·
                    refine ⟨250713433646145315004529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 668569156389720840012077 250713433646145315004529)
                    ·
                      refine ⟨188035075234608986253397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250713433646145315004529 188035075234608986253397)
                      ·
                        rfl

theorem cell23_366197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_366197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366197 prefixEnd_366197 := by exact prefixLift 366197
  have htrace : WordTrace (prefixWord ++ tailWord_366197) baseStart_366197 baseEnd_366197 := by
    simpa [prefixWord, tailWord_366197, baseEnd_366197] using wordTrace_append hprefix tailTrace_366197
  have hstable : (prefixWord ++ tailWord_366197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366197).length < 2 ^ (prefixWord ++ tailWord_366197).sum := by decide
  have hdescent : baseEnd_366197 < baseStart_366197 := by decide
  rcases family_descends (prefixWord ++ tailWord_366197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366244 : List Nat := [2, 3, 1, 2, 2, 2, 4, 1, 2, 2, 2]
def baseStart_366244 : Nat := 118140960795 + 366244 * 2 ^ 59
def prefixEnd_366244 : Nat := 4983230072969 + 3 ^ 40 * 366244 * 2
def baseEnd_366244 : Nat := 188059208825370302365681

theorem tailTrace_366244 : CollatzResearch.WordTrace tailWord_366244 prefixEnd_366244 188059208825370302365681 := by
  unfold tailWord_366244
  simp only [CollatzResearch.WordTrace]
  refine ⟨6679008042584006170244893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8905344056778674893659857 6679008042584006170244893)
  ·
    refine ⟨2504628015969002313841835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6679008042584006170244893 2504628015969002313841835)
    ·
      refine ⟨3756942023953503470762753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2504628015969002313841835 3756942023953503470762753)
      ·
        refine ⟨2817706517965127603072065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3756942023953503470762753 2817706517965127603072065)
        ·
          refine ⟨2113279888473845702304049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2817706517965127603072065 2113279888473845702304049)
          ·
            refine ⟨1584959916355384276728037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2113279888473845702304049 1584959916355384276728037)
            ·
              refine ⟨297179984316634551886507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1584959916355384276728037 297179984316634551886507)
              ·
                refine ⟨445769976474951827829761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297179984316634551886507 445769976474951827829761)
                ·
                  refine ⟨334327482356213870872321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445769976474951827829761 334327482356213870872321)
                  ·
                    refine ⟨250745611767160403154241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 334327482356213870872321 250745611767160403154241)
                    ·
                      refine ⟨188059208825370302365681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250745611767160403154241 188059208825370302365681)
                      ·
                        rfl

theorem cell23_366244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_366244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366244 prefixEnd_366244 := by exact prefixLift 366244
  have htrace : WordTrace (prefixWord ++ tailWord_366244) baseStart_366244 baseEnd_366244 := by
    simpa [prefixWord, tailWord_366244, baseEnd_366244] using wordTrace_append hprefix tailTrace_366244
  have hstable : (prefixWord ++ tailWord_366244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366244).length < 2 ^ (prefixWord ++ tailWord_366244).sum := by decide
  have hdescent : baseEnd_366244 < baseStart_366244 := by decide
  rcases family_descends (prefixWord ++ tailWord_366244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
