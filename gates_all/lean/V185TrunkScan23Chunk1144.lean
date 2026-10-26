import V185TrunkScan23Chunk1143

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6776441 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 4, 4]
def baseStart_6776441 : Nat := 118140960795 + 6776441 * 2 ^ 59
def prefixEnd_6776441 : Nat := 4983230072969 + 3 ^ 40 * 6776441 * 2
def baseEnd_6776441 : Nat := 1159857119944742292374407

theorem tailTrace_6776441 : CollatzResearch.WordTrace tailWord_6776441 prefixEnd_6776441 1159857119944742292374407 := by
  unfold tailWord_6776441
  simp only [CollatzResearch.WordTrace]
  refine ⟨247157108043119055828641177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164771405362079370552427451 247157108043119055828641177)
  ·
    refine ⟨185367831032339291871480883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247157108043119055828641177 185367831032339291871480883)
    ·
      refine ⟨278051746548508937807221325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185367831032339291871480883 278051746548508937807221325)
      ·
        refine ⟨104269404955690851677707997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278051746548508937807221325 104269404955690851677707997)
        ·
          refine ⟨39101026858384069379140499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104269404955690851677707997 39101026858384069379140499)
          ·
            refine ⟨58651540287576104068710749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39101026858384069379140499 58651540287576104068710749)
            ·
              refine ⟨21994327607841039025766531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58651540287576104068710749 21994327607841039025766531)
              ·
                refine ⟨32991491411761558538649797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21994327607841039025766531 32991491411761558538649797)
                ·
                  refine ⟨6185904639705292225996837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32991491411761558538649797 6185904639705292225996837)
                  ·
                    refine ⟨1159857119944742292374407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6185904639705292225996837 1159857119944742292374407)
                    ·
                      rfl

theorem cell23_6776441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 4].length) (baseStart_6776441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776441 prefixEnd_6776441 := by exact prefixLift 6776441
  have htrace : WordTrace (prefixWord ++ tailWord_6776441) baseStart_6776441 baseEnd_6776441 := by
    simpa [prefixWord, tailWord_6776441, baseEnd_6776441] using wordTrace_append hprefix tailTrace_6776441
  have hstable : (prefixWord ++ tailWord_6776441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776441).length < 2 ^ (prefixWord ++ tailWord_6776441).sum := by decide
  have hdescent : baseEnd_6776441 < baseStart_6776441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776444 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_6776444 : Nat := 118140960795 + 6776444 * 2 ^ 59
def prefixEnd_6776444 : Nat := 4983230072969 + 3 ^ 40 * 6776444 * 2
def baseEnd_6776444 : Nat := 3479572900276190365385707

theorem tailTrace_6776444 : CollatzResearch.WordTrace tailWord_6776444 prefixEnd_6776444 3479572900276190365385707 := by
  unfold tailWord_6776444
  simp only [CollatzResearch.WordTrace]
  refine ⟨123578608731054093670500193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164771478308072124894000257 123578608731054093670500193)
  ·
    refine ⟨92683956548290570252875145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123578608731054093670500193 92683956548290570252875145)
    ·
      refine ⟨69512967411217927689656359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92683956548290570252875145 69512967411217927689656359)
      ·
        refine ⟨104269451116826891534484539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69512967411217927689656359 104269451116826891534484539)
        ·
          refine ⟨156404176675240337301726809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104269451116826891534484539 156404176675240337301726809)
          ·
            refine ⟨117303132506430252976295107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156404176675240337301726809 117303132506430252976295107)
            ·
              refine ⟨175954698759645379464442661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117303132506430252976295107 175954698759645379464442661)
              ·
                refine ⟨32991506017433508649582999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175954698759645379464442661 32991506017433508649582999)
                ·
                  refine ⟨49487259026150262974374499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32991506017433508649582999 49487259026150262974374499)
                  ·
                    refine ⟨74230888539225394461561749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49487259026150262974374499 74230888539225394461561749)
                    ·
                      refine ⟨3479572900276190365385707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74230888539225394461561749 3479572900276190365385707)
                      ·
                        rfl

theorem cell23_6776444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_6776444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776444 prefixEnd_6776444 := by exact prefixLift 6776444
  have htrace : WordTrace (prefixWord ++ tailWord_6776444) baseStart_6776444 baseEnd_6776444 := by
    simpa [prefixWord, tailWord_6776444, baseEnd_6776444] using wordTrace_append hprefix tailTrace_6776444
  have hstable : (prefixWord ++ tailWord_6776444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776444).length < 2 ^ (prefixWord ++ tailWord_6776444).sum := by decide
  have hdescent : baseEnd_6776444 < baseStart_6776444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776458 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 1, 6]
def baseStart_6776458 : Nat := 118140960795 + 6776458 * 2 ^ 59
def prefixEnd_6776458 : Nat := 4983230072969 + 3 ^ 40 * 6776458 * 2
def baseEnd_6776458 : Nat := 1159860029668451103536881

theorem tailTrace_6776458 : CollatzResearch.WordTrace tailWord_6776458 prefixEnd_6776458 1159860029668451103536881 := by
  unfold tailWord_6776458
  simp only [CollatzResearch.WordTrace]
  refine ⟨61789432021014366933002507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164771818722704978488006685 61789432021014366933002507)
  ·
    refine ⟨92684148031521550399503761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61789432021014366933002507 92684148031521550399503761)
    ·
      refine ⟨69513111023641162799627821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92684148031521550399503761 69513111023641162799627821)
      ·
        refine ⟨26067416633865436049860433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69513111023641162799627821 26067416633865436049860433)
        ·
          refine ⟨19550562475399077037395325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26067416633865436049860433 19550562475399077037395325)
          ·
            refine ⟨7331460928274653889023247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19550562475399077037395325 7331460928274653889023247)
            ·
              refine ⟨10997191392411980833534871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7331460928274653889023247 10997191392411980833534871)
              ·
                refine ⟨16495787088617971250302307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10997191392411980833534871 16495787088617971250302307)
                ·
                  refine ⟨24743680632926956875453461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16495787088617971250302307 24743680632926956875453461)
                  ·
                    refine ⟨1159860029668451103536881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24743680632926956875453461 1159860029668451103536881)
                    ·
                      rfl

theorem cell23_6776458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_6776458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776458 prefixEnd_6776458 := by exact prefixLift 6776458
  have htrace : WordTrace (prefixWord ++ tailWord_6776458) baseStart_6776458 baseEnd_6776458 := by
    simpa [prefixWord, tailWord_6776458, baseEnd_6776458] using wordTrace_append hprefix tailTrace_6776458
  have hstable : (prefixWord ++ tailWord_6776458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776458).length < 2 ^ (prefixWord ++ tailWord_6776458).sum := by decide
  have hdescent : baseEnd_6776458 < baseStart_6776458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776471 : List Nat := [1, 1, 3, 3, 2, 2, 4, 7]
def baseStart_6776471 : Nat := 118140960795 + 6776471 * 2 ^ 59
def prefixEnd_6776471 : Nat := 4983230072969 + 3 ^ 40 * 6776471 * 2
def baseEnd_6776471 : Nat := 128873583861254139249929

theorem tailTrace_6776471 : CollatzResearch.WordTrace tailWord_6776471 prefixEnd_6776471 128873583861254139249929 := by
  unfold tailWord_6776471
  simp only [CollatzResearch.WordTrace]
  refine ⟨247158202233010370952233267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164772134822006913968155511 247158202233010370952233267)
  ·
    refine ⟨370737303349515556428349901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247158202233010370952233267 370737303349515556428349901)
    ·
      refine ⟨139026488756068333660631213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370737303349515556428349901 139026488756068333660631213)
      ·
        refine ⟨52134933283525625122736705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139026488756068333660631213 52134933283525625122736705)
        ·
          refine ⟨39101199962644218842052529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52134933283525625122736705 39101199962644218842052529)
          ·
            refine ⟨29325899971983164131539397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39101199962644218842052529 29325899971983164131539397)
            ·
              refine ⟨5498606244746843274663637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29325899971983164131539397 5498606244746843274663637)
              ·
                refine ⟨128873583861254139249929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5498606244746843274663637 128873583861254139249929)
                ·
                  rfl

theorem cell23_6776471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 7].length) (baseStart_6776471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776471 prefixEnd_6776471 := by exact prefixLift 6776471
  have htrace : WordTrace (prefixWord ++ tailWord_6776471) baseStart_6776471 baseEnd_6776471 := by
    simpa [prefixWord, tailWord_6776471, baseEnd_6776471] using wordTrace_append hprefix tailTrace_6776471
  have hstable : (prefixWord ++ tailWord_6776471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776471).length < 2 ^ (prefixWord ++ tailWord_6776471).sum := by decide
  have hdescent : baseEnd_6776471 < baseStart_6776471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776498 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_6776498 : Nat := 118140960795 + 6776498 * 2 ^ 59
def prefixEnd_6776498 : Nat := 4983230072969 + 3 ^ 40 * 6776498 * 2
def baseEnd_6776498 : Nat := 3479600628231533154110459

theorem tailTrace_6776498 : CollatzResearch.WordTrace tailWord_6776498 prefixEnd_6776498 3479600628231533154110459 := by
  unfold tailWord_6776498
  simp only [CollatzResearch.WordTrace]
  refine ⟨61789796750978138640866537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164772791335941703042310765 61789796750978138640866537)
  ·
    refine ⟨46342347563233603980649903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61789796750978138640866537 46342347563233603980649903)
    ·
      refine ⟨69513521344850405970974855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46342347563233603980649903 69513521344850405970974855)
      ·
        refine ⟨104270282017275608956462283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69513521344850405970974855 104270282017275608956462283)
        ·
          refine ⟨156405423025913413434693425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104270282017275608956462283 156405423025913413434693425)
          ·
            refine ⟨117304067269435060076020069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156405423025913413434693425 117304067269435060076020069)
            ·
              refine ⟨21994512613019073764253763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117304067269435060076020069 21994512613019073764253763)
              ·
                refine ⟨32991768919528610646380645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21994512613019073764253763 32991768919528610646380645)
                ·
                  refine ⟨6185956672411614496196371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32991768919528610646380645 6185956672411614496196371)
                  ·
                    refine ⟨9278935008617421744294557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6185956672411614496196371 9278935008617421744294557)
                    ·
                      refine ⟨3479600628231533154110459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9278935008617421744294557 3479600628231533154110459)
                      ·
                        rfl

theorem cell23_6776498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_6776498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776498 prefixEnd_6776498 := by exact prefixLift 6776498
  have htrace : WordTrace (prefixWord ++ tailWord_6776498) baseStart_6776498 baseEnd_6776498 := by
    simpa [prefixWord, tailWord_6776498, baseEnd_6776498] using wordTrace_append hprefix tailTrace_6776498
  have hstable : (prefixWord ++ tailWord_6776498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776498).length < 2 ^ (prefixWord ++ tailWord_6776498).sum := by decide
  have hdescent : baseEnd_6776498 < baseStart_6776498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776538 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2]
def baseStart_6776538 : Nat := 118140960795 + 6776538 * 2 ^ 59
def prefixEnd_6776538 : Nat := 4983230072969 + 3 ^ 40 * 6776538 * 2
def baseEnd_6776538 : Nat := 3479621167457712997610275

theorem tailTrace_6776538 : CollatzResearch.WordTrace tailWord_6776538 prefixEnd_6776538 3479621167457712997610275 := by
  unfold tailWord_6776538
  simp only [CollatzResearch.WordTrace]
  refine ⟨61790161480941910348730567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164773763949178427596614845 61790161480941910348730567)
  ·
    refine ⟨92685242221412865523095851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61790161480941910348730567 92685242221412865523095851)
    ·
      refine ⟨139027863332119298284643777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92685242221412865523095851 139027863332119298284643777)
      ·
        refine ⟨104270897499089473713482833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139027863332119298284643777 104270897499089473713482833)
        ·
          refine ⟨78203173124317105285112125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104270897499089473713482833 78203173124317105285112125)
          ·
            refine ⟨29326189921618914481917047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78203173124317105285112125 29326189921618914481917047)
            ·
              refine ⟨43989284882428371722875571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29326189921618914481917047 43989284882428371722875571)
              ·
                refine ⟨65983927323642557584313357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43989284882428371722875571 65983927323642557584313357)
                ·
                  refine ⟨24743972746365959094117509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65983927323642557584313357 24743972746365959094117509)
                  ·
                    refine ⟨4639494889943617330147033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24743972746365959094117509 4639494889943617330147033)
                    ·
                      refine ⟨3479621167457712997610275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639494889943617330147033 3479621167457712997610275)
                      ·
                        rfl

theorem cell23_6776538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_6776538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776538 prefixEnd_6776538 := by exact prefixLift 6776538
  have htrace : WordTrace (prefixWord ++ tailWord_6776538) baseStart_6776538 baseEnd_6776538 := by
    simpa [prefixWord, tailWord_6776538, baseEnd_6776538] using wordTrace_append hprefix tailTrace_6776538
  have hstable : (prefixWord ++ tailWord_6776538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776538).length < 2 ^ (prefixWord ++ tailWord_6776538).sum := by decide
  have hdescent : baseEnd_6776538 < baseStart_6776538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776555 : List Nat := [1, 1, 1, 1, 2, 4, 3, 4, 2, 2, 2]
def baseStart_6776555 : Nat := 118140960795 + 6776555 * 2 ^ 59
def prefixEnd_6776555 : Nat := 4983230072969 + 3 ^ 40 * 6776555 * 2
def baseEnd_6776555 : Nat := 3479629896628839431097697

theorem tailTrace_6776555 : CollatzResearch.WordTrace tailWord_6776555 prefixEnd_6776555 3479629896628839431097697 := by
  unfold tailWord_6776555
  simp only [CollatzResearch.WordTrace]
  refine ⟨247161265964706053298291119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164774177309804035532194079 247161265964706053298291119)
  ·
    refine ⟨370741898947059079947436679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247161265964706053298291119 370741898947059079947436679)
    ·
      refine ⟨556112848420588619921155019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370741898947059079947436679 556112848420588619921155019)
      ·
        refine ⟨834169272630882929881732529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556112848420588619921155019 834169272630882929881732529)
        ·
          refine ⟨625626954473162197411299397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 834169272630882929881732529 625626954473162197411299397)
          ·
            refine ⟨117305053963717912014618637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 625626954473162197411299397 117305053963717912014618637)
            ·
              refine ⟨43989395236394217005481989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117305053963717912014618637 43989395236394217005481989)
              ·
                refine ⟨8248011606823915688527873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43989395236394217005481989 8248011606823915688527873)
                ·
                  refine ⟨6186008705117936766395905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8248011606823915688527873 6186008705117936766395905)
                  ·
                    refine ⟨4639506528838452574796929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6186008705117936766395905 4639506528838452574796929)
                    ·
                      refine ⟨3479629896628839431097697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639506528838452574796929 3479629896628839431097697)
                      ·
                        rfl

theorem cell23_6776555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 2, 2].length) (baseStart_6776555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776555 prefixEnd_6776555 := by exact prefixLift 6776555
  have htrace : WordTrace (prefixWord ++ tailWord_6776555) baseStart_6776555 baseEnd_6776555 := by
    simpa [prefixWord, tailWord_6776555, baseEnd_6776555] using wordTrace_append hprefix tailTrace_6776555
  have hstable : (prefixWord ++ tailWord_6776555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776555).length < 2 ^ (prefixWord ++ tailWord_6776555).sum := by decide
  have hdescent : baseEnd_6776555 < baseStart_6776555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776578 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 7]
def baseStart_6776578 : Nat := 118140960795 + 6776578 * 2 ^ 59
def prefixEnd_6776578 : Nat := 4983230072969 + 3 ^ 40 * 6776578 * 2
def baseEnd_6776578 : Nat := 386626856298210315678899

theorem tailTrace_6776578 : CollatzResearch.WordTrace tailWord_6776578 prefixEnd_6776578 386626856298210315678899 := by
  unfold tailWord_6776578
  simp only [CollatzResearch.WordTrace]
  refine ⟨61790526210905682056594597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164774736562415152150918925 61790526210905682056594597)
  ·
    refine ⟨11585723664544815385611487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61790526210905682056594597 11585723664544815385611487)
    ·
      refine ⟨17378585496817223078417231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11585723664544815385611487 17378585496817223078417231)
      ·
        refine ⟨26067878245225834617625847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17378585496817223078417231 26067878245225834617625847)
        ·
          refine ⟨39101817367838751926438771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26067878245225834617625847 39101817367838751926438771)
          ·
            refine ⟨58652726051758127889658157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39101817367838751926438771 58652726051758127889658157)
            ·
              refine ⟨21994772269409297958621809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58652726051758127889658157 21994772269409297958621809)
              ·
                refine ⟨16496079202056973468966357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21994772269409297958621809 16496079202056973468966357)
                ·
                  refine ⟨386626856298210315678899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16496079202056973468966357 386626856298210315678899)
                  ·
                    rfl

theorem cell23_6776578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_6776578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776578 prefixEnd_6776578 := by exact prefixLift 6776578
  have htrace : WordTrace (prefixWord ++ tailWord_6776578) baseStart_6776578 baseEnd_6776578 := by
    simpa [prefixWord, tailWord_6776578, baseEnd_6776578] using wordTrace_append hprefix tailTrace_6776578
  have hstable : (prefixWord ++ tailWord_6776578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776578).length < 2 ^ (prefixWord ++ tailWord_6776578).sum := by decide
  have hdescent : baseEnd_6776578 < baseStart_6776578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776591 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 2, 5]
def baseStart_6776591 : Nat := 118140960795 + 6776591 * 2 ^ 59
def prefixEnd_6776591 : Nat := 4983230072969 + 3 ^ 40 * 6776591 * 2
def baseEnd_6776591 : Nat := 1159882793977467096749177

theorem tailTrace_6776591 : CollatzResearch.WordTrace tailWord_6776591 prefixEnd_6776591 1159882793977467096749177 := by
  unfold tailWord_6776591
  simp only [CollatzResearch.WordTrace]
  refine ⟨247162578992575631446601627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164775052661717087631067751 247162578992575631446601627)
  ·
    refine ⟨370743868488863447169902441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247162578992575631446601627 370743868488863447169902441)
    ·
      refine ⟨278057901366647585377426831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370743868488863447169902441 278057901366647585377426831)
      ·
        refine ⟨417086852049971378066140247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278057901366647585377426831 417086852049971378066140247)
        ·
          refine ⟨625630278074957067099210371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417086852049971378066140247 625630278074957067099210371)
          ·
            refine ⟨938445417112435600648815557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625630278074957067099210371 938445417112435600648815557)
            ·
              refine ⟨175958515708581675121652917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 938445417112435600648815557 175958515708581675121652917)
              ·
                refine ⟨16496110847679532042654961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175958515708581675121652917 16496110847679532042654961)
                ·
                  refine ⟨12372083135759649031991221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16496110847679532042654961 12372083135759649031991221)
                  ·
                    refine ⟨1159882793977467096749177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12372083135759649031991221 1159882793977467096749177)
                    ·
                      rfl

theorem cell23_6776591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_6776591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776591 prefixEnd_6776591 := by exact prefixLift 6776591
  have htrace : WordTrace (prefixWord ++ tailWord_6776591) baseStart_6776591 baseEnd_6776591 := by
    simpa [prefixWord, tailWord_6776591, baseEnd_6776591] using wordTrace_append hprefix tailTrace_6776591
  have hstable : (prefixWord ++ tailWord_6776591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776591).length < 2 ^ (prefixWord ++ tailWord_6776591).sum := by decide
  have hdescent : baseEnd_6776591 < baseStart_6776591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776606 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_6776606 : Nat := 118140960795 + 6776606 * 2 ^ 59
def prefixEnd_6776606 : Nat := 4983230072969 + 3 ^ 40 * 6776606 * 2
def baseEnd_6776606 : Nat := 3479656084142218731559963

theorem tailTrace_6776606 : CollatzResearch.WordTrace tailWord_6776606 prefixEnd_6776606 3479656084142218731559963 := by
  unfold tailWord_6776606
  simp only [CollatzResearch.WordTrace]
  refine ⟨30895390760940161126049709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164775417391680859338931781 30895390760940161126049709)
  ·
    refine ⟨11585771535352560422268641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30895390760940161126049709 11585771535352560422268641)
    ·
      refine ⟨8689328651514420316701481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11585771535352560422268641 8689328651514420316701481)
      ·
        refine ⟨6516996488635815237526111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8689328651514420316701481 6516996488635815237526111)
        ·
          refine ⟨9775494732953722856289167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6516996488635815237526111 9775494732953722856289167)
          ·
            refine ⟨14663242099430584284433751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9775494732953722856289167 14663242099430584284433751)
            ·
              refine ⟨21994863149145876426650627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14663242099430584284433751 21994863149145876426650627)
              ·
                refine ⟨32992294723718814639975941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21994863149145876426650627 32992294723718814639975941)
                ·
                  refine ⟨6186055260697277744995489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32992294723718814639975941 6186055260697277744995489)
                  ·
                    refine ⟨4639541445522958308746617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6186055260697277744995489 4639541445522958308746617)
                    ·
                      refine ⟨3479656084142218731559963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639541445522958308746617 3479656084142218731559963)
                      ·
                        rfl

theorem cell23_6776606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_6776606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776606 prefixEnd_6776606 := by exact prefixLift 6776606
  have htrace : WordTrace (prefixWord ++ tailWord_6776606) baseStart_6776606 baseEnd_6776606 := by
    simpa [prefixWord, tailWord_6776606, baseEnd_6776606] using wordTrace_append hprefix tailTrace_6776606
  have hstable : (prefixWord ++ tailWord_6776606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776606).length < 2 ^ (prefixWord ++ tailWord_6776606).sum := by decide
  have hdescent : baseEnd_6776606 < baseStart_6776606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776648 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_6776648 : Nat := 118140960795 + 6776648 * 2 ^ 59
def prefixEnd_6776648 : Nat := 4983230072969 + 3 ^ 40 * 6776648 * 2
def baseEnd_6776648 : Nat := 3479677650329707567234769

theorem tailTrace_6776648 : CollatzResearch.WordTrace tailWord_6776648 prefixEnd_6776648 3479677650329707567234769 := by
  unfold tailWord_6776648
  simp only [CollatzResearch.WordTrace]
  refine ⟨123582328976684565090713299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164776438635579420120951065 123582328976684565090713299)
  ·
    refine ⟨185373493465026847636069949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123582328976684565090713299 185373493465026847636069949)
    ·
      refine ⟨69515060049385067863526231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185373493465026847636069949 69515060049385067863526231)
      ·
        refine ⟨104272590074077601795289347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69515060049385067863526231 104272590074077601795289347)
        ·
          refine ⟨156408885111116402692934021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104272590074077601795289347 156408885111116402692934021)
          ·
            refine ⟨29326665958334325504925129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156408885111116402692934021 29326665958334325504925129)
            ·
              refine ⟨21994999468750744128693847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29326665958334325504925129 21994999468750744128693847)
              ·
                refine ⟨32992499203126116193040771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21994999468750744128693847 32992499203126116193040771)
                ·
                  refine ⟨49488748804689174289561157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32992499203126116193040771 49488748804689174289561157)
                  ·
                    refine ⟨9279140400879220179292717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49488748804689174289561157 9279140400879220179292717)
                    ·
                      refine ⟨3479677650329707567234769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9279140400879220179292717 3479677650329707567234769)
                      ·
                        rfl

theorem cell23_6776648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_6776648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776648 prefixEnd_6776648 := by exact prefixLift 6776648
  have htrace : WordTrace (prefixWord ++ tailWord_6776648) baseStart_6776648 baseEnd_6776648 := by
    simpa [prefixWord, tailWord_6776648, baseEnd_6776648] using wordTrace_append hprefix tailTrace_6776648
  have hstable : (prefixWord ++ tailWord_6776648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776648).length < 2 ^ (prefixWord ++ tailWord_6776648).sum := by decide
  have hdescent : baseEnd_6776648 < baseStart_6776648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776685 : List Nat := [1, 5, 1, 1, 1, 1, 6, 1, 6]
def baseStart_6776685 : Nat := 118140960795 + 6776685 * 2 ^ 59
def prefixEnd_6776685 : Nat := 4983230072969 + 3 ^ 40 * 6776685 * 2
def baseEnd_6776685 : Nat := 386632961012658213608011

theorem tailTrace_6776685 : CollatzResearch.WordTrace tailWord_6776685 prefixEnd_6776685 386632961012658213608011 := by
  unfold tailWord_6776685
  simp only [CollatzResearch.WordTrace]
  refine ⟨247166007454235085500523509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164777338302823390333682339 247166007454235085500523509)
  ·
    refine ⟨23171813198834539265674079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247166007454235085500523509 23171813198834539265674079)
    ·
      refine ⟨34757719798251808898511119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23171813198834539265674079 34757719798251808898511119)
      ·
        refine ⟨52136579697377713347766679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34757719798251808898511119 52136579697377713347766679)
        ·
          refine ⟨78204869546066570021650019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52136579697377713347766679 78204869546066570021650019)
          ·
            refine ⟨117307304319099855032475029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78204869546066570021650019 117307304319099855032475029)
            ·
              refine ⟨5498779889957805704647267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117307304319099855032475029 5498779889957805704647267)
              ·
                refine ⟨8248169834936708556970901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5498779889957805704647267 8248169834936708556970901)
                ·
                  refine ⟨386632961012658213608011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8248169834936708556970901 386632961012658213608011)
                  ·
                    rfl

theorem cell23_6776685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_6776685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776685 prefixEnd_6776685 := by exact prefixLift 6776685
  have htrace : WordTrace (prefixWord ++ tailWord_6776685) baseStart_6776685 baseEnd_6776685 := by
    simpa [prefixWord, tailWord_6776685, baseEnd_6776685] using wordTrace_append hprefix tailTrace_6776685
  have hstable : (prefixWord ++ tailWord_6776685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776685).length < 2 ^ (prefixWord ++ tailWord_6776685).sum := by decide
  have hdescent : baseEnd_6776685 < baseStart_6776685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776729 : List Nat := [1, 2, 1, 2, 1, 3, 6, 2, 1, 1, 3]
def baseStart_6776729 : Nat := 118140960795 + 6776729 * 2 ^ 59
def prefixEnd_6776729 : Nat := 4983230072969 + 3 ^ 40 * 6776729 * 2
def baseEnd_6776729 : Nat := 3479719242262721750321897

theorem tailTrace_6776729 : CollatzResearch.WordTrace tailWord_6776729 prefixEnd_6776729 3479719242262721750321897 := by
  unfold tailWord_6776729
  simp only [CollatzResearch.WordTrace]
  refine ⟨247167612266075681015125241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164778408177383787343416827 247167612266075681015125241)
  ·
    refine ⟨185375709199556760761343931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247167612266075681015125241 185375709199556760761343931)
    ·
      refine ⟨278063563799335141142015897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185375709199556760761343931 278063563799335141142015897)
      ·
        refine ⟨208547672849501355856511923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278063563799335141142015897 208547672849501355856511923)
        ·
          refine ⟨312821509274252033784767885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208547672849501355856511923 312821509274252033784767885)
          ·
            refine ⟨117308065977844512669287957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312821509274252033784767885 117308065977844512669287957)
            ·
              refine ⟨5498815592711461531372873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117308065977844512669287957 5498815592711461531372873)
              ·
                refine ⟨4124111694533596148529655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5498815592711461531372873 4124111694533596148529655)
                ·
                  refine ⟨6186167541800394222794483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4124111694533596148529655 6186167541800394222794483)
                  ·
                    refine ⟨9279251312700591334191725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6186167541800394222794483 9279251312700591334191725)
                    ·
                      refine ⟨3479719242262721750321897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9279251312700591334191725 3479719242262721750321897)
                      ·
                        rfl

theorem cell23_6776729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 1, 1, 3].length) (baseStart_6776729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776729 prefixEnd_6776729 := by exact prefixLift 6776729
  have htrace : WordTrace (prefixWord ++ tailWord_6776729) baseStart_6776729 baseEnd_6776729 := by
    simpa [prefixWord, tailWord_6776729, baseEnd_6776729] using wordTrace_append hprefix tailTrace_6776729
  have hstable : (prefixWord ++ tailWord_6776729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776729).length < 2 ^ (prefixWord ++ tailWord_6776729).sum := by decide
  have hdescent : baseEnd_6776729 < baseStart_6776729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776755 : List Nat := [1, 1, 1, 2, 3, 1, 4, 4, 1, 2, 3]
def baseStart_6776755 : Nat := 118140960795 + 6776755 * 2 ^ 59
def prefixEnd_6776755 : Nat := 4983230072969 + 3 ^ 40 * 6776755 * 2
def baseEnd_6776755 : Nat := 3479732592759738648596777

theorem tailTrace_6776755 : CollatzResearch.WordTrace tailWord_6776755 prefixEnd_6776755 3479732592759738648596777 := by
  unfold tailWord_6776755
  simp only [CollatzResearch.WordTrace]
  refine ⟨247168560563981487455571719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164779040375987658303714479 247168560563981487455571719)
  ·
    refine ⟨370752840845972231183357579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247168560563981487455571719 370752840845972231183357579)
    ·
      refine ⟨556129261268958346775036369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370752840845972231183357579 556129261268958346775036369)
      ·
        refine ⟨417096945951718760081277277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556129261268958346775036369 417096945951718760081277277)
        ·
          refine ⟨156411354731894535030478979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 417096945951718760081277277 156411354731894535030478979)
          ·
            refine ⟨234617032097841802545718469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156411354731894535030478979 234617032097841802545718469)
            ·
              refine ⟨43990693518345337977322213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234617032097841802545718469 43990693518345337977322213)
              ·
                refine ⟨8248255034689750870747915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43990693518345337977322213 8248255034689750870747915)
                ·
                  refine ⟨12372382552034626306121873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8248255034689750870747915 12372382552034626306121873)
                  ·
                    refine ⟨9279286914025969729591405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12372382552034626306121873 9279286914025969729591405)
                    ·
                      refine ⟨3479732592759738648596777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9279286914025969729591405 3479732592759738648596777)
                      ·
                        rfl

theorem cell23_6776755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 2, 3].length) (baseStart_6776755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776755 prefixEnd_6776755 := by exact prefixLift 6776755
  have htrace : WordTrace (prefixWord ++ tailWord_6776755) baseStart_6776755 baseEnd_6776755 := by
    simpa [prefixWord, tailWord_6776755, baseEnd_6776755] using wordTrace_append hprefix tailTrace_6776755
  have hstable : (prefixWord ++ tailWord_6776755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776755).length < 2 ^ (prefixWord ++ tailWord_6776755).sum := by decide
  have hdescent : baseEnd_6776755 < baseStart_6776755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776765 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_6776765 : Nat := 118140960795 + 6776765 * 2 ^ 59
def prefixEnd_6776765 : Nat := 4983230072969 + 3 ^ 40 * 6776765 * 2
def baseEnd_6776765 : Nat := 3479737727566283609471731

theorem tailTrace_6776765 : CollatzResearch.WordTrace tailWord_6776765 prefixEnd_6776765 3479737727566283609471731 := by
  unfold tailWord_6776765
  simp only [CollatzResearch.WordTrace]
  refine ⟨247168925293945259163435749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164779283529296839442290499 247168925293945259163435749)
  ·
    refine ⟨46344173492614736093144203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247168925293945259163435749 46344173492614736093144203)
    ·
      refine ⟨69516260238922104139716305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46344173492614736093144203 69516260238922104139716305)
      ·
        refine ⟨52137195179191578104787229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69516260238922104139716305 52137195179191578104787229)
        ·
          refine ⟨19551448192196841789295211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52137195179191578104787229 19551448192196841789295211)
          ·
            refine ⟨29327172288295262683942817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19551448192196841789295211 29327172288295262683942817)
            ·
              refine ⟨21995379216221447012957113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29327172288295262683942817 21995379216221447012957113)
              ·
                refine ⟨16496534412166085259717835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21995379216221447012957113 16496534412166085259717835)
                ·
                  refine ⟨24744801618249127889576753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16496534412166085259717835 24744801618249127889576753)
                  ·
                    refine ⟨18558601213686845917182565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24744801618249127889576753 18558601213686845917182565)
                    ·
                      refine ⟨3479737727566283609471731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18558601213686845917182565 3479737727566283609471731)
                      ·
                        rfl

theorem cell23_6776765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_6776765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776765 prefixEnd_6776765 := by exact prefixLift 6776765
  have htrace : WordTrace (prefixWord ++ tailWord_6776765) baseStart_6776765 baseEnd_6776765 := by
    simpa [prefixWord, tailWord_6776765, baseEnd_6776765] using wordTrace_append hprefix tailTrace_6776765
  have hstable : (prefixWord ++ tailWord_6776765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776765).length < 2 ^ (prefixWord ++ tailWord_6776765).sum := by decide
  have hdescent : baseEnd_6776765 < baseStart_6776765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776786 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_6776786 : Nat := 118140960795 + 6776786 * 2 ^ 59
def prefixEnd_6776786 : Nat := 4983230072969 + 3 ^ 40 * 6776786 * 2
def baseEnd_6776786 : Nat := 3479748510660028027309135

theorem tailTrace_6776786 : CollatzResearch.WordTrace tailWord_6776786 prefixEnd_6776786 3479748510660028027309135 := by
  unfold tailWord_6776786
  simp only [CollatzResearch.WordTrace]
  refine ⟨61792422806717294937487553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164779794151246119833300141 61792422806717294937487553)
  ·
    refine ⟨46344317105037971203115665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61792422806717294937487553 46344317105037971203115665)
    ·
      refine ⟨34758237828778478402336749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46344317105037971203115665 34758237828778478402336749)
      ·
        refine ⟨13034339185791929400876281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34758237828778478402336749 13034339185791929400876281)
        ·
          refine ⟨9775754389343947050657211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13034339185791929400876281 9775754389343947050657211)
          ·
            refine ⟨14663631584015920575985817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9775754389343947050657211 14663631584015920575985817)
            ·
              refine ⟨10997723688011940431989363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14663631584015920575985817 10997723688011940431989363)
              ·
                refine ⟨16496585532017910647984045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10997723688011940431989363 16496585532017910647984045)
                ·
                  refine ⟨6186219574506716492994017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16496585532017910647984045 6186219574506716492994017)
                  ·
                    refine ⟨4639664680880037369745513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6186219574506716492994017 4639664680880037369745513)
                    ·
                      refine ⟨3479748510660028027309135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639664680880037369745513 3479748510660028027309135)
                      ·
                        rfl

theorem cell23_6776786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_6776786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776786 prefixEnd_6776786 := by exact prefixLift 6776786
  have htrace : WordTrace (prefixWord ++ tailWord_6776786) baseStart_6776786 baseEnd_6776786 := by
    simpa [prefixWord, tailWord_6776786, baseEnd_6776786] using wordTrace_append hprefix tailTrace_6776786
  have hstable : (prefixWord ++ tailWord_6776786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776786).length < 2 ^ (prefixWord ++ tailWord_6776786).sum := by decide
  have hdescent : baseEnd_6776786 < baseStart_6776786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776796 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6776796 : Nat := 118140960795 + 6776796 * 2 ^ 59
def prefixEnd_6776796 : Nat := 4983230072969 + 3 ^ 40 * 6776796 * 2
def baseEnd_6776796 : Nat := 1159917881822190996061363

theorem tailTrace_6776796 : CollatzResearch.WordTrace tailWord_6776796 prefixEnd_6776796 1159917881822190996061363 := by
  unfold tailWord_6776796
  simp only [CollatzResearch.WordTrace]
  refine ⟨123585027978416475728907121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164780037304555300971876161 123585027978416475728907121)
  ·
    refine ⟨92688770983812356796680341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123585027978416475728907121 92688770983812356796680341)
    ·
      refine ⟨4344786139866204224844391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92688770983812356796680341 4344786139866204224844391)
      ·
        refine ⟨6517179209799306337266587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4344786139866204224844391 6517179209799306337266587)
        ·
          refine ⟨9775768814698959505899881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6517179209799306337266587 9775768814698959505899881)
          ·
            refine ⟨7331826611024219629424911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9775768814698959505899881 7331826611024219629424911)
            ·
              refine ⟨10997739916536329444137367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7331826611024219629424911 10997739916536329444137367)
              ·
                refine ⟨16496609874804494166206051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10997739916536329444137367 16496609874804494166206051)
                ·
                  refine ⟨24744914812206741249309077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16496609874804494166206051 24744914812206741249309077)
                  ·
                    refine ⟨1159917881822190996061363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24744914812206741249309077 1159917881822190996061363)
                    ·
                      rfl

theorem cell23_6776796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6776796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776796 prefixEnd_6776796 := by exact prefixLift 6776796
  have htrace : WordTrace (prefixWord ++ tailWord_6776796) baseStart_6776796 baseEnd_6776796 := by
    simpa [prefixWord, tailWord_6776796, baseEnd_6776796] using wordTrace_append hprefix tailTrace_6776796
  have hstable : (prefixWord ++ tailWord_6776796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776796).length < 2 ^ (prefixWord ++ tailWord_6776796).sum := by decide
  have hdescent : baseEnd_6776796 < baseStart_6776796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776853 : List Nat := [1, 3, 2, 1, 6, 1, 2, 1, 2, 1, 3]
def baseStart_6776853 : Nat := 118140960795 + 6776853 * 2 ^ 59
def prefixEnd_6776853 : Nat := 4983230072969 + 3 ^ 40 * 6776853 * 2
def baseEnd_6776853 : Nat := 3479782913863879265171327

theorem tailTrace_6776853 : CollatzResearch.WordTrace tailWord_6776853 prefixEnd_6776853 3479782913863879265171327 := by
  unfold tailWord_6776853
  simp only [CollatzResearch.WordTrace]
  refine ⟨247172134917626450192639213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164781423278417633461759475 247172134917626450192639213)
  ·
    refine ⟨92689550594109918822239705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247172134917626450192639213 92689550594109918822239705)
    ·
      refine ⟨69517162945582439116679779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92689550594109918822239705 69517162945582439116679779)
      ·
        refine ⟨104275744418373658675019669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69517162945582439116679779 104275744418373658675019669)
        ·
          refine ⟨4887925519611265250391547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104275744418373658675019669 4887925519611265250391547)
          ·
            refine ⟨7331888279416897875587321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887925519611265250391547 7331888279416897875587321)
            ·
              refine ⟨5498916209562673406690491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7331888279416897875587321 5498916209562673406690491)
              ·
                refine ⟨8248374314344010110035737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5498916209562673406690491 8248374314344010110035737)
                ·
                  refine ⟨6186280735758007582526803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8248374314344010110035737 6186280735758007582526803)
                  ·
                    refine ⟨9279421103637011373790205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6186280735758007582526803 9279421103637011373790205)
                    ·
                      refine ⟨3479782913863879265171327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9279421103637011373790205 3479782913863879265171327)
                      ·
                        rfl

theorem cell23_6776853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_6776853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776853 prefixEnd_6776853 := by exact prefixLift 6776853
  have htrace : WordTrace (prefixWord ++ tailWord_6776853) baseStart_6776853 baseEnd_6776853 := by
    simpa [prefixWord, tailWord_6776853, baseEnd_6776853] using wordTrace_append hprefix tailTrace_6776853
  have hstable : (prefixWord ++ tailWord_6776853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776853).length < 2 ^ (prefixWord ++ tailWord_6776853).sum := by decide
  have hdescent : baseEnd_6776853 < baseStart_6776853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776895 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 2, 5]
def baseStart_6776895 : Nat := 118140960795 + 6776895 * 2 ^ 59
def prefixEnd_6776895 : Nat := 4983230072969 + 3 ^ 40 * 6776895 * 2
def baseEnd_6776895 : Nat := 1159934826683789366948711

theorem tailTrace_6776895 : CollatzResearch.WordTrace tailWord_6776895 prefixEnd_6776895 1159934826683789366948711 := by
  unfold tailWord_6776895
  simp only [CollatzResearch.WordTrace]
  refine ⟨247173666783474291365668139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164782444522316194243778759 247173666783474291365668139)
  ·
    refine ⟨370760500175211437048502209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247173666783474291365668139 370760500175211437048502209)
    ·
      refine ⟨278070375131408577786376657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370760500175211437048502209 278070375131408577786376657)
      ·
        refine ⟨208552781348556433339782493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278070375131408577786376657 208552781348556433339782493)
        ·
          refine ⟨78207293005708662502418435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208552781348556433339782493 78207293005708662502418435)
          ·
            refine ⟨117310939508562993753627653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78207293005708662502418435 117310939508562993753627653)
            ·
              refine ⟨21995801157855561328805185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117310939508562993753627653 21995801157855561328805185)
              ·
                refine ⟨16496850868391670996603889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21995801157855561328805185 16496850868391670996603889)
                ·
                  refine ⟨12372638151293753247452917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16496850868391670996603889 12372638151293753247452917)
                  ·
                    refine ⟨1159934826683789366948711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12372638151293753247452917 1159934826683789366948711)
                    ·
                      rfl

theorem cell23_6776895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_6776895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776895 prefixEnd_6776895 := by exact prefixLift 6776895
  have htrace : WordTrace (prefixWord ++ tailWord_6776895) baseStart_6776895 baseEnd_6776895 := by
    simpa [prefixWord, tailWord_6776895, baseEnd_6776895] using wordTrace_append hprefix tailTrace_6776895
  have hstable : (prefixWord ++ tailWord_6776895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776895).length < 2 ^ (prefixWord ++ tailWord_6776895).sum := by decide
  have hdescent : baseEnd_6776895 < baseStart_6776895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776932 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_6776932 : Nat := 118140960795 + 6776932 * 2 ^ 59
def prefixEnd_6776932 : Nat := 4983230072969 + 3 ^ 40 * 6776932 * 2
def baseEnd_6776932 : Nat := 3479823478835584456083463

theorem tailTrace_6776932 : CollatzResearch.WordTrace tailWord_6776932 prefixEnd_6776932 3479823478835584456083463 := by
  unfold tailWord_6776932
  simp only [CollatzResearch.WordTrace]
  refine ⟨123587508142170123342382525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164783344189560164456510033 123587508142170123342382525)
  ·
    refine ⟨46345315553313796253393447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123587508142170123342382525 46345315553313796253393447)
    ·
      refine ⟨69517973329970694380090171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46345315553313796253393447 69517973329970694380090171)
      ·
        refine ⟨104276959994956041570135257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69517973329970694380090171 104276959994956041570135257)
        ·
          refine ⟨78207719996217031177601443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104276959994956041570135257 78207719996217031177601443)
          ·
            refine ⟨117311579994325546766402165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78207719996217031177601443 117311579994325546766402165)
            ·
              refine ⟨10997960624468020009350203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117311579994325546766402165 10997960624468020009350203)
              ·
                refine ⟨16496940936702030014025305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10997960624468020009350203 16496940936702030014025305)
                ·
                  refine ⟨12372705702526522510518979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16496940936702030014025305 12372705702526522510518979)
                  ·
                    refine ⟨18559058553789783765778469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12372705702526522510518979 18559058553789783765778469)
                    ·
                      refine ⟨3479823478835584456083463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18559058553789783765778469 3479823478835584456083463)
                      ·
                        rfl

theorem cell23_6776932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_6776932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776932 prefixEnd_6776932 := by exact prefixLift 6776932
  have htrace : WordTrace (prefixWord ++ tailWord_6776932) baseStart_6776932 baseEnd_6776932 := by
    simpa [prefixWord, tailWord_6776932, baseEnd_6776932] using wordTrace_append hprefix tailTrace_6776932
  have hstable : (prefixWord ++ tailWord_6776932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776932).length < 2 ^ (prefixWord ++ tailWord_6776932).sum := by decide
  have hdescent : baseEnd_6776932 < baseStart_6776932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776942 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_6776942 : Nat := 118140960795 + 6776942 * 2 ^ 59
def prefixEnd_6776942 : Nat := 4983230072969 + 3 ^ 40 * 6776942 * 2
def baseEnd_6776942 : Nat := 1159942871214043138986139

theorem tailTrace_6776942 : CollatzResearch.WordTrace tailWord_6776942 prefixEnd_6776942 1159942871214043138986139 := by
  unfold tailWord_6776942
  simp only [CollatzResearch.WordTrace]
  refine ⟨30896922626788002299078635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164783587342869345595086053 30896922626788002299078635)
  ·
    refine ⟨46345383940182003448617953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30896922626788002299078635 46345383940182003448617953)
    ·
      refine ⟨34759037955136502586463465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46345383940182003448617953 34759037955136502586463465)
      ·
        refine ⟨26069278466352376939847599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34759037955136502586463465 26069278466352376939847599)
        ·
          refine ⟨39103917699528565409771399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26069278466352376939847599 39103917699528565409771399)
          ·
            refine ⟨58655876549292848114657099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39103917699528565409771399 58655876549292848114657099)
            ·
              refine ⟨87983814823939272171985649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58655876549292848114657099 87983814823939272171985649)
              ·
                refine ⟨65987861117954454128989237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87983814823939272171985649 65987861117954454128989237)
                ·
                  refine ⟨6186361979808230074592741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65987861117954454128989237 6186361979808230074592741)
                  ·
                    refine ⟨1159942871214043138986139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6186361979808230074592741 1159942871214043138986139)
                    ·
                      rfl

theorem cell23_6776942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_6776942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776942 prefixEnd_6776942 := by exact prefixLift 6776942
  have htrace : WordTrace (prefixWord ++ tailWord_6776942) baseStart_6776942 baseEnd_6776942 := by
    simpa [prefixWord, tailWord_6776942, baseEnd_6776942] using wordTrace_append hprefix tailTrace_6776942
  have hstable : (prefixWord ++ tailWord_6776942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776942).length < 2 ^ (prefixWord ++ tailWord_6776942).sum := by decide
  have hdescent : baseEnd_6776942 < baseStart_6776942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776985 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 3, 5]
def baseStart_6776985 : Nat := 118140960795 + 6776985 * 2 ^ 59
def prefixEnd_6776985 : Nat := 4983230072969 + 3 ^ 40 * 6776985 * 2
def baseEnd_6776985 : Nat := 1159950231103424249573573

theorem tailTrace_6776985 : CollatzResearch.WordTrace tailWord_6776985 prefixEnd_6776985 1159950231103424249573573 := by
  unfold tailWord_6776985
  simp only [CollatzResearch.WordTrace]
  refine ⟨247176949353148236736444409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164784632902098824490962939 247176949353148236736444409)
  ·
    refine ⟨185382712014861177552333307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247176949353148236736444409 185382712014861177552333307)
    ·
      refine ⟨278074068022291766328499961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185382712014861177552333307 278074068022291766328499961)
      ·
        refine ⟨208555551016718824746374971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278074068022291766328499961 208555551016718824746374971)
        ·
          refine ⟨312833326525078237119562457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208555551016718824746374971 312833326525078237119562457)
          ·
            refine ⟨234624994893808677839671843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312833326525078237119562457 234624994893808677839671843)
            ·
              refine ⟨351937492340713016759507765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234624994893808677839671843 351937492340713016759507765)
              ·
                refine ⟨32994139906941845321203853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 351937492340713016759507765 32994139906941845321203853)
                ·
                  refine ⟨12372802465103191995451445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32994139906941845321203853 12372802465103191995451445)
                  ·
                    refine ⟨1159950231103424249573573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12372802465103191995451445 1159950231103424249573573)
                    ·
                      rfl

theorem cell23_6776985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_6776985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776985 prefixEnd_6776985 := by exact prefixLift 6776985
  have htrace : WordTrace (prefixWord ++ tailWord_6776985) baseStart_6776985 baseEnd_6776985 := by
    simpa [prefixWord, tailWord_6776985, baseEnd_6776985] using wordTrace_append hprefix tailTrace_6776985
  have hstable : (prefixWord ++ tailWord_6776985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776985).length < 2 ^ (prefixWord ++ tailWord_6776985).sum := by decide
  have hdescent : baseEnd_6776985 < baseStart_6776985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777035 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 6]
def baseStart_6777035 : Nat := 118140960795 + 6777035 * 2 ^ 59
def prefixEnd_6777035 : Nat := 4983230072969 + 3 ^ 40 * 6777035 * 2
def baseEnd_6777035 : Nat := 3479876367342997553095489

theorem tailTrace_6777035 : CollatzResearch.WordTrace tailWord_6777035 prefixEnd_6777035 3479876367342997553095489 := by
  unfold tailWord_6777035
  simp only [CollatzResearch.WordTrace]
  refine ⟨247178773002967095275764559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164785848668644730183843039 247178773002967095275764559)
  ·
    refine ⟨370768159504450642913646839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247178773002967095275764559 370768159504450642913646839)
    ·
      refine ⟨556152239256675964370470259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370768159504450642913646839 556152239256675964370470259)
      ·
        refine ⟨834228358885013946555705389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556152239256675964370470259 834228358885013946555705389)
        ·
          refine ⟨312835634581880229958389521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 834228358885013946555705389 312835634581880229958389521)
          ·
            refine ⟨234626725936410172468792141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312835634581880229958389521 234626725936410172468792141)
            ·
              refine ⟨87985022226153814675797053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234626725936410172468792141 87985022226153814675797053)
              ·
                refine ⟨32994383334807680503423895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87985022226153814675797053 32994383334807680503423895)
                ·
                  refine ⟨49491575002211520755135843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32994383334807680503423895 49491575002211520755135843)
                  ·
                    refine ⟨74237362503317281132703765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49491575002211520755135843 74237362503317281132703765)
                    ·
                      refine ⟨3479876367342997553095489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74237362503317281132703765 3479876367342997553095489)
                      ·
                        rfl

theorem cell23_6777035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 6].length) (baseStart_6777035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777035 prefixEnd_6777035 := by exact prefixLift 6777035
  have htrace : WordTrace (prefixWord ++ tailWord_6777035) baseStart_6777035 baseEnd_6777035 := by
    simpa [prefixWord, tailWord_6777035, baseEnd_6777035] using wordTrace_append hprefix tailTrace_6777035
  have hstable : (prefixWord ++ tailWord_6777035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777035).length < 2 ^ (prefixWord ++ tailWord_6777035).sum := by decide
  have hdescent : baseEnd_6777035 < baseStart_6777035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777039 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 5, 2, 2]
def baseStart_6777039 : Nat := 118140960795 + 6777039 * 2 ^ 59
def prefixEnd_6777039 : Nat := 4983230072969 + 3 ^ 40 * 6777039 * 2
def baseEnd_6777039 : Nat := 3479878421265615537445471

theorem tailTrace_6777039 : CollatzResearch.WordTrace tailWord_6777039 prefixEnd_6777039 3479878421265615537445471 := by
  unfold tailWord_6777039
  simp only [CollatzResearch.WordTrace]
  refine ⟨247178918894952603958910171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164785945929968402639273447 247178918894952603958910171)
  ·
    refine ⟨370768378342428905938365257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247178918894952603958910171 370768378342428905938365257)
    ·
      refine ⟨278076283756821679453773943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370768378342428905938365257 278076283756821679453773943)
      ·
        refine ⟨417114425635232519180660915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278076283756821679453773943 417114425635232519180660915)
        ·
          refine ⟨625671638452848778770991373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417114425635232519180660915 625671638452848778770991373)
          ·
            refine ⟨234626864419818292039121765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 625671638452848778770991373 234626864419818292039121765)
            ·
              refine ⟨43992537078715929757335331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234626864419818292039121765 43992537078715929757335331)
              ·
                refine ⟨65988805618073894636002997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43992537078715929757335331 65988805618073894636002997)
                ·
                  refine ⟨6186450526694427622125281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65988805618073894636002997 6186450526694427622125281)
                  ·
                    refine ⟨4639837895020820716593961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6186450526694427622125281 4639837895020820716593961)
                    ·
                      refine ⟨3479878421265615537445471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639837895020820716593961 3479878421265615537445471)
                      ·
                        rfl

theorem cell23_6777039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 2, 2].length) (baseStart_6777039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777039 prefixEnd_6777039 := by exact prefixLift 6777039
  have htrace : WordTrace (prefixWord ++ tailWord_6777039) baseStart_6777039 baseEnd_6777039 := by
    simpa [prefixWord, tailWord_6777039, baseEnd_6777039] using wordTrace_append hprefix tailTrace_6777039
  have hstable : (prefixWord ++ tailWord_6777039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777039).length < 2 ^ (prefixWord ++ tailWord_6777039).sum := by decide
  have hdescent : baseEnd_6777039 < baseStart_6777039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777075 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 1, 9]
def baseStart_6777075 : Nat := 118140960795 + 6777075 * 2 ^ 59
def prefixEnd_6777075 : Nat := 4983230072969 + 3 ^ 40 * 6777075 * 2
def baseEnd_6777075 : Nat := 1159965635523059132198435

theorem tailTrace_6777075 : CollatzResearch.WordTrace tailWord_6777075 prefixEnd_6777075 1159965635523059132198435 := by
  unfold tailWord_6777075
  simp only [CollatzResearch.WordTrace]
  refine ⟨247180231922822182107220679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164786821281881454738147119 247180231922822182107220679)
  ·
    refine ⟨370770347884233273160831019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247180231922822182107220679 370770347884233273160831019)
    ·
      refine ⟨556155521826349909741246529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370770347884233273160831019 556155521826349909741246529)
      ·
        refine ⟨417116641369762432305934897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556155521826349909741246529 417116641369762432305934897)
        ·
          refine ⟨312837481027321824229451173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417116641369762432305934897 312837481027321824229451173)
          ·
            refine ⟨58657027692622842043022095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312837481027321824229451173 58657027692622842043022095)
            ·
              refine ⟨87985541538934263064533143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58657027692622842043022095 87985541538934263064533143)
              ·
                refine ⟨131978312308401394596799715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87985541538934263064533143 131978312308401394596799715)
                ·
                  refine ⟨197967468462602091895199573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131978312308401394596799715 197967468462602091895199573)
                  ·
                    refine ⟨1159965635523059132198435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 197967468462602091895199573 1159965635523059132198435)
                    ·
                      rfl

theorem cell23_6777075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 9].length) (baseStart_6777075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777075 prefixEnd_6777075 := by exact prefixLift 6777075
  have htrace : WordTrace (prefixWord ++ tailWord_6777075) baseStart_6777075 baseEnd_6777075 := by
    simpa [prefixWord, tailWord_6777075, baseEnd_6777075] using wordTrace_append hprefix tailTrace_6777075
  have hstable : (prefixWord ++ tailWord_6777075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777075).length < 2 ^ (prefixWord ++ tailWord_6777075).sum := by decide
  have hdescent : baseEnd_6777075 < baseStart_6777075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777089 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_6777089 : Nat := 118140960795 + 6777089 * 2 ^ 59
def prefixEnd_6777089 : Nat := 4983230072969 + 3 ^ 40 * 6777089 * 2
def baseEnd_6777089 : Nat := 3479904095298340341820241

theorem tailTrace_6777089 : CollatzResearch.WordTrace tailWord_6777089 prefixEnd_6777089 3479904095298340341820241 := by
  unfold tailWord_6777089
  simp only [CollatzResearch.WordTrace]
  refine ⟨247180742544771462498230321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164787161696514308332153547 247180742544771462498230321)
  ·
    refine ⟨185385556908578596873672741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247180742544771462498230321 185385556908578596873672741)
    ·
      refine ⟨34759791920358486913813639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185385556908578596873672741 34759791920358486913813639)
      ·
        refine ⟨52139687880537730370720459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34759791920358486913813639 52139687880537730370720459)
        ·
          refine ⟨78209531820806595556080689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52139687880537730370720459 78209531820806595556080689)
          ·
            refine ⟨58657148865604946667060517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78209531820806595556080689 58657148865604946667060517)
            ·
              refine ⟨10998215412300927500073847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58657148865604946667060517 10998215412300927500073847)
              ·
                refine ⟨16497323118451391250110771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10998215412300927500073847 16497323118451391250110771)
                ·
                  refine ⟨24745984677677086875166157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16497323118451391250110771 24745984677677086875166157)
                  ·
                    refine ⟨9279744254128907578187309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24745984677677086875166157 9279744254128907578187309)
                    ·
                      refine ⟨3479904095298340341820241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9279744254128907578187309 3479904095298340341820241)
                      ·
                        rfl

theorem cell23_6777089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_6777089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777089 prefixEnd_6777089 := by exact prefixLift 6777089
  have htrace : WordTrace (prefixWord ++ tailWord_6777089) baseStart_6777089 baseEnd_6777089 := by
    simpa [prefixWord, tailWord_6777089, baseEnd_6777089] using wordTrace_append hprefix tailTrace_6777089
  have hstable : (prefixWord ++ tailWord_6777089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777089).length < 2 ^ (prefixWord ++ tailWord_6777089).sum := by decide
  have hdescent : baseEnd_6777089 < baseStart_6777089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777099 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 3, 3, 2]
def baseStart_6777099 : Nat := 118140960795 + 6777099 * 2 ^ 59
def prefixEnd_6777099 : Nat := 4983230072969 + 3 ^ 40 * 6777099 * 2
def baseEnd_6777099 : Nat := 3479909230104885302695195

theorem tailTrace_6777099 : CollatzResearch.WordTrace tailWord_6777099 prefixEnd_6777099 3479909230104885302695195 := by
  unfold tailWord_6777099
  simp only [CollatzResearch.WordTrace]
  refine ⟨247181107274735234206094351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164787404849823489470729567 247181107274735234206094351)
  ·
    refine ⟨370771660912102851309141527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247181107274735234206094351 370771660912102851309141527)
    ·
      refine ⟨556157491368154276963712291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370771660912102851309141527 556157491368154276963712291)
      ·
        refine ⟨834236237052231415445568437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556157491368154276963712291 834236237052231415445568437)
        ·
          refine ⟨78209647223646695198022041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 834236237052231415445568437 78209647223646695198022041)
          ·
            refine ⟨58657235417735021398516531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78209647223646695198022041 58657235417735021398516531)
            ·
              refine ⟨87985853126602532097774797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58657235417735021398516531 87985853126602532097774797)
              ·
                refine ⟨32994694922475949536665549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87985853126602532097774797 32994694922475949536665549)
                ·
                  refine ⟨12373010595928481076249581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32994694922475949536665549 12373010595928481076249581)
                  ·
                    refine ⟨4639878973473180403593593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12373010595928481076249581 4639878973473180403593593)
                    ·
                      refine ⟨3479909230104885302695195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639878973473180403593593 3479909230104885302695195)
                      ·
                        rfl

theorem cell23_6777099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 3, 2].length) (baseStart_6777099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777099 prefixEnd_6777099 := by exact prefixLift 6777099
  have htrace : WordTrace (prefixWord ++ tailWord_6777099) baseStart_6777099 baseEnd_6777099 := by
    simpa [prefixWord, tailWord_6777099, baseEnd_6777099] using wordTrace_append hprefix tailTrace_6777099
  have hstable : (prefixWord ++ tailWord_6777099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777099).length < 2 ^ (prefixWord ++ tailWord_6777099).sum := by decide
  have hdescent : baseEnd_6777099 < baseStart_6777099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777102 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_6777102 : Nat := 118140960795 + 6777102 * 2 ^ 59
def prefixEnd_6777102 : Nat := 4983230072969 + 3 ^ 40 * 6777102 * 2
def baseEnd_6777102 : Nat := 3479910770546848790957681

theorem tailTrace_6777102 : CollatzResearch.WordTrace tailWord_6777102 prefixEnd_6777102 3479910770546848790957681 := by
  unfold tailWord_6777102
  simp only [CollatzResearch.WordTrace]
  refine ⟨30897652086715545714806695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164787477795816243812302373 30897652086715545714806695)
  ·
    refine ⟨46346478130073318572210043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30897652086715545714806695 46346478130073318572210043)
    ·
      refine ⟨69519717195109977858315065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46346478130073318572210043 69519717195109977858315065)
      ·
        refine ⟨52139787896332483393736299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69519717195109977858315065 52139787896332483393736299)
        ·
          refine ⟨78209681844498725090604449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52139787896332483393736299 78209681844498725090604449)
          ·
            refine ⟨58657261383374043817953337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78209681844498725090604449 58657261383374043817953337)
            ·
              refine ⟨43992946037530532863465003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58657261383374043817953337 43992946037530532863465003)
              ·
                refine ⟨65989419056295799295197505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43992946037530532863465003 65989419056295799295197505)
                ·
                  refine ⟨49492064292221849471398129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65989419056295799295197505 49492064292221849471398129)
                  ·
                    refine ⟨37119048219166387103548597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49492064292221849471398129 37119048219166387103548597)
                    ·
                      refine ⟨3479910770546848790957681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37119048219166387103548597 3479910770546848790957681)
                      ·
                        rfl

theorem cell23_6777102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_6777102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777102 prefixEnd_6777102 := by exact prefixLift 6777102
  have htrace : WordTrace (prefixWord ++ tailWord_6777102) baseStart_6777102 baseEnd_6777102 := by
    simpa [prefixWord, tailWord_6777102, baseEnd_6777102] using wordTrace_append hprefix tailTrace_6777102
  have hstable : (prefixWord ++ tailWord_6777102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777102).length < 2 ^ (prefixWord ++ tailWord_6777102).sum := by decide
  have hdescent : baseEnd_6777102 < baseStart_6777102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777132 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 3]
def baseStart_6777132 : Nat := 118140960795 + 6777132 * 2 ^ 59
def prefixEnd_6777132 : Nat := 4983230072969 + 3 ^ 40 * 6777132 * 2
def baseEnd_6777132 : Nat := 3479926174966483673582543

theorem tailTrace_6777132 : CollatzResearch.WordTrace tailWord_6777132 prefixEnd_6777132 3479926174966483673582543 := by
  unfold tailWord_6777132
  simp only [CollatzResearch.WordTrace]
  refine ⟨123591155441807840421022825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164788207255743787228030433 123591155441807840421022825)
  ·
    refine ⟨92693366581355880315767119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123591155441807840421022825 92693366581355880315767119)
    ·
      refine ⟨139040049872033820473650679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92693366581355880315767119 139040049872033820473650679)
      ·
        refine ⟨208560074808050730710476019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139040049872033820473650679 208560074808050730710476019)
        ·
          refine ⟨312840112212076096065714029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208560074808050730710476019 312840112212076096065714029)
          ·
            refine ⟨117315042079528536024642761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312840112212076096065714029 117315042079528536024642761)
            ·
              refine ⟨87986281559646402018482071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117315042079528536024642761 87986281559646402018482071)
              ·
                refine ⟨131979422339469603027723107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87986281559646402018482071 131979422339469603027723107)
                ·
                  refine ⟨197969133509204404541584661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131979422339469603027723107 197969133509204404541584661)
                  ·
                    refine ⟨9279803133243956462886781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 197969133509204404541584661 9279803133243956462886781)
                    ·
                      refine ⟨3479926174966483673582543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9279803133243956462886781 3479926174966483673582543)
                      ·
                        rfl

theorem cell23_6777132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_6777132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777132 prefixEnd_6777132 := by exact prefixLift 6777132
  have htrace : WordTrace (prefixWord ++ tailWord_6777132) baseStart_6777132 baseEnd_6777132 := by
    simpa [prefixWord, tailWord_6777132, baseEnd_6777132] using wordTrace_append hprefix tailTrace_6777132
  have hstable : (prefixWord ++ tailWord_6777132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777132).length < 2 ^ (prefixWord ++ tailWord_6777132).sum := by decide
  have hdescent : baseEnd_6777132 < baseStart_6777132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777140 : List Nat := [2, 5, 1, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_6777140 : Nat := 118140960795 + 6777140 * 2 ^ 59
def prefixEnd_6777140 : Nat := 4983230072969 + 3 ^ 40 * 6777140 * 2
def baseEnd_6777140 : Nat := 3479930282811719642282507

theorem tailTrace_6777140 : CollatzResearch.WordTrace tailWord_6777140 prefixEnd_6777140 3479930282811719642282507 := by
  unfold tailWord_6777140
  simp only [CollatzResearch.WordTrace]
  refine ⟨123591301333793349104168437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164788401778391132138891249 123591301333793349104168437)
  ·
    refine ⟨11586684500043126478515791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123591301333793349104168437 11586684500043126478515791)
    ·
      refine ⟨17380026750064689717773687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11586684500043126478515791 17380026750064689717773687)
      ·
        refine ⟨26070040125097034576660531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17380026750064689717773687 26070040125097034576660531)
        ·
          refine ⟨39105060187645551864990797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26070040125097034576660531 39105060187645551864990797)
          ·
            refine ⟨14664397570367081949371549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39105060187645551864990797 14664397570367081949371549)
            ·
              refine ⟨5499149088887655731014331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14664397570367081949371549 5499149088887655731014331)
              ·
                refine ⟨8248723633331483596521497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5499149088887655731014331 8248723633331483596521497)
                ·
                  refine ⟨6186542724998612697391123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8248723633331483596521497 6186542724998612697391123)
                  ·
                    refine ⟨9279814087497919046086685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6186542724998612697391123 9279814087497919046086685)
                    ·
                      refine ⟨3479930282811719642282507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9279814087497919046086685 3479930282811719642282507)
                      ·
                        rfl

theorem cell23_6777140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_6777140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777140 prefixEnd_6777140 := by exact prefixLift 6777140
  have htrace : WordTrace (prefixWord ++ tailWord_6777140) baseStart_6777140 baseEnd_6777140 := by
    simpa [prefixWord, tailWord_6777140, baseEnd_6777140] using wordTrace_append hprefix tailTrace_6777140
  have hstable : (prefixWord ++ tailWord_6777140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777140).length < 2 ^ (prefixWord ++ tailWord_6777140).sum := by decide
  have hdescent : baseEnd_6777140 < baseStart_6777140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777146 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2]
def baseStart_6777146 : Nat := 118140960795 + 6777146 * 2 ^ 59
def prefixEnd_6777146 : Nat := 4983230072969 + 3 ^ 40 * 6777146 * 2
def baseEnd_6777146 : Nat := 3479933363695646618807479

theorem tailTrace_6777146 : CollatzResearch.WordTrace tailWord_6777146 prefixEnd_6777146 3479933363695646618807479 := by
  unfold tailWord_6777146
  simp only [CollatzResearch.WordTrace]
  refine ⟨61795705376391240308263823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164788547670376640822036861 61795705376391240308263823)
  ·
    refine ⟨92693558064586860462395735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61795705376391240308263823 92693558064586860462395735)
    ·
      refine ⟨139040337096880290693593603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92693558064586860462395735 139040337096880290693593603)
      ·
        refine ⟨208560505645320436040390405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139040337096880290693593603 208560505645320436040390405)
        ·
          refine ⟨39105094808497581757573201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208560505645320436040390405 39105094808497581757573201)
          ·
            refine ⟨29328821106373186318179901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39105094808497581757573201 29328821106373186318179901)
            ·
              refine ⟨10998307914889944869317463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29328821106373186318179901 10998307914889944869317463)
              ·
                refine ⟨16497461872334917303976195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10998307914889944869317463 16497461872334917303976195)
                ·
                  refine ⟨24746192808502375955964293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16497461872334917303976195 24746192808502375955964293)
                  ·
                    refine ⟨4639911151594195491743305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24746192808502375955964293 4639911151594195491743305)
                    ·
                      refine ⟨3479933363695646618807479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639911151594195491743305 3479933363695646618807479)
                      ·
                        rfl

theorem cell23_6777146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2].length) (baseStart_6777146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777146 prefixEnd_6777146 := by exact prefixLift 6777146
  have htrace : WordTrace (prefixWord ++ tailWord_6777146) baseStart_6777146 baseEnd_6777146 := by
    simpa [prefixWord, tailWord_6777146, baseEnd_6777146] using wordTrace_append hprefix tailTrace_6777146
  have hstable : (prefixWord ++ tailWord_6777146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777146).length < 2 ^ (prefixWord ++ tailWord_6777146).sum := by decide
  have hdescent : baseEnd_6777146 < baseStart_6777146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777186 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 7]
def baseStart_6777186 : Nat := 118140960795 + 6777186 * 2 ^ 59
def prefixEnd_6777186 : Nat := 4983230072969 + 3 ^ 40 * 6777186 * 2
def baseEnd_6777186 : Nat := 386661544769091829145255

theorem tailTrace_6777186 : CollatzResearch.WordTrace tailWord_6777186 prefixEnd_6777186 386661544769091829145255 := by
  unfold tailWord_6777186
  simp only [CollatzResearch.WordTrace]
  refine ⟨61796070106355012016127853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164789520283613365376340941 61796070106355012016127853)
  ·
    refine ⟨23173526289883129506047945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61796070106355012016127853 23173526289883129506047945)
    ·
      refine ⟨17380144717412347129535959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23173526289883129506047945 17380144717412347129535959)
      ·
        refine ⟨26070217076118520694303939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17380144717412347129535959 26070217076118520694303939)
        ·
          refine ⟨39105325614177781041455909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26070217076118520694303939 39105325614177781041455909)
          ·
            refine ⟨7332248552658333945272983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39105325614177781041455909 7332248552658333945272983)
            ·
              refine ⟨10998372828987500917909475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7332248552658333945272983 10998372828987500917909475)
              ·
                refine ⟨16497559243481251376864213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10998372828987500917909475 16497559243481251376864213)
                ·
                  refine ⟨386661544769091829145255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16497559243481251376864213 386661544769091829145255)
                  ·
                    rfl

theorem cell23_6777186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_6777186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777186 prefixEnd_6777186 := by exact prefixLift 6777186
  have htrace : WordTrace (prefixWord ++ tailWord_6777186) baseStart_6777186 baseEnd_6777186 := by
    simpa [prefixWord, tailWord_6777186, baseEnd_6777186] using wordTrace_append hprefix tailTrace_6777186
  have hstable : (prefixWord ++ tailWord_6777186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777186).length < 2 ^ (prefixWord ++ tailWord_6777186).sum := by decide
  have hdescent : baseEnd_6777186 < baseStart_6777186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777232 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 4]
def baseStart_6777232 : Nat := 118140960795 + 6777232 * 2 ^ 59
def prefixEnd_6777232 : Nat := 4983230072969 + 3 ^ 40 * 6777232 * 2
def baseEnd_6777232 : Nat := 3479977523031933282332083

theorem tailTrace_6777232 : CollatzResearch.WordTrace tailWord_6777232 prefixEnd_6777232 3479977523031933282332083 := by
  unfold tailWord_6777232
  simp only [CollatzResearch.WordTrace]
  refine ⟨123592979091626698960342975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164790638788835598613790633 123592979091626698960342975)
  ·
    refine ⟨185389468637440048440514463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123592979091626698960342975 185389468637440048440514463)
    ·
      refine ⟨278084202956160072660771695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185389468637440048440514463 278084202956160072660771695)
      ·
        refine ⟨417126304434240108991157543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278084202956160072660771695 417126304434240108991157543)
        ·
          refine ⟨625689456651360163486736315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417126304434240108991157543 625689456651360163486736315)
          ·
            refine ⟨938534184977040245230104473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625689456651360163486736315 938534184977040245230104473)
            ·
              refine ⟨703900638732780183922578355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 938534184977040245230104473 703900638732780183922578355)
              ·
                refine ⟨1055850958099170275883867533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703900638732780183922578355 1055850958099170275883867533)
                ·
                  refine ⟨395944109287188853456450325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055850958099170275883867533 395944109287188853456450325)
                  ·
                    refine ⟨18559880122836977505771109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 395944109287188853456450325 18559880122836977505771109)
                    ·
                      refine ⟨3479977523031933282332083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18559880122836977505771109 3479977523031933282332083)
                      ·
                        rfl

theorem cell23_6777232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_6777232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777232 prefixEnd_6777232 := by exact prefixLift 6777232
  have htrace : WordTrace (prefixWord ++ tailWord_6777232) baseStart_6777232 baseEnd_6777232 := by
    simpa [prefixWord, tailWord_6777232, baseEnd_6777232] using wordTrace_append hprefix tailTrace_6777232
  have hstable : (prefixWord ++ tailWord_6777232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777232).length < 2 ^ (prefixWord ++ tailWord_6777232).sum := by decide
  have hdescent : baseEnd_6777232 < baseStart_6777232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777273 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 2, 2, 3]
def baseStart_6777273 : Nat := 118140960795 + 6777273 * 2 ^ 59
def prefixEnd_6777273 : Nat := 4983230072969 + 3 ^ 40 * 6777273 * 2
def baseEnd_6777273 : Nat := 3479998575738767621919395

theorem tailTrace_6777273 : CollatzResearch.WordTrace tailWord_6777273 prefixEnd_6777273 3479998575738767621919395 := by
  unfold tailWord_6777273
  simp only [CollatzResearch.WordTrace]
  refine ⟨247187453576104861922928473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164791635717403241281952315 247187453576104861922928473)
  ·
    refine ⟨185390590182078646442196355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247187453576104861922928473 185390590182078646442196355)
    ·
      refine ⟨278085885273117969663294533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185390590182078646442196355 278085885273117969663294533)
      ·
        refine ⟨52141103488709619311867725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278085885273117969663294533 52141103488709619311867725)
        ·
          refine ⟨19552913808266107241950397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52141103488709619311867725 19552913808266107241950397)
          ·
            refine ⟨7332342678099790215731399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19552913808266107241950397 7332342678099790215731399)
            ·
              refine ⟨10998514017149685323597099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7332342678099790215731399 10998514017149685323597099)
              ·
                refine ⟨16497771025724527985395649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10998514017149685323597099 16497771025724527985395649)
                ·
                  refine ⟨12373328269293395989046737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16497771025724527985395649 12373328269293395989046737)
                  ·
                    refine ⟨9279996201970046991785053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12373328269293395989046737 9279996201970046991785053)
                    ·
                      refine ⟨3479998575738767621919395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9279996201970046991785053 3479998575738767621919395)
                      ·
                        rfl

theorem cell23_6777273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_6777273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777273 prefixEnd_6777273 := by exact prefixLift 6777273
  have htrace : WordTrace (prefixWord ++ tailWord_6777273) baseStart_6777273 baseEnd_6777273 := by
    simpa [prefixWord, tailWord_6777273, baseEnd_6777273] using wordTrace_append hprefix tailTrace_6777273
  have hstable : (prefixWord ++ tailWord_6777273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777273).length < 2 ^ (prefixWord ++ tailWord_6777273).sum := by decide
  have hdescent : baseEnd_6777273 < baseStart_6777273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777329 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_6777329 : Nat := 118140960795 + 6777329 * 2 ^ 59
def prefixEnd_6777329 : Nat := 4983230072969 + 3 ^ 40 * 6777329 * 2
def baseEnd_6777329 : Nat := 3480027330655419402819137

theorem tailTrace_6777329 : CollatzResearch.WordTrace tailWord_6777329 prefixEnd_6777329 3480027330655419402819137 := by
  unfold tailWord_6777329
  simp only [CollatzResearch.WordTrace]
  refine ⟨247189496063901983486967041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164792997375934655657978027 247189496063901983486967041)
  ·
    refine ⟨185392122047926487615225281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247189496063901983486967041 185392122047926487615225281)
    ·
      refine ⟨139044091535944865711418961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185392122047926487615225281 139044091535944865711418961)
      ·
        refine ⟨104283068651958649283564221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139044091535944865711418961 104283068651958649283564221)
        ·
          refine ⟨39106150744484493481336583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104283068651958649283564221 39106150744484493481336583)
          ·
            refine ⟨58659226116726740222004875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39106150744484493481336583 58659226116726740222004875)
            ·
              refine ⟨87988839175090110333007313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58659226116726740222004875 87988839175090110333007313)
              ·
                refine ⟨65991629381317582749755485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87988839175090110333007313 65991629381317582749755485)
                ·
                  refine ⟨24746861017994093531158307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65991629381317582749755485 24746861017994093531158307)
                  ·
                    refine ⟨37120291526991140296737461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24746861017994093531158307 37120291526991140296737461)
                    ·
                      refine ⟨3480027330655419402819137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37120291526991140296737461 3480027330655419402819137)
                      ·
                        rfl

theorem cell23_6777329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_6777329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777329 prefixEnd_6777329 := by exact prefixLift 6777329
  have htrace : WordTrace (prefixWord ++ tailWord_6777329) baseStart_6777329 baseEnd_6777329 := by
    simpa [prefixWord, tailWord_6777329, baseEnd_6777329] using wordTrace_append hprefix tailTrace_6777329
  have hstable : (prefixWord ++ tailWord_6777329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777329).length < 2 ^ (prefixWord ++ tailWord_6777329).sum := by decide
  have hdescent : baseEnd_6777329 < baseStart_6777329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777380 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_6777380 : Nat := 118140960795 + 6777380 * 2 ^ 59
def prefixEnd_6777380 : Nat := 4983230072969 + 3 ^ 40 * 6777380 * 2
def baseEnd_6777380 : Nat := 3480053518168798703281403

theorem tailTrace_6777380 : CollatzResearch.WordTrace tailWord_6777380 prefixEnd_6777380 3480053518168798703281403 := by
  unfold tailWord_6777380
  simp only [CollatzResearch.WordTrace]
  refine ⟨123595678093358609598536797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164794237457811479464715729 123595678093358609598536797)
  ·
    refine ⟨46348379285009478599451299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123595678093358609598536797 46348379285009478599451299)
    ·
      refine ⟨69522568927514217899176949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46348379285009478599451299 69522568927514217899176949)
      ·
        refine ⟨6517740836954457928047839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69522568927514217899176949 6517740836954457928047839)
        ·
          refine ⟨9776611255431686892071759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6517740836954457928047839 9776611255431686892071759)
          ·
            refine ⟨14664916883147530338107639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9776611255431686892071759 14664916883147530338107639)
            ·
              refine ⟨21997375324721295507161459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14664916883147530338107639 21997375324721295507161459)
              ·
                refine ⟨32996062987081943260742189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21997375324721295507161459 32996062987081943260742189)
                ·
                  refine ⟨12373523620155728722778321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32996062987081943260742189 12373523620155728722778321)
                  ·
                    refine ⟨9280142715116796542083741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12373523620155728722778321 9280142715116796542083741)
                    ·
                      refine ⟨3480053518168798703281403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9280142715116796542083741 3480053518168798703281403)
                      ·
                        rfl

theorem cell23_6777380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_6777380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777380 prefixEnd_6777380 := by exact prefixLift 6777380
  have htrace : WordTrace (prefixWord ++ tailWord_6777380) baseStart_6777380 baseEnd_6777380 := by
    simpa [prefixWord, tailWord_6777380, baseEnd_6777380] using wordTrace_append hprefix tailTrace_6777380
  have hstable : (prefixWord ++ tailWord_6777380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777380).length < 2 ^ (prefixWord ++ tailWord_6777380).sum := by decide
  have hdescent : baseEnd_6777380 < baseStart_6777380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777419 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 5]
def baseStart_6777419 : Nat := 118140960795 + 6777419 * 2 ^ 59
def prefixEnd_6777419 : Nat := 4983230072969 + 3 ^ 40 * 6777419 * 2
def baseEnd_6777419 : Nat := 3480073543914324050693723

theorem tailTrace_6777419 : CollatzResearch.WordTrace tailWord_6777419 prefixEnd_6777419 3480073543914324050693723 := by
  unfold tailWord_6777419
  simp only [CollatzResearch.WordTrace]
  refine ⟨247192778633575928857743311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164795185755717285905162207 247192778633575928857743311)
  ·
    refine ⟨370789167950363893286614967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247192778633575928857743311 370789167950363893286614967)
    ·
      refine ⟨556183751925545839929922451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370789167950363893286614967 556183751925545839929922451)
      ·
        refine ⟨834275627888318759894883677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556183751925545839929922451 834275627888318759894883677)
        ·
          refine ⟨312853360458119534960581379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 834275627888318759894883677 312853360458119534960581379)
          ·
            refine ⟨469280040687179302440872069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312853360458119534960581379 469280040687179302440872069)
            ·
              refine ⟨87990007628846119207663513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 469280040687179302440872069 87990007628846119207663513)
              ·
                refine ⟨65992505721634589405747635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87990007628846119207663513 65992505721634589405747635)
                ·
                  refine ⟨98988758582451884108621453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65992505721634589405747635 98988758582451884108621453)
                  ·
                    refine ⟨37120784468419456540733045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98988758582451884108621453 37120784468419456540733045)
                    ·
                      refine ⟨3480073543914324050693723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37120784468419456540733045 3480073543914324050693723)
                      ·
                        rfl

theorem cell23_6777419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_6777419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777419 prefixEnd_6777419 := by exact prefixLift 6777419
  have htrace : WordTrace (prefixWord ++ tailWord_6777419) baseStart_6777419 baseEnd_6777419 := by
    simpa [prefixWord, tailWord_6777419, baseEnd_6777419] using wordTrace_append hprefix tailTrace_6777419
  have hstable : (prefixWord ++ tailWord_6777419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777419).length < 2 ^ (prefixWord ++ tailWord_6777419).sum := by decide
  have hdescent : baseEnd_6777419 < baseStart_6777419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777426 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_6777426 : Nat := 118140960795 + 6777426 * 2 ^ 59
def prefixEnd_6777426 : Nat := 4983230072969 + 3 ^ 40 * 6777426 * 2
def baseEnd_6777426 : Nat := 1160025712759635174435397

theorem tailTrace_6777426 : CollatzResearch.WordTrace tailWord_6777426 prefixEnd_6777426 1160025712759635174435397 := by
  unfold tailWord_6777426
  simp only [CollatzResearch.WordTrace]
  refine ⟨61798258486137642263312033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164795355963033712702165421 61798258486137642263312033)
  ·
    refine ⟨46348693864603231697484025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61798258486137642263312033 46348693864603231697484025)
    ·
      refine ⟨34761520398452423773113019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46348693864603231697484025 34761520398452423773113019)
      ·
        refine ⟨52142280597678635659669529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34761520398452423773113019 52142280597678635659669529)
        ·
          refine ⟨39106710448258976744752147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52142280597678635659669529 39106710448258976744752147)
          ·
            refine ⟨58660065672388465117128221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39106710448258976744752147 58660065672388465117128221)
            ·
              refine ⟨21997524627145674418923083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58660065672388465117128221 21997524627145674418923083)
              ·
                refine ⟨32996286940718511628384625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21997524627145674418923083 32996286940718511628384625)
                ·
                  refine ⟨24747215205538883721288469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32996286940718511628384625 24747215205538883721288469)
                  ·
                    refine ⟨1160025712759635174435397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24747215205538883721288469 1160025712759635174435397)
                    ·
                      rfl

theorem cell23_6777426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_6777426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777426 prefixEnd_6777426 := by exact prefixLift 6777426
  have htrace : WordTrace (prefixWord ++ tailWord_6777426) baseStart_6777426 baseEnd_6777426 := by
    simpa [prefixWord, tailWord_6777426, baseEnd_6777426] using wordTrace_append hprefix tailTrace_6777426
  have hstable : (prefixWord ++ tailWord_6777426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777426).length < 2 ^ (prefixWord ++ tailWord_6777426).sum := by decide
  have hdescent : baseEnd_6777426 < baseStart_6777426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777433 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 8, 2, 2]
def baseStart_6777433 : Nat := 118140960795 + 6777433 * 2 ^ 59
def prefixEnd_6777433 : Nat := 4983230072969 + 3 ^ 40 * 6777433 * 2
def baseEnd_6777433 : Nat := 3480080732643486995918659

theorem tailTrace_6777433 : CollatzResearch.WordTrace tailWord_6777433 prefixEnd_6777433 3480080732643486995918659 := by
  unfold tailWord_6777433
  simp only [CollatzResearch.WordTrace]
  refine ⟨247193289255525209248752953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164795526170350139499168635 247193289255525209248752953)
  ·
    refine ⟨185394966941643906936564715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247193289255525209248752953 185394966941643906936564715)
    ·
      refine ⟨278092450412465860404847073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185394966941643906936564715 278092450412465860404847073)
      ·
        refine ⟨208569337809349395303635305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278092450412465860404847073 208569337809349395303635305)
        ·
          refine ⟨156427003357012046477726479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208569337809349395303635305 156427003357012046477726479)
          ·
            refine ⟨234640505035518069716589719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156427003357012046477726479 234640505035518069716589719)
            ·
              refine ⟨351960757553277104574884579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234640505035518069716589719 351960757553277104574884579)
              ·
                refine ⟨527941136329915656862326869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351960757553277104574884579 527941136329915656862326869)
                ·
                  refine ⟨6186810191366199103855393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 527941136329915656862326869 6186810191366199103855393)
                  ·
                    refine ⟨4640107643524649327891545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6186810191366199103855393 4640107643524649327891545)
                    ·
                      refine ⟨3480080732643486995918659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640107643524649327891545 3480080732643486995918659)
                      ·
                        rfl

theorem cell23_6777433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 2, 2].length) (baseStart_6777433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777433 prefixEnd_6777433 := by exact prefixLift 6777433
  have htrace : WordTrace (prefixWord ++ tailWord_6777433) baseStart_6777433 baseEnd_6777433 := by
    simpa [prefixWord, tailWord_6777433, baseEnd_6777433] using wordTrace_append hprefix tailTrace_6777433
  have hstable : (prefixWord ++ tailWord_6777433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777433).length < 2 ^ (prefixWord ++ tailWord_6777433).sum := by decide
  have hdescent : baseEnd_6777433 < baseStart_6777433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777449 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 7]
def baseStart_6777449 : Nat := 118140960795 + 6777449 * 2 ^ 59
def prefixEnd_6777449 : Nat := 4983230072969 + 3 ^ 40 * 6777449 * 2
def baseEnd_6777449 : Nat := 3480088948333958933318585

theorem tailTrace_6777449 : CollatzResearch.WordTrace tailWord_6777449 prefixEnd_6777449 3480088948333958933318585 := by
  unfold tailWord_6777449
  simp only [CollatzResearch.WordTrace]
  refine ⟨247193872823467243981335401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164795915215644829320890267 247193872823467243981335401)
  ·
    refine ⟨185395404617600432986001551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247193872823467243981335401 185395404617600432986001551)
    ·
      refine ⟨278093106926400649479002327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185395404617600432986001551 278093106926400649479002327)
      ·
        refine ⟨417139660389600974218503491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278093106926400649479002327 417139660389600974218503491)
        ·
          refine ⟨625709490584401461327755237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417139660389600974218503491 625709490584401461327755237)
          ·
            refine ⟨117320529484575273998954107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 625709490584401461327755237 117320529484575273998954107)
            ·
              refine ⟨175980794226862910998431161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117320529484575273998954107 175980794226862910998431161)
              ·
                refine ⟨131985595670147183248823371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175980794226862910998431161 131985595670147183248823371)
                ·
                  refine ⟨197978393505220774873235057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131985595670147183248823371 197978393505220774873235057)
                  ·
                    refine ⟨148483795128915581154926293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197978393505220774873235057 148483795128915581154926293)
                    ·
                      refine ⟨3480088948333958933318585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148483795128915581154926293 3480088948333958933318585)
                      ·
                        rfl

theorem cell23_6777449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_6777449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777449 prefixEnd_6777449 := by exact prefixLift 6777449
  have htrace : WordTrace (prefixWord ++ tailWord_6777449) baseStart_6777449 baseEnd_6777449 := by
    simpa [prefixWord, tailWord_6777449, baseEnd_6777449] using wordTrace_append hprefix tailTrace_6777449
  have hstable : (prefixWord ++ tailWord_6777449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777449).length < 2 ^ (prefixWord ++ tailWord_6777449).sum := by decide
  have hdescent : baseEnd_6777449 < baseStart_6777449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777450 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_6777450 : Nat := 118140960795 + 6777450 * 2 ^ 59
def prefixEnd_6777450 : Nat := 4983230072969 + 3 ^ 40 * 6777450 * 2
def baseEnd_6777450 : Nat := 3480089461814613429406081

theorem tailTrace_6777450 : CollatzResearch.WordTrace tailWord_6777450 prefixEnd_6777450 3480089461814613429406081 := by
  unfold tailWord_6777450
  simp only [CollatzResearch.WordTrace]
  refine ⟨61798477324115905288030451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164795939530975747434747869 61798477324115905288030451)
  ·
    refine ⟨92697715986173857932045677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61798477324115905288030451 92697715986173857932045677)
    ·
      refine ⟨34761643494815196724517129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92697715986173857932045677 34761643494815196724517129)
      ·
        refine ⟨26071232621111397543387847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34761643494815196724517129 26071232621111397543387847)
        ·
          refine ⟨39106848931667096315081771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26071232621111397543387847 39106848931667096315081771)
          ·
            refine ⟨58660273397500644472622657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39106848931667096315081771 58660273397500644472622657)
            ·
              refine ⟨43995205048125483354466993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58660273397500644472622657 43995205048125483354466993)
              ·
                refine ⟨32996403786094112515850245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43995205048125483354466993 32996403786094112515850245)
                ·
                  refine ⟨6186825709892646096721921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32996403786094112515850245 6186825709892646096721921)
                  ·
                    refine ⟨4640119282419484572541441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6186825709892646096721921 4640119282419484572541441)
                    ·
                      refine ⟨3480089461814613429406081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640119282419484572541441 3480089461814613429406081)
                      ·
                        rfl

theorem cell23_6777450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_6777450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777450 prefixEnd_6777450 := by exact prefixLift 6777450
  have htrace : WordTrace (prefixWord ++ tailWord_6777450) baseStart_6777450 baseEnd_6777450 := by
    simpa [prefixWord, tailWord_6777450, baseEnd_6777450] using wordTrace_append hprefix tailTrace_6777450
  have hstable : (prefixWord ++ tailWord_6777450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777450).length < 2 ^ (prefixWord ++ tailWord_6777450).sum := by decide
  have hdescent : baseEnd_6777450 < baseStart_6777450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777454 : List Nat := [4, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_6777454 : Nat := 118140960795 + 6777454 * 2 ^ 59
def prefixEnd_6777454 : Nat := 4983230072969 + 3 ^ 40 * 6777454 * 2
def baseEnd_6777454 : Nat := 3480091515737231413756063

theorem tailTrace_6777454 : CollatzResearch.WordTrace tailWord_6777454 prefixEnd_6777454 3480091515737231413756063 := by
  unfold tailWord_6777454
  simp only [CollatzResearch.WordTrace]
  refine ⟨30899256898556141229408427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164796036792299419890178277 30899256898556141229408427)
  ·
    refine ⟨46348885347834211844112641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30899256898556141229408427 46348885347834211844112641)
    ·
      refine ⟨34761664010875658883084481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46348885347834211844112641 34761664010875658883084481)
      ·
        refine ⟨26071248008156744162313361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34761664010875658883084481 26071248008156744162313361)
        ·
          refine ⟨19553436006117558121735021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26071248008156744162313361 19553436006117558121735021)
          ·
            refine ⟨7332538502294084295650633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19553436006117558121735021 7332538502294084295650633)
            ·
              refine ⟨5499403876720563221737975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7332538502294084295650633 5499403876720563221737975)
              ·
                refine ⟨8249105815080844832606963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5499403876720563221737975 8249105815080844832606963)
                ·
                  refine ⟨12373658722621267248910445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8249105815080844832606963 12373658722621267248910445)
                  ·
                    refine ⟨4640122020982975218341417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12373658722621267248910445 4640122020982975218341417)
                    ·
                      refine ⟨3480091515737231413756063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640122020982975218341417 3480091515737231413756063)
                      ·
                        rfl

theorem cell23_6777454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_6777454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777454 prefixEnd_6777454 := by exact prefixLift 6777454
  have htrace : WordTrace (prefixWord ++ tailWord_6777454) baseStart_6777454 baseEnd_6777454 := by
    simpa [prefixWord, tailWord_6777454, baseEnd_6777454] using wordTrace_append hprefix tailTrace_6777454
  have hstable : (prefixWord ++ tailWord_6777454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777454).length < 2 ^ (prefixWord ++ tailWord_6777454).sum := by decide
  have hdescent : baseEnd_6777454 < baseStart_6777454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777473 : List Nat := [1, 2, 4, 2, 1, 1, 1, 6, 5]
def baseStart_6777473 : Nat := 118140960795 + 6777473 * 2 ^ 59
def prefixEnd_6777473 : Nat := 4983230072969 + 3 ^ 40 * 6777473 * 2
def baseEnd_6777473 : Nat := 386677919096629648824275

theorem tailTrace_6777473 : CollatzResearch.WordTrace tailWord_6777473 prefixEnd_6777473 386677919096629648824275 := by
  unfold tailWord_6777473
  simp only [CollatzResearch.WordTrace]
  refine ⟨247194748175380296080209073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164796498783586864053472715 247194748175380296080209073)
  ·
    refine ⟨185396061131535222060156805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247194748175380296080209073 185396061131535222060156805)
    ·
      refine ⟨34761761462162854136279401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185396061131535222060156805 34761761462162854136279401)
      ·
        refine ⟨26071321096622140602209551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34761761462162854136279401 26071321096622140602209551)
        ·
          refine ⟨39106981644933210903314327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26071321096622140602209551 39106981644933210903314327)
          ·
            refine ⟨58660472467399816354971491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39106981644933210903314327 58660472467399816354971491)
            ·
              refine ⟨87990708701099724532457237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58660472467399816354971491 87990708701099724532457237)
              ·
                refine ⟨4124564470364049587458933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87990708701099724532457237 4124564470364049587458933)
                ·
                  refine ⟨386677919096629648824275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4124564470364049587458933 386677919096629648824275)
                  ·
                    rfl

theorem cell23_6777473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 5].length) (baseStart_6777473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777473 prefixEnd_6777473 := by exact prefixLift 6777473
  have htrace : WordTrace (prefixWord ++ tailWord_6777473) baseStart_6777473 baseEnd_6777473 := by
    simpa [prefixWord, tailWord_6777473, baseEnd_6777473] using wordTrace_append hprefix tailTrace_6777473
  have hstable : (prefixWord ++ tailWord_6777473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777473).length < 2 ^ (prefixWord ++ tailWord_6777473).sum := by decide
  have hdescent : baseEnd_6777473 < baseStart_6777473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777486 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_6777486 : Nat := 118140960795 + 6777486 * 2 ^ 59
def prefixEnd_6777486 : Nat := 4983230072969 + 3 ^ 40 * 6777486 * 2
def baseEnd_6777486 : Nat := 1160035982372725096185305

theorem tailTrace_6777486 : CollatzResearch.WordTrace tailWord_6777486 prefixEnd_6777486 1160035982372725096185305 := by
  unfold tailWord_6777486
  simp only [CollatzResearch.WordTrace]
  refine ⟨30899402790541649912554039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164796814882888799533621541 30899402790541649912554039)
  ·
    refine ⟨46349104185812474868831059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30899402790541649912554039 46349104185812474868831059)
    ·
      refine ⟨69523656278718712303246589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46349104185812474868831059 69523656278718712303246589)
      ·
        refine ⟨26071371104519517113717471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69523656278718712303246589 26071371104519517113717471)
        ·
          refine ⟨39107056656779275670576207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26071371104519517113717471 39107056656779275670576207)
          ·
            refine ⟨58660584985168913505864311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39107056656779275670576207 58660584985168913505864311)
            ·
              refine ⟨87990877477753370258796467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58660584985168913505864311 87990877477753370258796467)
              ·
                refine ⟨131986316216630055388194701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87990877477753370258796467 131986316216630055388194701)
                ·
                  refine ⟨49494868581236270770573013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131986316216630055388194701 49494868581236270770573013)
                  ·
                    refine ⟨1160035982372725096185305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49494868581236270770573013 1160035982372725096185305)
                    ·
                      rfl

theorem cell23_6777486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_6777486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777486 prefixEnd_6777486 := by exact prefixLift 6777486
  have htrace : WordTrace (prefixWord ++ tailWord_6777486) baseStart_6777486 baseEnd_6777486 := by
    simpa [prefixWord, tailWord_6777486, baseEnd_6777486] using wordTrace_append hprefix tailTrace_6777486
  have hstable : (prefixWord ++ tailWord_6777486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777486).length < 2 ^ (prefixWord ++ tailWord_6777486).sum := by decide
  have hdescent : baseEnd_6777486 < baseStart_6777486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777523 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 4]
def baseStart_6777523 : Nat := 118140960795 + 6777523 * 2 ^ 59
def prefixEnd_6777523 : Nat := 4983230072969 + 3 ^ 40 * 6777523 * 2
def baseEnd_6777523 : Nat := 3480126945902391643793245

theorem tailTrace_6777523 : CollatzResearch.WordTrace tailWord_6777523 prefixEnd_6777523 3480126945902391643793245 := by
  unfold tailWord_6777523
  simp only [CollatzResearch.WordTrace]
  refine ⟨247196571825199154619529223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164797714550132769746352815 247196571825199154619529223)
  ·
    refine ⟨370794857737798731929293835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247196571825199154619529223 370794857737798731929293835)
    ·
      refine ⟨556192286606698097893940753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370794857737798731929293835 556192286606698097893940753)
      ·
        refine ⟨417144214955023573420455565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556192286606698097893940753 417144214955023573420455565)
        ·
          refine ⟨156429080608133840032670837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 417144214955023573420455565 156429080608133840032670837)
          ·
            refine ⟨14665226307012547503062891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156429080608133840032670837 14665226307012547503062891)
            ·
              refine ⟨21997839460518821254594337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14665226307012547503062891 21997839460518821254594337)
              ·
                refine ⟨16498379595389115940945753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21997839460518821254594337 16498379595389115940945753)
                ·
                  refine ⟨12373784696541836955709315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16498379595389115940945753 12373784696541836955709315)
                  ·
                    refine ⟨18560677044812755433563973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12373784696541836955709315 18560677044812755433563973)
                    ·
                      refine ⟨3480126945902391643793245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18560677044812755433563973 3480126945902391643793245)
                      ·
                        rfl

theorem cell23_6777523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_6777523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777523 prefixEnd_6777523 := by exact prefixLift 6777523
  have htrace : WordTrace (prefixWord ++ tailWord_6777523) baseStart_6777523 baseEnd_6777523 := by
    simpa [prefixWord, tailWord_6777523, baseEnd_6777523] using wordTrace_append hprefix tailTrace_6777523
  have hstable : (prefixWord ++ tailWord_6777523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777523).length < 2 ^ (prefixWord ++ tailWord_6777523).sum := by decide
  have hdescent : baseEnd_6777523 < baseStart_6777523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777557 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6777557 : Nat := 118140960795 + 6777557 * 2 ^ 59
def prefixEnd_6777557 : Nat := 4983230072969 + 3 ^ 40 * 6777557 * 2
def baseEnd_6777557 : Nat := 3480144404244644510768089

theorem tailTrace_6777557 : CollatzResearch.WordTrace tailWord_6777557 prefixEnd_6777557 3480144404244644510768089 := by
  unfold tailWord_6777557
  simp only [CollatzResearch.WordTrace]
  refine ⟨247197811907075978426266925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164798541271383985617511283 247197811907075978426266925)
  ·
    refine ⟨92699179465153491909850097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247197811907075978426266925 92699179465153491909850097)
    ·
      refine ⟨69524384598865118932387573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92699179465153491909850097 69524384598865118932387573)
      ·
        refine ⟨6517911056143604899911335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69524384598865118932387573 6517911056143604899911335)
        ·
          refine ⟨9776866584215407349867003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6517911056143604899911335 9776866584215407349867003)
          ·
            refine ⟨14665299876323111024800505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9776866584215407349867003 14665299876323111024800505)
            ·
              refine ⟨10998974907242333268600379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14665299876323111024800505 10998974907242333268600379)
              ·
                refine ⟨16498462360863499902900569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10998974907242333268600379 16498462360863499902900569)
                ·
                  refine ⟨12373846770647624927175427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16498462360863499902900569 12373846770647624927175427)
                  ·
                    refine ⟨18560770155971437390763141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12373846770647624927175427 18560770155971437390763141)
                    ·
                      refine ⟨3480144404244644510768089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18560770155971437390763141 3480144404244644510768089)
                      ·
                        rfl

theorem cell23_6777557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6777557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777557 prefixEnd_6777557 := by exact prefixLift 6777557
  have htrace : WordTrace (prefixWord ++ tailWord_6777557) baseStart_6777557 baseEnd_6777557 := by
    simpa [prefixWord, tailWord_6777557, baseEnd_6777557] using wordTrace_append hprefix tailTrace_6777557
  have hstable : (prefixWord ++ tailWord_6777557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777557).length < 2 ^ (prefixWord ++ tailWord_6777557).sum := by decide
  have hdescent : baseEnd_6777557 < baseStart_6777557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777560 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 2, 2, 3]
def baseStart_6777560 : Nat := 118140960795 + 6777560 * 2 ^ 59
def prefixEnd_6777560 : Nat := 4983230072969 + 3 ^ 40 * 6777560 * 2
def baseEnd_6777560 : Nat := 3480145944686607999030575

theorem tailTrace_6777560 : CollatzResearch.WordTrace tailWord_6777560 prefixEnd_6777560 3480145944686607999030575 := by
  unfold tailWord_6777560
  simp only [CollatzResearch.WordTrace]
  refine ⟨123598960663032554969313067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164798614217376739959084089 123598960663032554969313067)
  ·
    refine ⟨185398440994548832453969601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123598960663032554969313067 185398440994548832453969601)
    ·
      refine ⟨139048830745911624340477201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185398440994548832453969601 139048830745911624340477201)
      ·
        refine ⟨104286623059433718255357901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139048830745911624340477201 104286623059433718255357901)
        ·
          refine ⟨39107483647287644345759213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104286623059433718255357901 39107483647287644345759213)
          ·
            refine ⟨14665306367732866629659705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39107483647287644345759213 14665306367732866629659705)
            ·
              refine ⟨10998979775799649972244779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14665306367732866629659705 10998979775799649972244779)
              ·
                refine ⟨16498469663699474958367169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10998979775799649972244779 16498469663699474958367169)
                ·
                  refine ⟨12373852247774606218775377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16498469663699474958367169 12373852247774606218775377)
                  ·
                    refine ⟨9280389185830954664081533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12373852247774606218775377 9280389185830954664081533)
                    ·
                      refine ⟨3480145944686607999030575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9280389185830954664081533 3480145944686607999030575)
                      ·
                        rfl

theorem cell23_6777560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_6777560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777560 prefixEnd_6777560 := by exact prefixLift 6777560
  have htrace : WordTrace (prefixWord ++ tailWord_6777560) baseStart_6777560 baseEnd_6777560 := by
    simpa [prefixWord, tailWord_6777560, baseEnd_6777560] using wordTrace_append hprefix tailTrace_6777560
  have hstable : (prefixWord ++ tailWord_6777560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777560).length < 2 ^ (prefixWord ++ tailWord_6777560).sum := by decide
  have hdescent : baseEnd_6777560 < baseStart_6777560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777607 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_6777607 : Nat := 118140960795 + 6777607 * 2 ^ 59
def prefixEnd_6777607 : Nat := 4983230072969 + 3 ^ 40 * 6777607 * 2
def baseEnd_6777607 : Nat := 3480170078277369315142859

theorem tailTrace_6777607 : CollatzResearch.WordTrace tailWord_6777607 prefixEnd_6777607 3480170078277369315142859 := by
  unfold tailWord_6777607
  simp only [CollatzResearch.WordTrace]
  refine ⟨247199635556894836965587075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164799757037929891310391383 247199635556894836965587075)
  ·
    refine ⟨370799453335342255448380613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247199635556894836965587075 370799453335342255448380613)
    ·
      refine ⟨69524897500376672896571365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370799453335342255448380613 69524897500376672896571365)
      ·
        refine ⟨13035918281320626168107131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69524897500376672896571365 13035918281320626168107131)
        ·
          refine ⟨19553877421980939252160697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13035918281320626168107131 19553877421980939252160697)
          ·
            refine ⟨14665408066485704439120523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19553877421980939252160697 14665408066485704439120523)
            ·
              refine ⟨21998112099728556658680785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14665408066485704439120523 21998112099728556658680785)
              ·
                refine ⟨16498584074796417494010589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21998112099728556658680785 16498584074796417494010589)
                ·
                  refine ⟨6186969028048656560253971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16498584074796417494010589 6186969028048656560253971)
                  ·
                    refine ⟨9280453542072984840380957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6186969028048656560253971 9280453542072984840380957)
                    ·
                      refine ⟨3480170078277369315142859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9280453542072984840380957 3480170078277369315142859)
                      ·
                        rfl

theorem cell23_6777607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_6777607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777607 prefixEnd_6777607 := by exact prefixLift 6777607
  have htrace : WordTrace (prefixWord ++ tailWord_6777607) baseStart_6777607 baseEnd_6777607 := by
    simpa [prefixWord, tailWord_6777607, baseEnd_6777607] using wordTrace_append hprefix tailTrace_6777607
  have hstable : (prefixWord ++ tailWord_6777607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777607).length < 2 ^ (prefixWord ++ tailWord_6777607).sum := by decide
  have hdescent : baseEnd_6777607 < baseStart_6777607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777633 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6777633 : Nat := 118140960795 + 6777633 * 2 ^ 59
def prefixEnd_6777633 : Nat := 4983230072969 + 3 ^ 40 * 6777633 * 2
def baseEnd_6777633 : Nat := 3480183428774386213417739

theorem tailTrace_6777633 : CollatzResearch.WordTrace tailWord_6777633 prefixEnd_6777633 3480183428774386213417739 := by
  unfold tailWord_6777633
  simp only [CollatzResearch.WordTrace]
  refine ⟨247200583854800643406033553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164800389236533762270689035 247200583854800643406033553)
  ·
    refine ⟨185400437891100482554525165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247200583854800643406033553 185400437891100482554525165)
    ·
      refine ⟨69525164209162680957946937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185400437891100482554525165 69525164209162680957946937)
      ·
        refine ⟨52143873156872010718460203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69525164209162680957946937 52143873156872010718460203)
        ·
          refine ⟨78215809735308016077690305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52143873156872010718460203 78215809735308016077690305)
          ·
            refine ⟨58661857301481012058267729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78215809735308016077690305 58661857301481012058267729)
            ·
              refine ⟨43996392976110759043700797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58661857301481012058267729 43996392976110759043700797)
              ·
                refine ⟨16498647366041534641387799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43996392976110759043700797 16498647366041534641387799)
                ·
                  refine ⟨24747971049062301962081699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16498647366041534641387799 24747971049062301962081699)
                  ·
                    refine ⟨37121956573593452943122549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24747971049062301962081699 37121956573593452943122549)
                    ·
                      refine ⟨3480183428774386213417739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37121956573593452943122549 3480183428774386213417739)
                      ·
                        rfl

theorem cell23_6777633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6777633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777633 prefixEnd_6777633 := by exact prefixLift 6777633
  have htrace : WordTrace (prefixWord ++ tailWord_6777633) baseStart_6777633 baseEnd_6777633 := by
    simpa [prefixWord, tailWord_6777633, baseEnd_6777633] using wordTrace_append hprefix tailTrace_6777633
  have hstable : (prefixWord ++ tailWord_6777633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777633).length < 2 ^ (prefixWord ++ tailWord_6777633).sum := by decide
  have hdescent : baseEnd_6777633 < baseStart_6777633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777640 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 4, 4]
def baseStart_6777640 : Nat := 118140960795 + 6777640 * 2 ^ 59
def prefixEnd_6777640 : Nat := 4983230072969 + 3 ^ 40 * 6777640 * 2
def baseEnd_6777640 : Nat := 1160062341046322562010069

theorem tailTrace_6777640 : CollatzResearch.WordTrace tailWord_6777640 prefixEnd_6777640 1160062341046322562010069 := by
  unfold tailWord_6777640
  simp only [CollatzResearch.WordTrace]
  refine ⟨123600419582887641800769187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164800559443850189067692249 123600419582887641800769187)
  ·
    refine ⟨185400629374331462701153781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123600419582887641800769187 185400629374331462701153781)
    ·
      refine ⟨17381309003843574628233167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185400629374331462701153781 17381309003843574628233167)
      ·
        refine ⟨26071963505765361942349751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17381309003843574628233167 26071963505765361942349751)
        ·
          refine ⟨39107945258648042913524627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26071963505765361942349751 39107945258648042913524627)
          ·
            refine ⟨58661917887972064370286941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39107945258648042913524627 58661917887972064370286941)
            ·
              refine ⟨21998219207989524138857603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58661917887972064370286941 21998219207989524138857603)
              ·
                refine ⟨32997328811984286208286405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21998219207989524138857603 32997328811984286208286405)
                ·
                  refine ⟨6186999152247053664053701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32997328811984286208286405 6186999152247053664053701)
                  ·
                    refine ⟨1160062341046322562010069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6186999152247053664053701 1160062341046322562010069)
                    ·
                      rfl

theorem cell23_6777640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_6777640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777640 prefixEnd_6777640 := by exact prefixLift 6777640
  have htrace : WordTrace (prefixWord ++ tailWord_6777640) baseStart_6777640 baseEnd_6777640 := by
    simpa [prefixWord, tailWord_6777640, baseEnd_6777640] using wordTrace_append hprefix tailTrace_6777640
  have hstable : (prefixWord ++ tailWord_6777640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777640).length < 2 ^ (prefixWord ++ tailWord_6777640).sum := by decide
  have hdescent : baseEnd_6777640 < baseStart_6777640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777680 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 4, 1, 3]
def baseStart_6777680 : Nat := 118140960795 + 6777680 * 2 ^ 59
def prefixEnd_6777680 : Nat := 4983230072969 + 3 ^ 40 * 6777680 * 2
def baseEnd_6777680 : Nat := 3480207562365147529530023

theorem tailTrace_6777680 : CollatzResearch.WordTrace tailWord_6777680 prefixEnd_6777680 3480207562365147529530023 := by
  unfold tailWord_6777680
  simp only [CollatzResearch.WordTrace]
  refine ⟨123601149042815185216497247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164801532057086913621996329 123601149042815185216497247)
  ·
    refine ⟨185401723564222777824745871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123601149042815185216497247 185401723564222777824745871)
    ·
      refine ⟨278102585346334166737118807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185401723564222777824745871 278102585346334166737118807)
      ·
        refine ⟨417153878019501250105678211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278102585346334166737118807 417153878019501250105678211)
        ·
          refine ⟨625730817029251875158517317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417153878019501250105678211 625730817029251875158517317)
          ·
            refine ⟨117324528192984726592221997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 625730817029251875158517317 117324528192984726592221997)
            ·
              refine ⟨43996698072369272472083249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117324528192984726592221997 43996698072369272472083249)
              ·
                refine ⟨32997523554276954354062437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43996698072369272472083249 32997523554276954354062437)
                ·
                  refine ⟨6187035666426928941386707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32997523554276954354062437 6187035666426928941386707)
                  ·
                    refine ⟨9280553499640393412080061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6187035666426928941386707 9280553499640393412080061)
                    ·
                      refine ⟨3480207562365147529530023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9280553499640393412080061 3480207562365147529530023)
                      ·
                        rfl

theorem cell23_6777680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 4, 1, 3].length) (baseStart_6777680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777680 prefixEnd_6777680 := by exact prefixLift 6777680
  have htrace : WordTrace (prefixWord ++ tailWord_6777680) baseStart_6777680 baseEnd_6777680 := by
    simpa [prefixWord, tailWord_6777680, baseEnd_6777680] using wordTrace_append hprefix tailTrace_6777680
  have hstable : (prefixWord ++ tailWord_6777680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777680).length < 2 ^ (prefixWord ++ tailWord_6777680).sum := by decide
  have hdescent : baseEnd_6777680 < baseStart_6777680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777698 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_6777698 : Nat := 118140960795 + 6777698 * 2 ^ 59
def prefixEnd_6777698 : Nat := 4983230072969 + 3 ^ 40 * 6777698 * 2
def baseEnd_6777698 : Nat := 3480216805016928459104941

theorem tailTrace_6777698 : CollatzResearch.WordTrace tailWord_6777698 prefixEnd_6777698 3480216805016928459104941 := by
  unfold tailWord_6777698
  simp only [CollatzResearch.WordTrace]
  refine ⟨61800738649891289876787437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164801969733043439671433165 61800738649891289876787437)
  ·
    refine ⟨23175276993709233703795289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61800738649891289876787437 23175276993709233703795289)
    ·
      refine ⟨17381457745281925277846467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23175276993709233703795289 17381457745281925277846467)
      ·
        refine ⟨26072186617922887916769701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17381457745281925277846467 26072186617922887916769701)
        ·
          refine ⟨4888534990860541484394319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26072186617922887916769701 4888534990860541484394319)
          ·
            refine ⟨7332802486290812226591479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4888534990860541484394319 7332802486290812226591479)
            ·
              refine ⟨10999203729436218339887219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7332802486290812226591479 10999203729436218339887219)
              ·
                refine ⟨16498805594154327509830829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10999203729436218339887219 16498805594154327509830829)
                ·
                  refine ⟨6187052097807872816186561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16498805594154327509830829 6187052097807872816186561)
                  ·
                    refine ⟨4640289073355904612139921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6187052097807872816186561 4640289073355904612139921)
                    ·
                      refine ⟨3480216805016928459104941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640289073355904612139921 3480216805016928459104941)
                      ·
                        rfl

theorem cell23_6777698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_6777698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777698 prefixEnd_6777698 := by exact prefixLift 6777698
  have htrace : WordTrace (prefixWord ++ tailWord_6777698) baseStart_6777698 baseEnd_6777698 := by
    simpa [prefixWord, tailWord_6777698, baseEnd_6777698] using wordTrace_append hprefix tailTrace_6777698
  have hstable : (prefixWord ++ tailWord_6777698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777698).length < 2 ^ (prefixWord ++ tailWord_6777698).sum := by decide
  have hdescent : baseEnd_6777698 < baseStart_6777698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777714 : List Nat := [3, 2, 1, 2, 1, 1, 6, 1, 2, 1, 3]
def baseStart_6777714 : Nat := 118140960795 + 6777714 * 2 ^ 59
def prefixEnd_6777714 : Nat := 4983230072969 + 3 ^ 40 * 6777714 * 2
def baseEnd_6777714 : Nat := 3480225020707400396504867

theorem tailTrace_6777714 : CollatzResearch.WordTrace tailWord_6777714 prefixEnd_6777714 3480225020707400396504867 := by
  unfold tailWord_6777714
  simp only [CollatzResearch.WordTrace]
  refine ⟨61800884541876798559933049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164802358778338129493154797 61800884541876798559933049)
  ·
    refine ⟨46350663406407598919949787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61800884541876798559933049 46350663406407598919949787)
    ·
      refine ⟨69525995109611398379924681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46350663406407598919949787 69525995109611398379924681)
      ·
        refine ⟨52144496332208548784943511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69525995109611398379924681 52144496332208548784943511)
        ·
          refine ⟨78216744498312823177415267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52144496332208548784943511 78216744498312823177415267)
          ·
            refine ⟨117325116747469234766122901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78216744498312823177415267 117325116747469234766122901)
            ·
              refine ⟨5499614847537620379662011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117325116747469234766122901 5499614847537620379662011)
              ·
                refine ⟨8249422271306430569493017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5499614847537620379662011 8249422271306430569493017)
                ·
                  refine ⟨6187066703479822927119763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8249422271306430569493017 6187066703479822927119763)
                  ·
                    refine ⟨9280600055219734390679645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6187066703479822927119763 9280600055219734390679645)
                    ·
                      refine ⟨3480225020707400396504867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9280600055219734390679645 3480225020707400396504867)
                      ·
                        rfl

theorem cell23_6777714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_6777714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777714 prefixEnd_6777714 := by exact prefixLift 6777714
  have htrace : WordTrace (prefixWord ++ tailWord_6777714) baseStart_6777714 baseEnd_6777714 := by
    simpa [prefixWord, tailWord_6777714, baseEnd_6777714] using wordTrace_append hprefix tailTrace_6777714
  have hstable : (prefixWord ++ tailWord_6777714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777714).length < 2 ^ (prefixWord ++ tailWord_6777714).sum := by decide
  have hdescent : baseEnd_6777714 < baseStart_6777714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777723 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 5]
def baseStart_6777723 : Nat := 118140960795 + 6777723 * 2 ^ 59
def prefixEnd_6777723 : Nat := 4983230072969 + 3 ^ 40 * 6777723 * 2
def baseEnd_6777723 : Nat := 3480229642033290861292325

theorem tailTrace_6777723 : CollatzResearch.WordTrace tailWord_6777723 prefixEnd_6777723 3480229642033290861292325 := by
  unfold tailWord_6777723
  simp only [CollatzResearch.WordTrace]
  refine ⟨247203866424474588776809823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164802577616316392517873215 247203866424474588776809823)
  ·
    refine ⟨370805799636711883165214735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247203866424474588776809823 370805799636711883165214735)
    ·
      refine ⟨556208699455067824747822103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370805799636711883165214735 556208699455067824747822103)
      ·
        refine ⟨834313049182601737121733155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556208699455067824747822103 834313049182601737121733155)
        ·
          refine ⟨1251469573773902605682599733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834313049182601737121733155 1251469573773902605682599733)
          ·
            refine ⟨117325272541303369282743725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1251469573773902605682599733 117325272541303369282743725)
            ·
              refine ⟨43996977202988763481028897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117325272541303369282743725 43996977202988763481028897)
              ·
                refine ⟨32997732902241572610771673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43996977202988763481028897 32997732902241572610771673)
                ·
                  refine ⟨24748299676681179458078755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32997732902241572610771673 24748299676681179458078755)
                  ·
                    refine ⟨37122449515021769187118133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24748299676681179458078755 37122449515021769187118133)
                    ·
                      refine ⟨3480229642033290861292325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37122449515021769187118133 3480229642033290861292325)
                      ·
                        rfl

theorem cell23_6777723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 5].length) (baseStart_6777723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777723 prefixEnd_6777723 := by exact prefixLift 6777723
  have htrace : WordTrace (prefixWord ++ tailWord_6777723) baseStart_6777723 baseEnd_6777723 := by
    simpa [prefixWord, tailWord_6777723, baseEnd_6777723] using wordTrace_append hprefix tailTrace_6777723
  have hstable : (prefixWord ++ tailWord_6777723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777723).length < 2 ^ (prefixWord ++ tailWord_6777723).sum := by decide
  have hdescent : baseEnd_6777723 < baseStart_6777723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777737 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 1, 4, 2]
def baseStart_6777737 : Nat := 118140960795 + 6777737 * 2 ^ 59
def prefixEnd_6777737 : Nat := 4983230072969 + 3 ^ 40 * 6777737 * 2
def baseEnd_6777737 : Nat := 3480236830762453806517261

theorem tailTrace_6777737 : CollatzResearch.WordTrace tailWord_6777737 prefixEnd_6777737 3480236830762453806517261 := by
  unfold tailWord_6777737
  simp only [CollatzResearch.WordTrace]
  refine ⟨247204377046423869167819465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164802918030949246111879643 247204377046423869167819465)
  ·
    refine ⟨185403282784817901875864599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247204377046423869167819465 185403282784817901875864599)
    ·
      refine ⟨278104924177226852813796899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185403282784817901875864599 278104924177226852813796899)
      ·
        refine ⟨417157386265840279220695349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278104924177226852813796899 417157386265840279220695349)
        ·
          refine ⟨39108504962422526176940189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 417157386265840279220695349 39108504962422526176940189)
          ·
            refine ⟨14665689360908447316352571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39108504962422526176940189 14665689360908447316352571)
            ·
              refine ⟨21998534041362670974528857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14665689360908447316352571 21998534041362670974528857)
              ·
                refine ⟨16498900531022003230896643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21998534041362670974528857 16498900531022003230896643)
                ·
                  refine ⟨24748350796533004846344965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16498900531022003230896643 24748350796533004846344965)
                  ·
                    refine ⟨4640315774349938408689681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24748350796533004846344965 4640315774349938408689681)
                    ·
                      refine ⟨3480236830762453806517261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640315774349938408689681 3480236830762453806517261)
                      ·
                        rfl

theorem cell23_6777737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 4, 2].length) (baseStart_6777737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777737 prefixEnd_6777737 := by exact prefixLift 6777737
  have htrace : WordTrace (prefixWord ++ tailWord_6777737) baseStart_6777737 baseEnd_6777737 := by
    simpa [prefixWord, tailWord_6777737, baseEnd_6777737] using wordTrace_append hprefix tailTrace_6777737
  have hstable : (prefixWord ++ tailWord_6777737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777737).length < 2 ^ (prefixWord ++ tailWord_6777737).sum := by decide
  have hdescent : baseEnd_6777737 < baseStart_6777737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777767 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_6777767 : Nat := 118140960795 + 6777767 * 2 ^ 59
def prefixEnd_6777767 : Nat := 4983230072969 + 3 ^ 40 * 6777767 * 2
def baseEnd_6777767 : Nat := 3480252235182088689142123

theorem tailTrace_6777767 : CollatzResearch.WordTrace tailWord_6777767 prefixEnd_6777767 3480252235182088689142123 := by
  unfold tailWord_6777767
  simp only [CollatzResearch.WordTrace]
  refine ⟨247205471236315184291411555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164803647490876789527607703 247205471236315184291411555)
  ·
    refine ⟨370808206854472776437117333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247205471236315184291411555 370808206854472776437117333)
    ·
      refine ⟨17381634696303411395489875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 370808206854472776437117333 17381634696303411395489875)
      ·
        refine ⟨26072452044455117093234813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17381634696303411395489875 26072452044455117093234813)
        ·
          refine ⟨9777169516670668909963055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26072452044455117093234813 9777169516670668909963055)
          ·
            refine ⟨14665754275006003364944583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9777169516670668909963055 14665754275006003364944583)
            ·
              refine ⟨21998631412509005047416875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14665754275006003364944583 21998631412509005047416875)
              ·
                refine ⟨32997947118763507571125313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21998631412509005047416875 32997947118763507571125313)
                ·
                  refine ⟨24748460339072630678343985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32997947118763507571125313 24748460339072630678343985)
                  ·
                    refine ⟨18561345254304473008757989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24748460339072630678343985 18561345254304473008757989)
                    ·
                      refine ⟨3480252235182088689142123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18561345254304473008757989 3480252235182088689142123)
                      ·
                        rfl

theorem cell23_6777767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_6777767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777767 prefixEnd_6777767 := by exact prefixLift 6777767
  have htrace : WordTrace (prefixWord ++ tailWord_6777767) baseStart_6777767 baseEnd_6777767 := by
    simpa [prefixWord, tailWord_6777767, baseEnd_6777767] using wordTrace_append hprefix tailTrace_6777767
  have hstable : (prefixWord ++ tailWord_6777767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777767).length < 2 ^ (prefixWord ++ tailWord_6777767).sum := by decide
  have hdescent : baseEnd_6777767 < baseStart_6777767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777783 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_6777783 : Nat := 118140960795 + 6777783 * 2 ^ 59
def prefixEnd_6777783 : Nat := 4983230072969 + 3 ^ 40 * 6777783 * 2
def baseEnd_6777783 : Nat := 3480260450872560626542049

theorem tailTrace_6777783 : CollatzResearch.WordTrace tailWord_6777783 prefixEnd_6777783 3480260450872560626542049 := by
  unfold tailWord_6777783
  simp only [CollatzResearch.WordTrace]
  refine ⟨247206054804257219023994003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164804036536171479349329335 247206054804257219023994003)
  ·
    refine ⟨370809082206385828535991005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247206054804257219023994003 370809082206385828535991005)
    ·
      refine ⟨139053405827394685700996627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370809082206385828535991005 139053405827394685700996627)
      ·
        refine ⟨208580108741092028551494941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139053405827394685700996627 208580108741092028551494941)
        ·
          refine ⟨78217540777909510706810603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208580108741092028551494941 78217540777909510706810603)
          ·
            refine ⟨117326311166864266060215905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78217540777909510706810603 117326311166864266060215905)
            ·
              refine ⟨87994733375148199545161929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117326311166864266060215905 87994733375148199545161929)
              ·
                refine ⟨65996050031361149658871447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87994733375148199545161929 65996050031361149658871447)
                ·
                  refine ⟨98994075047041724488307171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65996050031361149658871447 98994075047041724488307171)
                  ·
                    refine ⟨148491112570562586732460757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98994075047041724488307171 148491112570562586732460757)
                    ·
                      refine ⟨3480260450872560626542049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148491112570562586732460757 3480260450872560626542049)
                      ·
                        rfl

theorem cell23_6777783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_6777783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777783 prefixEnd_6777783 := by exact prefixLift 6777783
  have htrace : WordTrace (prefixWord ++ tailWord_6777783) baseStart_6777783 baseEnd_6777783 := by
    simpa [prefixWord, tailWord_6777783, baseEnd_6777783] using wordTrace_append hprefix tailTrace_6777783
  have hstable : (prefixWord ++ tailWord_6777783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777783).length < 2 ^ (prefixWord ++ tailWord_6777783).sum := by decide
  have hdescent : baseEnd_6777783 < baseStart_6777783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777790 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_6777790 : Nat := 118140960795 + 6777790 * 2 ^ 59
def prefixEnd_6777790 : Nat := 4983230072969 + 3 ^ 40 * 6777790 * 2
def baseEnd_6777790 : Nat := 1160088015079047366384839

theorem tailTrace_6777790 : CollatzResearch.WordTrace tailWord_6777790 prefixEnd_6777790 1160088015079047366384839 := by
  unfold tailWord_6777790
  simp only [CollatzResearch.WordTrace]
  refine ⟨30900788764403982402437353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164804206743487906146332549 30900788764403982402437353)
  ·
    refine ⟨23175591573302986801828015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30900788764403982402437353 23175591573302986801828015)
    ·
      refine ⟨34763387359954480202742023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23175591573302986801828015 34763387359954480202742023)
      ·
        refine ⟨52145081039931720304113035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34763387359954480202742023 52145081039931720304113035)
        ·
          refine ⟨78217621559897580456169553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52145081039931720304113035 78217621559897580456169553)
          ·
            refine ⟨58663216169923185342127165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78217621559897580456169553 58663216169923185342127165)
            ·
              refine ⟨21998706063721194503297687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58663216169923185342127165 21998706063721194503297687)
              ·
                refine ⟨32998059095581791754946531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21998706063721194503297687 32998059095581791754946531)
                ·
                  refine ⟨49497088643372687632419797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32998059095581791754946531 49497088643372687632419797)
                  ·
                    refine ⟨1160088015079047366384839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49497088643372687632419797 1160088015079047366384839)
                    ·
                      rfl

theorem cell23_6777790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_6777790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777790 prefixEnd_6777790 := by exact prefixLift 6777790
  have htrace : WordTrace (prefixWord ++ tailWord_6777790) baseStart_6777790 baseEnd_6777790 := by
    simpa [prefixWord, tailWord_6777790, baseEnd_6777790] using wordTrace_append hprefix tailTrace_6777790
  have hstable : (prefixWord ++ tailWord_6777790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777790).length < 2 ^ (prefixWord ++ tailWord_6777790).sum := by decide
  have hdescent : baseEnd_6777790 < baseStart_6777790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777805 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_6777805 : Nat := 118140960795 + 6777805 * 2 ^ 59
def prefixEnd_6777805 : Nat := 4983230072969 + 3 ^ 40 * 6777805 * 2
def baseEnd_6777805 : Nat := 3480271747446959540466949

theorem tailTrace_6777805 : CollatzResearch.WordTrace tailWord_6777805 prefixEnd_6777805 3480271747446959540466949 := by
  unfold tailWord_6777805
  simp only [CollatzResearch.WordTrace]
  refine ⟨247206857210177516781294869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164804571473451677854196579 247206857210177516781294869)
  ·
    refine ⟨11587821431727071099123197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 247206857210177516781294869 11587821431727071099123197)
    ·
      refine ⟨4345433036897651662171199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11587821431727071099123197 4345433036897651662171199)
      ·
        refine ⟨6518149555346477493256799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4345433036897651662171199 6518149555346477493256799)
        ·
          refine ⟨9777224333019716239885199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6518149555346477493256799 9777224333019716239885199)
          ·
            refine ⟨14665836499529574359827799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9777224333019716239885199 14665836499529574359827799)
            ·
              refine ⟨21998754749294361539741699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14665836499529574359827799 21998754749294361539741699)
              ·
                refine ⟨32998132123941542309612549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21998754749294361539741699 32998132123941542309612549)
                ·
                  refine ⟨6187149773239039183052353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32998132123941542309612549 6187149773239039183052353)
                  ·
                    refine ⟨4640362329929279387289265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6187149773239039183052353 4640362329929279387289265)
                    ·
                      refine ⟨3480271747446959540466949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640362329929279387289265 3480271747446959540466949)
                      ·
                        rfl

theorem cell23_6777805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_6777805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777805 prefixEnd_6777805 := by exact prefixLift 6777805
  have htrace : WordTrace (prefixWord ++ tailWord_6777805) baseStart_6777805 baseEnd_6777805 := by
    simpa [prefixWord, tailWord_6777805, baseEnd_6777805] using wordTrace_append hprefix tailTrace_6777805
  have hstable : (prefixWord ++ tailWord_6777805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777805).length < 2 ^ (prefixWord ++ tailWord_6777805).sum := by decide
  have hdescent : baseEnd_6777805 < baseStart_6777805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777827 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 2, 4, 2]
def baseStart_6777827 : Nat := 118140960795 + 6777827 * 2 ^ 59
def prefixEnd_6777827 : Nat := 4983230072969 + 3 ^ 40 * 6777827 * 2
def baseEnd_6777827 : Nat := 3480283044021358454391847

theorem tailTrace_6777827 : CollatzResearch.WordTrace tailWord_6777827 prefixEnd_6777827 3480283044021358454391847 := by
  unfold tailWord_6777827
  simp only [CollatzResearch.WordTrace]
  refine ⟨247207659616097814538595735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164805106410731876359063823 247207659616097814538595735)
  ·
    refine ⟨370811489424146721807893603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247207659616097814538595735 370811489424146721807893603)
    ·
      refine ⟨556217234136220082711840405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370811489424146721807893603 556217234136220082711840405)
      ·
        refine ⟨26072682850135316377117519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 556217234136220082711840405 26072682850135316377117519)
        ·
          refine ⟨39109024275202974565676279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26072682850135316377117519 39109024275202974565676279)
          ·
            refine ⟨58663536412804461848514419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39109024275202974565676279 58663536412804461848514419)
            ·
              refine ⟨87995304619206692772771629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58663536412804461848514419 87995304619206692772771629)
              ·
                refine ⟨32998239232202509789789361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87995304619206692772771629 32998239232202509789789361)
                ·
                  refine ⟨24748679424151882342342021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32998239232202509789789361 24748679424151882342342021)
                  ·
                    refine ⟨4640377392028477939189129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24748679424151882342342021 4640377392028477939189129)
                    ·
                      refine ⟨3480283044021358454391847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640377392028477939189129 3480283044021358454391847)
                      ·
                        rfl

theorem cell23_6777827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_6777827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777827 prefixEnd_6777827 := by exact prefixLift 6777827
  have htrace : WordTrace (prefixWord ++ tailWord_6777827) baseStart_6777827 baseEnd_6777827 := by
    simpa [prefixWord, tailWord_6777827, baseEnd_6777827] using wordTrace_append hprefix tailTrace_6777827
  have hstable : (prefixWord ++ tailWord_6777827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777827).length < 2 ^ (prefixWord ++ tailWord_6777827).sum := by decide
  have hdescent : baseEnd_6777827 < baseStart_6777827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777843 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 9]
def baseStart_6777843 : Nat := 118140960795 + 6777843 * 2 ^ 59
def prefixEnd_6777843 : Nat := 4983230072969 + 3 ^ 40 * 6777843 * 2
def baseEnd_6777843 : Nat := 3480291259711830391791773

theorem tailTrace_6777843 : CollatzResearch.WordTrace tailWord_6777843 prefixEnd_6777843 3480291259711830391791773 := by
  unfold tailWord_6777843
  simp only [CollatzResearch.WordTrace]
  refine ⟨247208243184039849271178183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164805495456026566180785455 247208243184039849271178183)
  ·
    refine ⟨370812364776059773906767275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247208243184039849271178183 370812364776059773906767275)
    ·
      refine ⟨556218547164089660860150913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370812364776059773906767275 556218547164089660860150913)
      ·
        refine ⟨417163910373067245645113185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556218547164089660860150913 417163910373067245645113185)
        ·
          refine ⟨312872932779800434233834889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417163910373067245645113185 312872932779800434233834889)
          ·
            refine ⟨234654699584850325675376167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312872932779800434233834889 234654699584850325675376167)
            ·
              refine ⟨351982049377275488513064251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234654699584850325675376167 351982049377275488513064251)
              ·
                refine ⟨527973074065913232769596377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351982049377275488513064251 527973074065913232769596377)
                ·
                  refine ⟨395979805549434924577197283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527973074065913232769596377 395979805549434924577197283)
                  ·
                    refine ⟨593969708324152386865795925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 395979805549434924577197283 593969708324152386865795925)
                    ·
                      refine ⟨3480291259711830391791773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 593969708324152386865795925 3480291259711830391791773)
                      ·
                        rfl

theorem cell23_6777843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_6777843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777843 prefixEnd_6777843 := by exact prefixLift 6777843
  have htrace : WordTrace (prefixWord ++ tailWord_6777843) baseStart_6777843 baseEnd_6777843 := by
    simpa [prefixWord, tailWord_6777843, baseEnd_6777843] using wordTrace_append hprefix tailTrace_6777843
  have hstable : (prefixWord ++ tailWord_6777843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777843).length < 2 ^ (prefixWord ++ tailWord_6777843).sum := by decide
  have hdescent : baseEnd_6777843 < baseStart_6777843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777904 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 2, 3, 2]
def baseStart_6777904 : Nat := 118140960795 + 6777904 * 2 ^ 59
def prefixEnd_6777904 : Nat := 4983230072969 + 3 ^ 40 * 6777904 * 2
def baseEnd_6777904 : Nat := 3480322582031754653128993

theorem tailTrace_6777904 : CollatzResearch.WordTrace tailWord_6777904 prefixEnd_6777904 3480322582031754653128993 := by
  unfold tailWord_6777904
  simp only [CollatzResearch.WordTrace]
  refine ⟨123605234018409428344574383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164806978691212571126099177 123605234018409428344574383)
  ·
    refine ⟨185407851027614142516861575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123605234018409428344574383 185407851027614142516861575)
    ·
      refine ⟨278111776541421213775292363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185407851027614142516861575 278111776541421213775292363)
      ·
        refine ⟨417167664812131820662938545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278111776541421213775292363 417167664812131820662938545)
        ·
          refine ⟨312875748609098865497203909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417167664812131820662938545 312875748609098865497203909)
          ·
            refine ⟨58664202864206037280725733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312875748609098865497203909 58664202864206037280725733)
            ·
              refine ⟨10999538037038631990136075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58664202864206037280725733 10999538037038631990136075)
              ·
                refine ⟨16499307055557947985204113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10999538037038631990136075 16499307055557947985204113)
                ·
                  refine ⟨12374480291668460988903085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16499307055557947985204113 12374480291668460988903085)
                  ·
                    refine ⟨4640430109375672870838657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12374480291668460988903085 4640430109375672870838657)
                    ·
                      refine ⟨3480322582031754653128993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640430109375672870838657 3480322582031754653128993)
                      ·
                        rfl

theorem cell23_6777904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 2, 3, 2].length) (baseStart_6777904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777904 prefixEnd_6777904 := by exact prefixLift 6777904
  have htrace : WordTrace (prefixWord ++ tailWord_6777904) baseStart_6777904 baseEnd_6777904 := by
    simpa [prefixWord, tailWord_6777904, baseEnd_6777904] using wordTrace_append hprefix tailTrace_6777904
  have hstable : (prefixWord ++ tailWord_6777904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777904).length < 2 ^ (prefixWord ++ tailWord_6777904).sum := by decide
  have hdescent : baseEnd_6777904 < baseStart_6777904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777930 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_6777930 : Nat := 118140960795 + 6777930 * 2 ^ 59
def prefixEnd_6777930 : Nat := 4983230072969 + 3 ^ 40 * 6777930 * 2
def baseEnd_6777930 : Nat := 3480335932528771551403873

theorem tailTrace_6777930 : CollatzResearch.WordTrace tailWord_6777930 prefixEnd_6777930 3480335932528771551403873 := by
  unfold tailWord_6777930
  simp only [CollatzResearch.WordTrace]
  refine ⟨61802854083681165782398811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164807610889816442086396829 61802854083681165782398811)
  ·
    refine ⟨92704281125521748673598217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61802854083681165782398811 92704281125521748673598217)
    ·
      refine ⟨69528210844141311505198663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92704281125521748673598217 69528210844141311505198663)
      ·
        refine ⟨104292316266211967257797995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69528210844141311505198663 104292316266211967257797995)
        ·
          refine ⟨156438474399317950886696993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104292316266211967257797995 156438474399317950886696993)
          ·
            refine ⟨117328855799488463165022745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156438474399317950886696993 117328855799488463165022745)
            ·
              refine ⟨87996641849616347373767059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117328855799488463165022745 87996641849616347373767059)
              ·
                refine ⟨131994962774424521060650589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87996641849616347373767059 131994962774424521060650589)
                ·
                  refine ⟨49498111040409195397743971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131994962774424521060650589 49498111040409195397743971)
                  ·
                    refine ⟨74247166560613793096615957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49498111040409195397743971 74247166560613793096615957)
                    ·
                      refine ⟨3480335932528771551403873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74247166560613793096615957 3480335932528771551403873)
                      ·
                        rfl

theorem cell23_6777930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_6777930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777930 prefixEnd_6777930 := by exact prefixLift 6777930
  have htrace : WordTrace (prefixWord ++ tailWord_6777930) baseStart_6777930 baseEnd_6777930 := by
    simpa [prefixWord, tailWord_6777930, baseEnd_6777930] using wordTrace_append hprefix tailTrace_6777930
  have hstable : (prefixWord ++ tailWord_6777930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777930).length < 2 ^ (prefixWord ++ tailWord_6777930).sum := by decide
  have hdescent : baseEnd_6777930 < baseStart_6777930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777937 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 3, 2, 3]
def baseStart_6777937 : Nat := 118140960795 + 6777937 * 2 ^ 59
def prefixEnd_6777937 : Nat := 4983230072969 + 3 ^ 40 * 6777937 * 2
def baseEnd_6777937 : Nat := 3480339526893353024016341

theorem tailTrace_6777937 : CollatzResearch.WordTrace tailWord_6777937 prefixEnd_6777937 3480339526893353024016341 := by
  unfold tailWord_6777937
  simp only [CollatzResearch.WordTrace]
  refine ⟨247211671645699303325100065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164807781097132868883400043 247211671645699303325100065)
  ·
    refine ⟨185408753734274477493825049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247211671645699303325100065 185408753734274477493825049)
    ·
      refine ⟨139056565300705858120368787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185408753734274477493825049 139056565300705858120368787)
      ·
        refine ⟨208584847951058787180553181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139056565300705858120368787 208584847951058787180553181)
        ·
          refine ⟨78219317981647045192707443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208584847951058787180553181 78219317981647045192707443)
          ·
            refine ⟨117328976972470567789061165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78219317981647045192707443 117328976972470567789061165)
            ·
              refine ⟨43998366364676462920897937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117328976972470567789061165 43998366364676462920897937)
              ·
                refine ⟨32998774773507347190673453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43998366364676462920897937 32998774773507347190673453)
                ·
                  refine ⟨12374540540065255196502545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32998774773507347190673453 12374540540065255196502545)
                  ·
                    refine ⟨9280905405048941397376909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12374540540065255196502545 9280905405048941397376909)
                    ·
                      refine ⟨3480339526893353024016341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9280905405048941397376909 3480339526893353024016341)
                      ·
                        rfl

theorem cell23_6777937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_6777937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777937 prefixEnd_6777937 := by exact prefixLift 6777937
  have htrace : WordTrace (prefixWord ++ tailWord_6777937) baseStart_6777937 baseEnd_6777937 := by
    simpa [prefixWord, tailWord_6777937, baseEnd_6777937] using wordTrace_append hprefix tailTrace_6777937
  have hstable : (prefixWord ++ tailWord_6777937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777937).length < 2 ^ (prefixWord ++ tailWord_6777937).sum := by decide
  have hdescent : baseEnd_6777937 < baseStart_6777937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777957 : List Nat := [1, 3, 1, 3, 2, 1, 5, 7]
def baseStart_6777957 : Nat := 118140960795 + 6777957 * 2 ^ 59
def prefixEnd_6777957 : Nat := 4983230072969 + 3 ^ 40 * 6777957 * 2
def baseEnd_6777957 : Nat := 128901844315053442435787

theorem tailTrace_6777957 : CollatzResearch.WordTrace tailWord_6777957 prefixEnd_6777957 128901844315053442435787 := by
  unfold tailWord_6777957
  simp only [CollatzResearch.WordTrace]
  refine ⟨247212401105626846740828125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164808267403751231160552083 247212401105626846740828125)
  ·
    refine ⟨92704650414610067527810547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247212401105626846740828125 92704650414610067527810547)
    ·
      refine ⟨139056975621915101291715821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92704650414610067527810547 139056975621915101291715821)
      ·
        refine ⟨52146365858218162984393433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139056975621915101291715821 52146365858218162984393433)
        ·
          refine ⟨39109774393663622238295075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52146365858218162984393433 39109774393663622238295075)
          ·
            refine ⟨58664661590495433357442613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39109774393663622238295075 58664661590495433357442613)
            ·
              refine ⟨5499812024108946877260245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58664661590495433357442613 5499812024108946877260245)
              ·
                refine ⟨128901844315053442435787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5499812024108946877260245 128901844315053442435787)
                ·
                  rfl

theorem cell23_6777957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 7].length) (baseStart_6777957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777957 prefixEnd_6777957 := by exact prefixLift 6777957
  have htrace : WordTrace (prefixWord ++ tailWord_6777957) baseStart_6777957 baseEnd_6777957 := by
    simpa [prefixWord, tailWord_6777957, baseEnd_6777957] using wordTrace_append hprefix tailTrace_6777957
  have hstable : (prefixWord ++ tailWord_6777957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777957).length < 2 ^ (prefixWord ++ tailWord_6777957).sum := by decide
  have hdescent : baseEnd_6777957 < baseStart_6777957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777967 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 3]
def baseStart_6777967 : Nat := 118140960795 + 6777967 * 2 ^ 59
def prefixEnd_6777967 : Nat := 4983230072969 + 3 ^ 40 * 6777967 * 2
def baseEnd_6777967 : Nat := 3480354931312987906641203

theorem tailTrace_6777967 : CollatzResearch.WordTrace tailWord_6777967 prefixEnd_6777967 3480354931312987906641203 := by
  unfold tailWord_6777967
  simp only [CollatzResearch.WordTrace]
  refine ⟨247212765835590618448692155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164808510557060412299128103 247212765835590618448692155)
  ·
    refine ⟨370819148753385927673038233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247212765835590618448692155 370819148753385927673038233)
    ·
      refine ⟨278114361565039445754778675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370819148753385927673038233 278114361565039445754778675)
      ·
        refine ⟨417171542347559168632168013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278114361565039445754778675 417171542347559168632168013)
        ·
          refine ⟨156439328380334688237063005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 417171542347559168632168013 156439328380334688237063005)
          ·
            refine ⟨58664748142625508088898627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156439328380334688237063005 58664748142625508088898627)
            ·
              refine ⟨87997122213938262133347941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58664748142625508088898627 87997122213938262133347941)
              ·
                refine ⟨16499460415113424150002739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87997122213938262133347941 16499460415113424150002739)
                ·
                  refine ⟨24749190622670136225004109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16499460415113424150002739 24749190622670136225004109)
                  ·
                    refine ⟨9280946483501301084376541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24749190622670136225004109 9280946483501301084376541)
                    ·
                      refine ⟨3480354931312987906641203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9280946483501301084376541 3480354931312987906641203)
                      ·
                        rfl

theorem cell23_6777967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 3].length) (baseStart_6777967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777967 prefixEnd_6777967 := by exact prefixLift 6777967
  have htrace : WordTrace (prefixWord ++ tailWord_6777967) baseStart_6777967 baseEnd_6777967 := by
    simpa [prefixWord, tailWord_6777967, baseEnd_6777967] using wordTrace_append hprefix tailTrace_6777967
  have hstable : (prefixWord ++ tailWord_6777967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777967).length < 2 ^ (prefixWord ++ tailWord_6777967).sum := by decide
  have hdescent : baseEnd_6777967 < baseStart_6777967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777968 : List Nat := [2, 1, 1, 1, 5, 1, 4, 3, 1, 2, 2]
def baseStart_6777968 : Nat := 118140960795 + 6777968 * 2 ^ 59
def prefixEnd_6777968 : Nat := 4983230072969 + 3 ^ 40 * 6777968 * 2
def baseEnd_6777968 : Nat := 3480355444793642402728699

theorem tailTrace_6777968 : CollatzResearch.WordTrace tailWord_6777968 prefixEnd_6777968 3480355444793642402728699 := by
  unfold tailWord_6777968
  simp only [CollatzResearch.WordTrace]
  refine ⟨123606401154293497809739279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164808534872391330412985705 123606401154293497809739279)
  ·
    refine ⟨185409601731440246714608919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123606401154293497809739279 185409601731440246714608919)
    ·
      refine ⟨278114402597160370071913379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185409601731440246714608919 278114402597160370071913379)
      ·
        refine ⟨417171603895740555107870069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278114402597160370071913379 417171603895740555107870069)
        ·
          refine ⟨39109837865225677041362819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 417171603895740555107870069 39109837865225677041362819)
          ·
            refine ⟨58664756797838515562044229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39109837865225677041362819 58664756797838515562044229)
            ·
              refine ⟨10999641899594721667883293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58664756797838515562044229 10999641899594721667883293)
              ·
                refine ⟨4124865712348020625456235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10999641899594721667883293 4124865712348020625456235)
                ·
                  refine ⟨6187298568522030938184353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4124865712348020625456235 6187298568522030938184353)
                  ·
                    refine ⟨4640473926391523203638265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6187298568522030938184353 4640473926391523203638265)
                    ·
                      refine ⟨3480355444793642402728699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640473926391523203638265 3480355444793642402728699)
                      ·
                        rfl

theorem cell23_6777968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 1, 2, 2].length) (baseStart_6777968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777968 prefixEnd_6777968 := by exact prefixLift 6777968
  have htrace : WordTrace (prefixWord ++ tailWord_6777968) baseStart_6777968 baseEnd_6777968 := by
    simpa [prefixWord, tailWord_6777968, baseEnd_6777968] using wordTrace_append hprefix tailTrace_6777968
  have hstable : (prefixWord ++ tailWord_6777968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777968).length < 2 ^ (prefixWord ++ tailWord_6777968).sum := by decide
  have hdescent : baseEnd_6777968 < baseStart_6777968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778000 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 1, 8]
def baseStart_6778000 : Nat := 118140960795 + 6778000 * 2 ^ 59
def prefixEnd_6778000 : Nat := 4983230072969 + 3 ^ 40 * 6778000 * 2
def baseEnd_6778000 : Nat := 1160123958724862092509517

theorem tailTrace_6778000 : CollatzResearch.WordTrace tailWord_6778000 prefixEnd_6778000 1160123958724862092509517 := by
  unfold tailWord_6778000
  simp only [CollatzResearch.WordTrace]
  refine ⟨123606984722235532542321727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164809312962980710056428969 123606984722235532542321727)
  ·
    refine ⟨185410477083353298813482591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123606984722235532542321727 185410477083353298813482591)
    ·
      refine ⟨278115715625029948220223887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185410477083353298813482591 278115715625029948220223887)
      ·
        refine ⟨417173573437544922330335831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278115715625029948220223887 417173573437544922330335831)
        ·
          refine ⟨625760360156317383495503747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417173573437544922330335831 625760360156317383495503747)
          ·
            refine ⟨938640540234476075243255621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625760360156317383495503747 938640540234476075243255621)
            ·
              refine ⟨175995101293964264108110429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 938640540234476075243255621 175995101293964264108110429)
              ·
                refine ⟨65998162985236599040541411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175995101293964264108110429 65998162985236599040541411)
                ·
                  refine ⟨98997244477854898560812117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65998162985236599040541411 98997244477854898560812117)
                  ·
                    refine ⟨1160123958724862092509517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98997244477854898560812117 1160123958724862092509517)
                    ·
                      rfl

theorem cell23_6778000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_6778000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778000 prefixEnd_6778000 := by exact prefixLift 6778000
  have htrace : WordTrace (prefixWord ++ tailWord_6778000) baseStart_6778000 baseEnd_6778000 := by
    simpa [prefixWord, tailWord_6778000, baseEnd_6778000] using wordTrace_append hprefix tailTrace_6778000
  have hstable : (prefixWord ++ tailWord_6778000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778000).length < 2 ^ (prefixWord ++ tailWord_6778000).sum := by decide
  have hdescent : baseEnd_6778000 < baseStart_6778000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778014 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_6778014 : Nat := 118140960795 + 6778014 * 2 ^ 59
def prefixEnd_6778014 : Nat := 4983230072969 + 3 ^ 40 * 6778014 * 2
def baseEnd_6778014 : Nat := 3480379064903749222753487

theorem tailTrace_6778014 : CollatzResearch.WordTrace tailWord_6778014 prefixEnd_6778014 3480379064903749222753487 := by
  unfold tailWord_6778014
  simp only [CollatzResearch.WordTrace]
  refine ⟨30901810008302543184456637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164809653377613563650435397 30901810008302543184456637)
  ·
    refine ⟨11588178753113453694171239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30901810008302543184456637 11588178753113453694171239)
    ·
      refine ⟨17382268129670180541256859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11588178753113453694171239 17382268129670180541256859)
      ·
        refine ⟨26073402194505270811885289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17382268129670180541256859 26073402194505270811885289)
        ·
          refine ⟨19555051645878953108913967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26073402194505270811885289 19555051645878953108913967)
          ·
            refine ⟨29332577468818429663370951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19555051645878953108913967 29332577468818429663370951)
            ·
              refine ⟨43998866203227644495056427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29332577468818429663370951 43998866203227644495056427)
              ·
                refine ⟨65998299304841466742584641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43998866203227644495056427 65998299304841466742584641)
                ·
                  refine ⟨49498724478631100056938481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65998299304841466742584641 49498724478631100056938481)
                  ·
                    refine ⟨37124043358973325042703861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49498724478631100056938481 37124043358973325042703861)
                    ·
                      refine ⟨3480379064903749222753487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37124043358973325042703861 3480379064903749222753487)
                      ·
                        rfl

theorem cell23_6778014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_6778014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778014 prefixEnd_6778014 := by exact prefixLift 6778014
  have htrace : WordTrace (prefixWord ++ tailWord_6778014) baseStart_6778014 baseEnd_6778014 := by
    simpa [prefixWord, tailWord_6778014, baseEnd_6778014] using wordTrace_append hprefix tailTrace_6778014
  have hstable : (prefixWord ++ tailWord_6778014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778014).length < 2 ^ (prefixWord ++ tailWord_6778014).sum := by decide
  have hdescent : baseEnd_6778014 < baseStart_6778014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778041 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 4, 2, 2]
def baseStart_6778041 : Nat := 118140960795 + 6778041 * 2 ^ 59
def prefixEnd_6778041 : Nat := 4983230072969 + 3 ^ 40 * 6778041 * 2
def baseEnd_6778041 : Nat := 3480392928881420617115863

theorem tailTrace_6778041 : CollatzResearch.WordTrace tailWord_6778041 prefixEnd_6778041 3480392928881420617115863 := by
  unfold tailWord_6778041
  simp only [CollatzResearch.WordTrace]
  refine ⟨247215464837322529086885977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164810309891548352724590651 247215464837322529086885977)
  ·
    refine ⟨185411598627991896815164483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247215464837322529086885977 185411598627991896815164483)
    ·
      refine ⟨278117397941987845222746725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185411598627991896815164483 278117397941987845222746725)
      ·
        refine ⟨52147012114122720979265011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278117397941987845222746725 52147012114122720979265011)
        ·
          refine ⟨78220518171184081468897517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52147012114122720979265011 78220518171184081468897517)
          ·
            refine ⟨29332694314194030550836569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78220518171184081468897517 29332694314194030550836569)
            ·
              refine ⟨21999520735645522913127427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29332694314194030550836569 21999520735645522913127427)
              ·
                refine ⟨32999281103468284369691141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21999520735645522913127427 32999281103468284369691141)
                ·
                  refine ⟨6187365206900303319317089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32999281103468284369691141 6187365206900303319317089)
                  ·
                    refine ⟨4640523905175227489487817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6187365206900303319317089 4640523905175227489487817)
                    ·
                      refine ⟨3480392928881420617115863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640523905175227489487817 3480392928881420617115863)
                      ·
                        rfl

theorem cell23_6778041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_6778041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778041 prefixEnd_6778041 := by exact prefixLift 6778041
  have htrace : WordTrace (prefixWord ++ tailWord_6778041) baseStart_6778041 baseEnd_6778041 := by
    simpa [prefixWord, tailWord_6778041, baseEnd_6778041] using wordTrace_append hprefix tailTrace_6778041
  have hstable : (prefixWord ++ tailWord_6778041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778041).length < 2 ^ (prefixWord ++ tailWord_6778041).sum := by decide
  have hdescent : baseEnd_6778041 < baseStart_6778041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778047 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 7]
def baseStart_6778047 : Nat := 118140960795 + 6778047 * 2 ^ 59
def prefixEnd_6778047 : Nat := 4983230072969 + 3 ^ 40 * 6778047 * 2
def baseEnd_6778047 : Nat := 386710667751705288182315

theorem tailTrace_6778047 : CollatzResearch.WordTrace tailWord_6778047 prefixEnd_6778047 386710667751705288182315 := by
  unfold tailWord_6778047
  simp only [CollatzResearch.WordTrace]
  refine ⟨247215683675300792111604395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164810455783533861407736263 247215683675300792111604395)
  ·
    refine ⟨370823525512951188167406593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247215683675300792111604395 370823525512951188167406593)
    ·
      refine ⟨278117644134713391125554945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370823525512951188167406593 278117644134713391125554945)
      ·
        refine ⟨208588233101035043344166209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278117644134713391125554945 208588233101035043344166209)
        ·
          refine ⟨156441174825776282508124657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208588233101035043344166209 156441174825776282508124657)
          ·
            refine ⟨117330881119332211881093493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156441174825776282508124657 117330881119332211881093493)
            ·
              refine ⟨10999770104937394863852515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117330881119332211881093493 10999770104937394863852515)
              ·
                refine ⟨16499655157406092295778773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10999770104937394863852515 16499655157406092295778773)
                ·
                  refine ⟨386710667751705288182315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16499655157406092295778773 386710667751705288182315)
                  ·
                    rfl

theorem cell23_6778047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 7].length) (baseStart_6778047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778047 prefixEnd_6778047 := by exact prefixLift 6778047
  have htrace : WordTrace (prefixWord ++ tailWord_6778047) baseStart_6778047 baseEnd_6778047 := by
    simpa [prefixWord, tailWord_6778047, baseEnd_6778047] using wordTrace_append hprefix tailTrace_6778047
  have hstable : (prefixWord ++ tailWord_6778047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778047).length < 2 ^ (prefixWord ++ tailWord_6778047).sum := by decide
  have hdescent : baseEnd_6778047 < baseStart_6778047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778052 : List Nat := [2, 3, 3, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_6778052 : Nat := 118140960795 + 6778052 * 2 ^ 59
def prefixEnd_6778052 : Nat := 4983230072969 + 3 ^ 40 * 6778052 * 2
def baseEnd_6778052 : Nat := 3480398577168620074078313

theorem tailTrace_6778052 : CollatzResearch.WordTrace tailWord_6778052 prefixEnd_6778052 3480398577168620074078313 := by
  unfold tailWord_6778052
  simp only [CollatzResearch.WordTrace]
  refine ⟨123607933020141338982768205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164810577360188451977024273 123607933020141338982768205)
  ·
    refine ⟨46352974882553002118538077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123607933020141338982768205 46352974882553002118538077)
    ·
      refine ⟨17382365580957375794451779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46352974882553002118538077 17382365580957375794451779)
      ·
        refine ⟨26073548371436063691677669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17382365580957375794451779 26073548371436063691677669)
        ·
          refine ⟨4888790319644261942189563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26073548371436063691677669 4888790319644261942189563)
          ·
            refine ⟨7333185479466392913284345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4888790319644261942189563 7333185479466392913284345)
            ·
              refine ⟨5499889109599794684963259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7333185479466392913284345 5499889109599794684963259)
              ·
                refine ⟨8249833664399692027444889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5499889109599794684963259 8249833664399692027444889)
                ·
                  refine ⟨6187375248299769020583667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8249833664399692027444889 6187375248299769020583667)
                  ·
                    refine ⟨9281062872449653530875501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6187375248299769020583667 9281062872449653530875501)
                    ·
                      refine ⟨3480398577168620074078313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9281062872449653530875501 3480398577168620074078313)
                      ·
                        rfl

theorem cell23_6778052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_6778052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778052 prefixEnd_6778052 := by exact prefixLift 6778052
  have htrace : WordTrace (prefixWord ++ tailWord_6778052) baseStart_6778052 baseEnd_6778052 := by
    simpa [prefixWord, tailWord_6778052, baseEnd_6778052] using wordTrace_append hprefix tailTrace_6778052
  have hstable : (prefixWord ++ tailWord_6778052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778052).length < 2 ^ (prefixWord ++ tailWord_6778052).sum := by decide
  have hdescent : baseEnd_6778052 < baseStart_6778052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778057 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 6, 3, 3]
def baseStart_6778057 : Nat := 118140960795 + 6778057 * 2 ^ 59
def prefixEnd_6778057 : Nat := 4983230072969 + 3 ^ 40 * 6778057 * 2
def baseEnd_6778057 : Nat := 3480401144571892554515789

theorem tailTrace_6778057 : CollatzResearch.WordTrace tailWord_6778057 prefixEnd_6778057 3480401144571892554515789 := by
  unfold tailWord_6778057
  simp only [CollatzResearch.WordTrace]
  refine ⟨247216048405264563819468425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164810698936843042546312283 247216048405264563819468425)
  ·
    refine ⟨185412036303948422864601319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247216048405264563819468425 185412036303948422864601319)
    ·
      refine ⟨278118054455922634296901979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185412036303948422864601319 278118054455922634296901979)
      ·
        refine ⟨417177081683883951445352969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278118054455922634296901979 417177081683883951445352969)
        ·
          refine ⟨312882811262912963584014727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417177081683883951445352969 312882811262912963584014727)
          ·
            refine ⟨469324216894369445376022091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312882811262912963584014727 469324216894369445376022091)
            ·
              refine ⟨703986325341554168064033137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469324216894369445376022091 703986325341554168064033137)
              ·
                refine ⟨527989744006165626048024853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703986325341554168064033137 527989744006165626048024853)
                ·
                  refine ⟨24749519250289013721001165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 527989744006165626048024853 24749519250289013721001165)
                  ·
                    refine ⟨9281069718858380145375437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24749519250289013721001165 9281069718858380145375437)
                    ·
                      refine ⟨3480401144571892554515789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9281069718858380145375437 3480401144571892554515789)
                      ·
                        rfl

theorem cell23_6778057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 3, 3].length) (baseStart_6778057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778057 prefixEnd_6778057 := by exact prefixLift 6778057
  have htrace : WordTrace (prefixWord ++ tailWord_6778057) baseStart_6778057 baseEnd_6778057 := by
    simpa [prefixWord, tailWord_6778057, baseEnd_6778057] using wordTrace_append hprefix tailTrace_6778057
  have hstable : (prefixWord ++ tailWord_6778057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778057).length < 2 ^ (prefixWord ++ tailWord_6778057).sum := by decide
  have hdescent : baseEnd_6778057 < baseStart_6778057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778058 : List Nat := [3, 1, 2, 1, 3, 3, 1, 3, 2, 2, 2]
def baseStart_6778058 : Nat := 118140960795 + 6778058 * 2 ^ 59
def prefixEnd_6778058 : Nat := 4983230072969 + 3 ^ 40 * 6778058 * 2
def baseEnd_6778058 : Nat := 3480401658052547050603285

theorem tailTrace_6778058 : CollatzResearch.WordTrace tailWord_6778058 prefixEnd_6778058 3480401658052547050603285 := by
  unfold tailWord_6778058
  simp only [CollatzResearch.WordTrace]
  refine ⟨61804021219565235247563707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164810723252173960660169885 61804021219565235247563707)
  ·
    refine ⟨92706031829347852871345561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61804021219565235247563707 92706031829347852871345561)
    ·
      refine ⟨69529523872010889653509171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92706031829347852871345561 69529523872010889653509171)
      ·
        refine ⟨104294285808016334480263757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69529523872010889653509171 104294285808016334480263757)
        ·
          refine ⟨39110357178006125430098909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104294285808016334480263757 39110357178006125430098909)
          ·
            refine ⟨14666383941752297036287091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39110357178006125430098909 14666383941752297036287091)
            ·
              refine ⟨21999575912628445554430637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14666383941752297036287091 21999575912628445554430637)
              ·
                refine ⟨8249840967235667082911489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21999575912628445554430637 8249840967235667082911489)
                ·
                  refine ⟨6187380725426750312183617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8249840967235667082911489 6187380725426750312183617)
                  ·
                    refine ⟨4640535544070062734137713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6187380725426750312183617 4640535544070062734137713)
                    ·
                      refine ⟨3480401658052547050603285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640535544070062734137713 3480401658052547050603285)
                      ·
                        rfl

theorem cell23_6778058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_6778058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778058 prefixEnd_6778058 := by exact prefixLift 6778058
  have htrace : WordTrace (prefixWord ++ tailWord_6778058) baseStart_6778058 baseEnd_6778058 := by
    simpa [prefixWord, tailWord_6778058, baseEnd_6778058] using wordTrace_append hprefix tailTrace_6778058
  have hstable : (prefixWord ++ tailWord_6778058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778058).length < 2 ^ (prefixWord ++ tailWord_6778058).sum := by decide
  have hdescent : baseEnd_6778058 < baseStart_6778058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778094 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_6778094 : Nat := 118140960795 + 6778094 * 2 ^ 59
def prefixEnd_6778094 : Nat := 4983230072969 + 3 ^ 40 * 6778094 * 2
def baseEnd_6778094 : Nat := 1160140047785369636584373

theorem tailTrace_6778094 : CollatzResearch.WordTrace tailWord_6778094 prefixEnd_6778094 1160140047785369636584373 := by
  unfold tailWord_6778094
  simp only [CollatzResearch.WordTrace]
  refine ⟨30902174738266314892320667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164811598604087012759043557 30902174738266314892320667)
  ·
    refine ⟨46353262107399472338481001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30902174738266314892320667 46353262107399472338481001)
    ·
      refine ⟨34764946580549604253860751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46353262107399472338481001 34764946580549604253860751)
      ·
        refine ⟨52147419870824406380791127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34764946580549604253860751 52147419870824406380791127)
        ·
          refine ⟨78221129806236609571186691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52147419870824406380791127 78221129806236609571186691)
          ·
            refine ⟨117331694709354914356780037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78221129806236609571186691 117331694709354914356780037)
            ·
              refine ⟨21999692758004046441896257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117331694709354914356780037 21999692758004046441896257)
              ·
                refine ⟨16499769568503034831422193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21999692758004046441896257 16499769568503034831422193)
                ·
                  refine ⟨12374827176377276123566645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16499769568503034831422193 12374827176377276123566645)
                  ·
                    refine ⟨1160140047785369636584373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12374827176377276123566645 1160140047785369636584373)
                    ·
                      rfl

theorem cell23_6778094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_6778094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778094 prefixEnd_6778094 := by exact prefixLift 6778094
  have htrace : WordTrace (prefixWord ++ tailWord_6778094) baseStart_6778094 baseEnd_6778094 := by
    simpa [prefixWord, tailWord_6778094, baseEnd_6778094] using wordTrace_append hprefix tailTrace_6778094
  have hstable : (prefixWord ++ tailWord_6778094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778094).length < 2 ^ (prefixWord ++ tailWord_6778094).sum := by decide
  have hdescent : baseEnd_6778094 < baseStart_6778094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778097 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_6778097 : Nat := 118140960795 + 6778097 * 2 ^ 59
def prefixEnd_6778097 : Nat := 4983230072969 + 3 ^ 40 * 6778097 * 2
def baseEnd_6778097 : Nat := 3480421683798072398015605

theorem tailTrace_6778097 : CollatzResearch.WordTrace tailWord_6778097 prefixEnd_6778097 3480421683798072398015605 := by
  unfold tailWord_6778097
  simp only [CollatzResearch.WordTrace]
  refine ⟨247217507325119650650924545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164811671550079767100616363 247217507325119650650924545)
  ·
    refine ⟨185413130493839737988193409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247217507325119650650924545 185413130493839737988193409)
    ·
      refine ⟨139059847870379803491145057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185413130493839737988193409 139059847870379803491145057)
      ·
        refine ⟨104294885902784852618358793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139059847870379803491145057 104294885902784852618358793)
        ·
          refine ⟨78221164427088639463769095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104294885902784852618358793 78221164427088639463769095)
          ·
            refine ⟨117331746640632959195653643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78221164427088639463769095 117331746640632959195653643)
            ·
              refine ⟨175997619960949438793480465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117331746640632959195653643 175997619960949438793480465)
              ·
                refine ⟨131998214970712079095110349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175997619960949438793480465 131998214970712079095110349)
                ·
                  refine ⟨49499330614017029660666381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131998214970712079095110349 49499330614017029660666381)
                  ·
                    refine ⟨18562248980256386122749893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49499330614017029660666381 18562248980256386122749893)
                    ·
                      refine ⟨3480421683798072398015605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18562248980256386122749893 3480421683798072398015605)
                      ·
                        rfl

theorem cell23_6778097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_6778097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778097 prefixEnd_6778097 := by exact prefixLift 6778097
  have htrace : WordTrace (prefixWord ++ tailWord_6778097) baseStart_6778097 baseEnd_6778097 := by
    simpa [prefixWord, tailWord_6778097, baseEnd_6778097] using wordTrace_append hprefix tailTrace_6778097
  have hstable : (prefixWord ++ tailWord_6778097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778097).length < 2 ^ (prefixWord ++ tailWord_6778097).sum := by decide
  have hdescent : baseEnd_6778097 < baseStart_6778097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778124 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 5, 4]
def baseStart_6778124 : Nat := 118140960795 + 6778124 * 2 ^ 59
def prefixEnd_6778124 : Nat := 4983230072969 + 3 ^ 40 * 6778124 * 2
def baseEnd_6778124 : Nat := 1160145182591914597459327

theorem tailTrace_6778124 : CollatzResearch.WordTrace tailWord_6778124 prefixEnd_6778124 1160145182591914597459327 := by
  unfold tailWord_6778124
  simp only [CollatzResearch.WordTrace]
  refine ⟨123609246048010917131078713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164812328064014556174771617 123609246048010917131078713)
  ·
    refine ⟨92706934536008187848309035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123609246048010917131078713 92706934536008187848309035)
    ·
      refine ⟨139060401804012281772463553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92706934536008187848309035 139060401804012281772463553)
      ·
        refine ⟨104295301353009211329347665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139060401804012281772463553 104295301353009211329347665)
        ·
          refine ⟨78221476014756908497010749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104295301353009211329347665 78221476014756908497010749)
          ·
            refine ⟨29333053505533840686379031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78221476014756908497010749 29333053505533840686379031)
            ·
              refine ⟨43999580258300761029568547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29333053505533840686379031 43999580258300761029568547)
              ·
                refine ⟨65999370387451141544352821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43999580258300761029568547 65999370387451141544352821)
                ·
                  refine ⟨6187440973823544519783077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65999370387451141544352821 6187440973823544519783077)
                  ·
                    refine ⟨1160145182591914597459327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6187440973823544519783077 1160145182591914597459327)
                    ·
                      rfl

theorem cell23_6778124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_6778124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778124 prefixEnd_6778124 := by exact prefixLift 6778124
  have htrace : WordTrace (prefixWord ++ tailWord_6778124) baseStart_6778124 baseEnd_6778124 := by
    simpa [prefixWord, tailWord_6778124, baseEnd_6778124] using wordTrace_append hprefix tailTrace_6778124
  have hstable : (prefixWord ++ tailWord_6778124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778124).length < 2 ^ (prefixWord ++ tailWord_6778124).sum := by decide
  have hdescent : baseEnd_6778124 < baseStart_6778124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778174 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_6778174 : Nat := 118140960795 + 6778174 * 2 ^ 59
def prefixEnd_6778174 : Nat := 4983230072969 + 3 ^ 40 * 6778174 * 2
def baseEnd_6778174 : Nat := 3480461221808468596752751

theorem tailTrace_6778174 : CollatzResearch.WordTrace tailWord_6778174 prefixEnd_6778174 3480461221808468596752751 := by
  unfold tailWord_6778174
  simp only [CollatzResearch.WordTrace]
  refine ⟨30902539468230086600184697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164813543830560461867651717 30902539468230086600184697)
  ·
    refine ⟨23176904601172564950138523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30902539468230086600184697 23176904601172564950138523)
    ·
      refine ⟨34765356901758847425207785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23176904601172564950138523 34765356901758847425207785)
      ·
        refine ⟨26074017676319135568905839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34765356901758847425207785 26074017676319135568905839)
        ·
          refine ⟨39111026514478703353358759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26074017676319135568905839 39111026514478703353358759)
          ·
            refine ⟨58666539771718055030038139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39111026514478703353358759 58666539771718055030038139)
            ·
              refine ⟨87999809657577082545057209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58666539771718055030038139 87999809657577082545057209)
              ·
                refine ⟨65999857243182811908792907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87999809657577082545057209 65999857243182811908792907)
                ·
                  refine ⟨98999785864774217863189361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65999857243182811908792907 98999785864774217863189361)
                  ·
                    refine ⟨74249839398580663397392021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98999785864774217863189361 74249839398580663397392021)
                    ·
                      refine ⟨3480461221808468596752751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74249839398580663397392021 3480461221808468596752751)
                      ·
                        rfl

theorem cell23_6778174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_6778174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778174 prefixEnd_6778174 := by exact prefixLift 6778174
  have htrace : WordTrace (prefixWord ++ tailWord_6778174) baseStart_6778174 baseEnd_6778174 := by
    simpa [prefixWord, tailWord_6778174, baseEnd_6778174] using wordTrace_append hprefix tailTrace_6778174
  have hstable : (prefixWord ++ tailWord_6778174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778174).length < 2 ^ (prefixWord ++ tailWord_6778174).sum := by decide
  have hdescent : baseEnd_6778174 < baseStart_6778174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778208 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 2, 3, 2]
def baseStart_6778208 : Nat := 118140960795 + 6778208 * 2 ^ 59
def prefixEnd_6778208 : Nat := 4983230072969 + 3 ^ 40 * 6778208 * 2
def baseEnd_6778208 : Nat := 3480478680150721463727595

theorem tailTrace_6778208 : CollatzResearch.WordTrace tailWord_6778208 prefixEnd_6778208 3480478680150721463727595 := by
  unfold tailWord_6778208
  simp only [CollatzResearch.WordTrace]
  refine ⟨123610777913858758304107639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164814370551811677738810185 123610777913858758304107639)
  ·
    refine ⟨185416166870788137456161459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123610777913858758304107639 185416166870788137456161459)
    ·
      refine ⟨278124250306182206184242189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185416166870788137456161459 278124250306182206184242189)
      ·
        refine ⟨104296593864818327319090821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278124250306182206184242189 104296593864818327319090821)
        ·
          refine ⟨19555611349653436372329529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104296593864818327319090821 19555611349653436372329529)
          ·
            refine ⟨14666708512240077279247147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19555611349653436372329529 14666708512240077279247147)
            ·
              refine ⟨22000062768360115918870721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14666708512240077279247147 22000062768360115918870721)
              ·
                refine ⟨16500047076270086939153041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22000062768360115918870721 16500047076270086939153041)
                ·
                  refine ⟨12375035307202565204364781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16500047076270086939153041 12375035307202565204364781)
                  ·
                    refine ⟨4640638240200961951636793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12375035307202565204364781 4640638240200961951636793)
                    ·
                      refine ⟨3480478680150721463727595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640638240200961951636793 3480478680150721463727595)
                      ·
                        rfl

theorem cell23_6778208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_6778208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778208 prefixEnd_6778208 := by exact prefixLift 6778208
  have htrace : WordTrace (prefixWord ++ tailWord_6778208) baseStart_6778208 baseEnd_6778208 := by
    simpa [prefixWord, tailWord_6778208, baseEnd_6778208] using wordTrace_append hprefix tailTrace_6778208
  have hstable : (prefixWord ++ tailWord_6778208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778208).length < 2 ^ (prefixWord ++ tailWord_6778208).sum := by decide
  have hdescent : baseEnd_6778208 < baseStart_6778208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778215 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_6778215 : Nat := 118140960795 + 6778215 * 2 ^ 59
def prefixEnd_6778215 : Nat := 4983230072969 + 3 ^ 40 * 6778215 * 2
def baseEnd_6778215 : Nat := 3480482274515302936340063

theorem tailTrace_6778215 : CollatzResearch.WordTrace tailWord_6778215 prefixEnd_6778215 3480482274515302936340063 := by
  unfold tailWord_6778215
  simp only [CollatzResearch.WordTrace]
  refine ⟨247221811138692156803720099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164814540759128104535813399 247221811138692156803720099)
  ·
    refine ⟨370832716708038235205580149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247221811138692156803720099 370832716708038235205580149)
    ·
      refine ⟨34765567191378584550523139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 370832716708038235205580149 34765567191378584550523139)
      ·
        refine ⟨52148350787067876825784709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34765567191378584550523139 52148350787067876825784709)
        ·
          refine ⟨9777815772575226904834633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52148350787067876825784709 9777815772575226904834633)
          ·
            refine ⟨7333361829431420178625975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9777815772575226904834633 7333361829431420178625975)
            ·
              refine ⟨11000042744147130267938963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7333361829431420178625975 11000042744147130267938963)
              ·
                refine ⟨16500064116220695401908445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11000042744147130267938963 16500064116220695401908445)
                ·
                  refine ⟨6187524043582760775715667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16500064116220695401908445 6187524043582760775715667)
                  ·
                    refine ⟨9281286065374141163573501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6187524043582760775715667 9281286065374141163573501)
                    ·
                      refine ⟨3480482274515302936340063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9281286065374141163573501 3480482274515302936340063)
                      ·
                        rfl

theorem cell23_6778215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_6778215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778215 prefixEnd_6778215 := by exact prefixLift 6778215
  have htrace : WordTrace (prefixWord ++ tailWord_6778215) baseStart_6778215 baseEnd_6778215 := by
    simpa [prefixWord, tailWord_6778215, baseEnd_6778215] using wordTrace_append hprefix tailTrace_6778215
  have hstable : (prefixWord ++ tailWord_6778215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778215).length < 2 ^ (prefixWord ++ tailWord_6778215).sum := by decide
  have hdescent : baseEnd_6778215 < baseStart_6778215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778222 : List Nat := [4, 1, 2, 4, 2, 1, 2, 1, 6]
def baseStart_6778222 : Nat := 118140960795 + 6778222 * 2 ^ 59
def prefixEnd_6778222 : Nat := 4983230072969 + 3 ^ 40 * 6778222 * 2
def baseEnd_6778222 : Nat := 386720652097764934328059

theorem tailTrace_6778222 : CollatzResearch.WordTrace tailWord_6778222 prefixEnd_6778222 386720652097764934328059 := by
  unfold tailWord_6778222
  simp only [CollatzResearch.WordTrace]
  refine ⟨30902758306208349624903115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164814710966444531332816613 30902758306208349624903115)
  ·
    refine ⟨46354137459312524437354673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30902758306208349624903115 46354137459312524437354673)
    ·
      refine ⟨34765603094484393328016005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46354137459312524437354673 34765603094484393328016005)
      ·
        refine ⟨6518550580215823749003001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34765603094484393328016005 6518550580215823749003001)
        ·
          refine ⟨4888912935161867811752251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6518550580215823749003001 4888912935161867811752251)
          ·
            refine ⟨7333369402742801717628377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4888912935161867811752251 7333369402742801717628377)
            ·
              refine ⟨5500027052057101288221283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7333369402742801717628377 5500027052057101288221283)
              ·
                refine ⟨8250040578085651932331925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5500027052057101288221283 8250040578085651932331925)
                ·
                  refine ⟨386720652097764934328059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8250040578085651932331925 386720652097764934328059)
                  ·
                    rfl

theorem cell23_6778222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_6778222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778222 prefixEnd_6778222 := by exact prefixLift 6778222
  have htrace : WordTrace (prefixWord ++ tailWord_6778222) baseStart_6778222 baseEnd_6778222 := by
    simpa [prefixWord, tailWord_6778222, baseEnd_6778222] using wordTrace_append hprefix tailTrace_6778222
  have hstable : (prefixWord ++ tailWord_6778222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778222).length < 2 ^ (prefixWord ++ tailWord_6778222).sum := by decide
  have hdescent : baseEnd_6778222 < baseStart_6778222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778224 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 5]
def baseStart_6778224 : Nat := 118140960795 + 6778224 * 2 ^ 59
def prefixEnd_6778224 : Nat := 4983230072969 + 3 ^ 40 * 6778224 * 2
def baseEnd_6778224 : Nat := 3480486895841193401127521

theorem tailTrace_6778224 : CollatzResearch.WordTrace tailWord_6778224 prefixEnd_6778224 3480486895841193401127521 := by
  unfold tailWord_6778224
  simp only [CollatzResearch.WordTrace]
  refine ⟨123611069697829775670398863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164814759597106367560531817 123611069697829775670398863)
  ·
    refine ⟨185416604546744663505598295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123611069697829775670398863 185416604546744663505598295)
    ·
      refine ⟨278124906820116995258397443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185416604546744663505598295 278124906820116995258397443)
      ·
        refine ⟨417187360230175492887596165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278124906820116995258397443 417187360230175492887596165)
        ·
          refine ⟨78222630043157904916424281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 417187360230175492887596165 78222630043157904916424281)
          ·
            refine ⟨58666972532368428687318211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78222630043157904916424281 58666972532368428687318211)
            ·
              refine ⟨88000458798552643030977317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58666972532368428687318211 88000458798552643030977317)
              ·
                refine ⟨16500086024728620568308247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88000458798552643030977317 16500086024728620568308247)
                ·
                  refine ⟨24750129037092930852462371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16500086024728620568308247 24750129037092930852462371)
                  ·
                    refine ⟨37125193555639396278693557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24750129037092930852462371 37125193555639396278693557)
                    ·
                      refine ⟨3480486895841193401127521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37125193555639396278693557 3480486895841193401127521)
                      ·
                        rfl

theorem cell23_6778224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_6778224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778224 prefixEnd_6778224 := by exact prefixLift 6778224
  have htrace : WordTrace (prefixWord ++ tailWord_6778224) baseStart_6778224 baseEnd_6778224 := by
    simpa [prefixWord, tailWord_6778224, baseEnd_6778224] using wordTrace_append hprefix tailTrace_6778224
  have hstable : (prefixWord ++ tailWord_6778224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778224).length < 2 ^ (prefixWord ++ tailWord_6778224).sum := by decide
  have hdescent : baseEnd_6778224 < baseStart_6778224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778231 : List Nat := [1, 1, 3, 1, 1, 2, 5, 3, 2, 4]
def baseStart_6778231 : Nat := 118140960795 + 6778231 * 2 ^ 59
def prefixEnd_6778231 : Nat := 4983230072969 + 3 ^ 40 * 6778231 * 2
def baseEnd_6778231 : Nat := 1160163496735258291246663

theorem tailTrace_6778231 : CollatzResearch.WordTrace tailWord_6778231 prefixEnd_6778231 1160163496735258291246663 := by
  unfold tailWord_6778231
  simp only [CollatzResearch.WordTrace]
  refine ⟨247222394706634191536302547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164814929804422794357535031 247222394706634191536302547)
  ·
    refine ⟨370833592059951287304453821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247222394706634191536302547 370833592059951287304453821)
    ·
      refine ⟨139062597022481732739170183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370833592059951287304453821 139062597022481732739170183)
      ·
        refine ⟨208593895533722599108755275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139062597022481732739170183 208593895533722599108755275)
        ·
          refine ⟨312890843300583898663132913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208593895533722599108755275 312890843300583898663132913)
          ·
            refine ⟨234668132475437923997349685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312890843300583898663132913 234668132475437923997349685)
            ·
              refine ⟨22000137419572305374751533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 234668132475437923997349685 22000137419572305374751533)
              ·
                refine ⟨8250051532339614515531825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22000137419572305374751533 8250051532339614515531825)
                ·
                  refine ⟨6187538649254710886648869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8250051532339614515531825 6187538649254710886648869)
                  ·
                    refine ⟨1160163496735258291246663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6187538649254710886648869 1160163496735258291246663)
                    ·
                      rfl

theorem cell23_6778231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_6778231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778231 prefixEnd_6778231 := by exact prefixLift 6778231
  have htrace : WordTrace (prefixWord ++ tailWord_6778231) baseStart_6778231 baseEnd_6778231 := by
    simpa [prefixWord, tailWord_6778231, baseEnd_6778231] using wordTrace_append hprefix tailTrace_6778231
  have hstable : (prefixWord ++ tailWord_6778231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778231).length < 2 ^ (prefixWord ++ tailWord_6778231).sum := by decide
  have hdescent : baseEnd_6778231 < baseStart_6778231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778242 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_6778242 : Nat := 118140960795 + 6778242 * 2 ^ 59
def prefixEnd_6778242 : Nat := 4983230072969 + 3 ^ 40 * 6778242 * 2
def baseEnd_6778242 : Nat := 3480496138492974330702439

theorem tailTrace_6778242 : CollatzResearch.WordTrace tailWord_6778242 prefixEnd_6778242 3480496138492974330702439 := by
  unfold tailWord_6778242
  simp only [CollatzResearch.WordTrace]
  refine ⟨61805698977398585103738245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164815197273062893609968653 61805698977398585103738245)
  ·
    refine ⟨11588568558262234706950921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61805698977398585103738245 11588568558262234706950921)
    ·
      refine ⟨8691426418696676030213191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11588568558262234706950921 8691426418696676030213191)
      ·
        refine ⟨13037139628045014045319787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8691426418696676030213191 13037139628045014045319787)
        ·
          refine ⟨19555709442067521067979681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13037139628045014045319787 19555709442067521067979681)
          ·
            refine ⟨14666782081550640800984761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19555709442067521067979681 14666782081550640800984761)
            ·
              refine ⟨11000086561162980600738571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14666782081550640800984761 11000086561162980600738571)
              ·
                refine ⟨16500129841744470901107857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11000086561162980600738571 16500129841744470901107857)
                ·
                  refine ⟨12375097381308353175830893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16500129841744470901107857 12375097381308353175830893)
                  ·
                    refine ⟨4640661517990632440936585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12375097381308353175830893 4640661517990632440936585)
                    ·
                      refine ⟨3480496138492974330702439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640661517990632440936585 3480496138492974330702439)
                      ·
                        rfl

theorem cell23_6778242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_6778242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778242 prefixEnd_6778242 := by exact prefixLift 6778242
  have htrace : WordTrace (prefixWord ++ tailWord_6778242) baseStart_6778242 baseEnd_6778242 := by
    simpa [prefixWord, tailWord_6778242, baseEnd_6778242] using wordTrace_append hprefix tailTrace_6778242
  have hstable : (prefixWord ++ tailWord_6778242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778242).length < 2 ^ (prefixWord ++ tailWord_6778242).sum := by decide
  have hdescent : baseEnd_6778242 < baseStart_6778242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778244 : List Nat := [2, 3, 2, 1, 1, 3, 2, 9]
def baseStart_6778244 : Nat := 118140960795 + 6778244 * 2 ^ 59
def prefixEnd_6778244 : Nat := 4983230072969 + 3 ^ 40 * 6778244 * 2
def baseEnd_6778244 : Nat := 128907302424232715662127

theorem tailTrace_6778244 : CollatzResearch.WordTrace tailWord_6778244 prefixEnd_6778244 128907302424232715662127 := by
  unfold tailWord_6778244
  simp only [CollatzResearch.WordTrace]
  refine ⟨123611434427793547378262893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164815245903724729837683857 123611434427793547378262893)
  ·
    refine ⟨46354287910422580266848585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123611434427793547378262893 46354287910422580266848585)
    ·
      refine ⟨34765715932816935200136439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46354287910422580266848585 34765715932816935200136439)
      ·
        refine ⟨52148573899225402800204659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34765715932816935200136439 52148573899225402800204659)
        ·
          refine ⟨78222860848838104200306989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52148573899225402800204659 78222860848838104200306989)
          ·
            refine ⟨29333572818314289075115121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78222860848838104200306989 29333572818314289075115121)
            ·
              refine ⟨22000179613735716806336341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29333572818314289075115121 22000179613735716806336341)
              ·
                refine ⟨128907302424232715662127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22000179613735716806336341 128907302424232715662127)
                ·
                  rfl

theorem cell23_6778244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 9].length) (baseStart_6778244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778244 prefixEnd_6778244 := by exact prefixLift 6778244
  have htrace : WordTrace (prefixWord ++ tailWord_6778244) baseStart_6778244 baseEnd_6778244 := by
    simpa [prefixWord, tailWord_6778244, baseEnd_6778244] using wordTrace_append hprefix tailTrace_6778244
  have hstable : (prefixWord ++ tailWord_6778244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778244).length < 2 ^ (prefixWord ++ tailWord_6778244).sum := by decide
  have hdescent : baseEnd_6778244 < baseStart_6778244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778315 : List Nat := [1, 1, 1, 1, 3, 3, 6, 1, 1, 3, 2]
def baseStart_6778315 : Nat := 118140960795 + 6778315 * 2 ^ 59
def prefixEnd_6778315 : Nat := 4983230072969 + 3 ^ 40 * 6778315 * 2
def baseEnd_6778315 : Nat := 3480533622580752545089603

theorem tailTrace_6778315 : CollatzResearch.WordTrace tailWord_6778315 prefixEnd_6778315 3480533622580752545089603 := by
  unfold tailWord_6778315
  simp only [CollatzResearch.WordTrace]
  refine ⟨247225458438329873882360399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164816972292219915921573599 247225458438329873882360399)
  ·
    refine ⟨370838187657494810823540599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247225458438329873882360399 370838187657494810823540599)
    ·
      refine ⟨556257281486242216235310899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370838187657494810823540599 556257281486242216235310899)
      ·
        refine ⟨834385922229363324352966349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556257281486242216235310899 834385922229363324352966349)
        ·
          refine ⟨312894720836011246632362381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 834385922229363324352966349 312894720836011246632362381)
          ·
            refine ⟨117335520313504217487135893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312894720836011246632362381 117335520313504217487135893)
            ·
              refine ⟨5500102514695510194709495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117335520313504217487135893 5500102514695510194709495)
              ·
                refine ⟨8250153772043265292064243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5500102514695510194709495 8250153772043265292064243)
                ·
                  refine ⟨12375230658064897938096365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8250153772043265292064243 12375230658064897938096365)
                  ·
                    refine ⟨4640711496774336726786137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12375230658064897938096365 4640711496774336726786137)
                    ·
                      refine ⟨3480533622580752545089603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640711496774336726786137 3480533622580752545089603)
                      ·
                        rfl

theorem cell23_6778315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 1, 3, 2].length) (baseStart_6778315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778315 prefixEnd_6778315 := by exact prefixLift 6778315
  have htrace : WordTrace (prefixWord ++ tailWord_6778315) baseStart_6778315 baseEnd_6778315 := by
    simpa [prefixWord, tailWord_6778315, baseEnd_6778315] using wordTrace_append hprefix tailTrace_6778315
  have hstable : (prefixWord ++ tailWord_6778315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778315).length < 2 ^ (prefixWord ++ tailWord_6778315).sum := by decide
  have hdescent : baseEnd_6778315 < baseStart_6778315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778418 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2]
def baseStart_6778418 : Nat := 118140960795 + 6778418 * 2 ^ 59
def prefixEnd_6778418 : Nat := 4983230072969 + 3 ^ 40 * 6778418 * 2
def baseEnd_6778418 : Nat := 3480586511088165642101629

theorem tailTrace_6778418 : CollatzResearch.WordTrace tailWord_6778418 prefixEnd_6778418 3480586511088165642101629 := by
  unfold tailWord_6778418
  simp only [CollatzResearch.WordTrace]
  refine ⟨61807303789239180618339977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164819476771304481648906605 61807303789239180618339977)
  ·
    refine ⟨46355477841929385463754983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61807303789239180618339977 46355477841929385463754983)
    ·
      refine ⟨69533216762894078195632475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46355477841929385463754983 69533216762894078195632475)
      ·
        refine ⟨104299825144341117293448713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69533216762894078195632475 104299825144341117293448713)
        ·
          refine ⟨78224868858255837970086535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104299825144341117293448713 78224868858255837970086535)
          ·
            refine ⟨117337303287383756955129803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78224868858255837970086535 117337303287383756955129803)
            ·
              refine ⟨176005954931075635432694705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117337303287383756955129803 176005954931075635432694705)
              ·
                refine ⟨132004466198306726574521029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176005954931075635432694705 132004466198306726574521029)
                ·
                  refine ⟨24750837412182511232722693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132004466198306726574521029 24750837412182511232722693)
                  ·
                    refine ⟨4640782014784220856135505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24750837412182511232722693 4640782014784220856135505)
                    ·
                      refine ⟨3480586511088165642101629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640782014784220856135505 3480586511088165642101629)
                      ·
                        rfl

theorem cell23_6778418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_6778418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778418 prefixEnd_6778418 := by exact prefixLift 6778418
  have htrace : WordTrace (prefixWord ++ tailWord_6778418) baseStart_6778418 baseEnd_6778418 := by
    simpa [prefixWord, tailWord_6778418, baseEnd_6778418] using wordTrace_append hprefix tailTrace_6778418
  have hstable : (prefixWord ++ tailWord_6778418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778418).length < 2 ^ (prefixWord ++ tailWord_6778418).sum := by decide
  have hdescent : baseEnd_6778418 < baseStart_6778418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778472 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_6778472 : Nat := 118140960795 + 6778472 * 2 ^ 59
def prefixEnd_6778472 : Nat := 4983230072969 + 3 ^ 40 * 6778472 * 2
def baseEnd_6778472 : Nat := 3480614239043508430826381

theorem tailTrace_6778472 : CollatzResearch.WordTrace tailWord_6778472 prefixEnd_6778472 3480614239043508430826381 := by
  unfold tailWord_6778472
  simp only [CollatzResearch.WordTrace]
  refine ⟨123615592349380544847912835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164820789799174059797217113 123615592349380544847912835)
  ·
    refine ⟨185423388524070817271869253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123615592349380544847912835 185423388524070817271869253)
    ·
      refine ⟨34766885348263278238475485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185423388524070817271869253 34766885348263278238475485)
      ·
        refine ⟨13037582005598729339428307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34766885348263278238475485 13037582005598729339428307)
        ·
          refine ⟨19556373008398094009142461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13037582005598729339428307 19556373008398094009142461)
          ·
            refine ⟨7333639878149285253428423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19556373008398094009142461 7333639878149285253428423)
            ·
              refine ⟨11000459817223927880142635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7333639878149285253428423 11000459817223927880142635)
              ·
                refine ⟨16500689725835891820213953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11000459817223927880142635 16500689725835891820213953)
                ·
                  refine ⟨12375517294376918865160465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16500689725835891820213953 12375517294376918865160465)
                  ·
                    refine ⟨9281637970782689148870349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12375517294376918865160465 9281637970782689148870349)
                    ·
                      refine ⟨3480614239043508430826381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9281637970782689148870349 3480614239043508430826381)
                      ·
                        rfl

theorem cell23_6778472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_6778472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778472 prefixEnd_6778472 := by exact prefixLift 6778472
  have htrace : WordTrace (prefixWord ++ tailWord_6778472) baseStart_6778472 baseEnd_6778472 := by
    simpa [prefixWord, tailWord_6778472, baseEnd_6778472] using wordTrace_append hprefix tailTrace_6778472
  have hstable : (prefixWord ++ tailWord_6778472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778472).length < 2 ^ (prefixWord ++ tailWord_6778472).sum := by decide
  have hdescent : baseEnd_6778472 < baseStart_6778472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778531 : List Nat := [1, 1, 1, 4, 1, 1, 5, 9]
def baseStart_6778531 : Nat := 118140960795 + 6778531 * 2 ^ 59
def prefixEnd_6778531 : Nat := 4983230072969 + 3 ^ 40 * 6778531 * 2
def baseEnd_6778531 : Nat := 128912760533411988888467

theorem tailTrace_6778531 : CollatzResearch.WordTrace tailWord_6778531 prefixEnd_6778531 128912760533411988888467 := by
  unfold tailWord_6778531
  simp only [CollatzResearch.WordTrace]
  refine ⟨247233336605547342772223447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164822224403698228514815631 247233336605547342772223447)
  ·
    refine ⟨370850004908321014158335171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247233336605547342772223447 370850004908321014158335171)
    ·
      refine ⟨556275007362481521237502757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370850004908321014158335171 556275007362481521237502757)
      ·
        refine ⟨104301563880465285232031767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 556275007362481521237502757 104301563880465285232031767)
        ·
          refine ⟨156452345820697927848047651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104301563880465285232031767 156452345820697927848047651)
          ·
            refine ⟨234678518731046891772071477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156452345820697927848047651 234678518731046891772071477)
            ·
              refine ⟨22001111131035646103631701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 234678518731046891772071477 22001111131035646103631701)
              ·
                refine ⟨128912760533411988888467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22001111131035646103631701 128912760533411988888467)
                ·
                  rfl

theorem cell23_6778531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 9].length) (baseStart_6778531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778531 prefixEnd_6778531 := by exact prefixLift 6778531
  have htrace : WordTrace (prefixWord ++ tailWord_6778531) baseStart_6778531 baseEnd_6778531 := by
    simpa [prefixWord, tailWord_6778531, baseEnd_6778531] using wordTrace_append hprefix tailTrace_6778531
  have hstable : (prefixWord ++ tailWord_6778531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778531).length < 2 ^ (prefixWord ++ tailWord_6778531).sum := by decide
  have hdescent : baseEnd_6778531 < baseStart_6778531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778602 : List Nat := [3, 1, 3, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_6778602 : Nat := 118140960795 + 6778602 * 2 ^ 59
def prefixEnd_6778602 : Nat := 4983230072969 + 3 ^ 40 * 6778602 * 2
def baseEnd_6778602 : Nat := 3480680991528592922200783

theorem tailTrace_6778602 : CollatzResearch.WordTrace tailWord_6778602 prefixEnd_6778602 3480680991528592922200783 := by
  unfold tailWord_6778602
  simp only [CollatzResearch.WordTrace]
  refine ⟨61808981547072530474514515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164823950792193414598705373 61808981547072530474514515)
  ·
    refine ⟨92713472320608795711771773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61808981547072530474514515 92713472320608795711771773)
    ·
      refine ⟨34767552120228298391914415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92713472320608795711771773 34767552120228298391914415)
      ·
        refine ⟨52151328180342447587871623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34767552120228298391914415 52151328180342447587871623)
        ·
          refine ⟨78226992270513671381807435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52151328180342447587871623 78226992270513671381807435)
          ·
            refine ⟨117340488405770507072711153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78226992270513671381807435 117340488405770507072711153)
            ·
              refine ⟨88005366304327880304533365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117340488405770507072711153 88005366304327880304533365)
              ·
                refine ⟨8250503091030738778550003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88005366304327880304533365 8250503091030738778550003)
                ·
                  refine ⟨12375754636546108167825005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8250503091030738778550003 12375754636546108167825005)
                  ·
                    refine ⟨4640907988704790562934377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12375754636546108167825005 4640907988704790562934377)
                    ·
                      refine ⟨3480680991528592922200783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640907988704790562934377 3480680991528592922200783)
                      ·
                        rfl

theorem cell23_6778602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_6778602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778602 prefixEnd_6778602 := by exact prefixLift 6778602
  have htrace : WordTrace (prefixWord ++ tailWord_6778602) baseStart_6778602 baseEnd_6778602 := by
    simpa [prefixWord, tailWord_6778602, baseEnd_6778602] using wordTrace_append hprefix tailTrace_6778602
  have hstable : (prefixWord ++ tailWord_6778602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778602).length < 2 ^ (prefixWord ++ tailWord_6778602).sum := by decide
  have hdescent : baseEnd_6778602 < baseStart_6778602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778612 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6778612 : Nat := 118140960795 + 6778612 * 2 ^ 59
def prefixEnd_6778612 : Nat := 4983230072969 + 3 ^ 40 * 6778612 * 2
def baseEnd_6778612 : Nat := 1160228708778379294358579

theorem tailTrace_6778612 : CollatzResearch.WordTrace tailWord_6778612 prefixEnd_6778612 1160228708778379294358579 := by
  unfold tailWord_6778612
  simp only [CollatzResearch.WordTrace]
  refine ⟨123618145459126946802961045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164824193945502595737281393 123618145459126946802961045)
  ·
    refine ⟨5794600568396575631388799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 123618145459126946802961045 5794600568396575631388799)
    ·
      refine ⟨8691900852594863447083199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5794600568396575631388799 8691900852594863447083199)
      ·
        refine ⟨13037851278892295170624799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8691900852594863447083199 13037851278892295170624799)
        ·
          refine ⟨19556776918338442755937199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13037851278892295170624799 19556776918338442755937199)
          ·
            refine ⟨29335165377507664133905799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19556776918338442755937199 29335165377507664133905799)
            ·
              refine ⟨44002748066261496200858699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29335165377507664133905799 44002748066261496200858699)
              ·
                refine ⟨66004122099392244301288049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44002748066261496200858699 66004122099392244301288049)
                ·
                  refine ⟨49503091574544183225966037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66004122099392244301288049 49503091574544183225966037)
                  ·
                    refine ⟨1160228708778379294358579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49503091574544183225966037 1160228708778379294358579)
                    ·
                      rfl

theorem cell23_6778612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6778612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778612 prefixEnd_6778612 := by exact prefixLift 6778612
  have htrace : WordTrace (prefixWord ++ tailWord_6778612) baseStart_6778612 baseEnd_6778612 := by
    simpa [prefixWord, tailWord_6778612, baseEnd_6778612] using wordTrace_append hprefix tailTrace_6778612
  have hstable : (prefixWord ++ tailWord_6778612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778612).length < 2 ^ (prefixWord ++ tailWord_6778612).sum := by decide
  have hdescent : baseEnd_6778612 < baseStart_6778612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778632 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 1, 4, 2]
def baseStart_6778632 : Nat := 118140960795 + 6778632 * 2 ^ 59
def prefixEnd_6778632 : Nat := 4983230072969 + 3 ^ 40 * 6778632 * 2
def baseEnd_6778632 : Nat := 3480696395948227804825645

theorem tailTrace_6778632 : CollatzResearch.WordTrace tailWord_6778632 prefixEnd_6778632 3480696395948227804825645 := by
  unfold tailWord_6778632
  simp only [CollatzResearch.WordTrace]
  refine ⟨123618510189090718510825075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164824680252120958014433433 123618510189090718510825075)
  ·
    refine ⟨185427765283636077766237613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123618510189090718510825075 185427765283636077766237613)
    ·
      refine ⟨69535411981363529162339105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185427765283636077766237613 69535411981363529162339105)
      ·
        refine ⟨52151558986022646871754329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69535411981363529162339105 52151558986022646871754329)
        ·
          refine ⟨39113669239516985153815747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52151558986022646871754329 39113669239516985153815747)
          ·
            refine ⟨58670503859275477730723621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39113669239516985153815747 58670503859275477730723621)
            ·
              refine ⟨11000719473614152074510679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58670503859275477730723621 11000719473614152074510679)
              ·
                refine ⟨16501079210421228111766019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11000719473614152074510679 16501079210421228111766019)
                ·
                  refine ⟨24751618815631842167649029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16501079210421228111766019 24751618815631842167649029)
                  ·
                    refine ⟨4640928527930970406434193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24751618815631842167649029 4640928527930970406434193)
                    ·
                      refine ⟨3480696395948227804825645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4640928527930970406434193 3480696395948227804825645)
                      ·
                        rfl

theorem cell23_6778632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_6778632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778632 prefixEnd_6778632 := by exact prefixLift 6778632
  have htrace : WordTrace (prefixWord ++ tailWord_6778632) baseStart_6778632 baseEnd_6778632 := by
    simpa [prefixWord, tailWord_6778632, baseEnd_6778632] using wordTrace_append hprefix tailTrace_6778632
  have hstable : (prefixWord ++ tailWord_6778632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778632).length < 2 ^ (prefixWord ++ tailWord_6778632).sum := by decide
  have hdescent : baseEnd_6778632 < baseStart_6778632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778638 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 9]
def baseStart_6778638 : Nat := 118140960795 + 6778638 * 2 ^ 59
def prefixEnd_6778638 : Nat := 4983230072969 + 3 ^ 40 * 6778638 * 2
def baseEnd_6778638 : Nat := 386744386314683864594513

theorem tailTrace_6778638 : CollatzResearch.WordTrace tailWord_6778638 prefixEnd_6778638 386744386314683864594513 := by
  unfold tailWord_6778638
  simp only [CollatzResearch.WordTrace]
  refine ⟨30904654902019962505796071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164824826144106466697579045 30904654902019962505796071)
  ·
    refine ⟨46356982353029943758694107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30904654902019962505796071 46356982353029943758694107)
    ·
      refine ⟨69535473529544915638041161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46356982353029943758694107 69535473529544915638041161)
      ·
        refine ⟨52151605147158686728530871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69535473529544915638041161 52151605147158686728530871)
        ·
          refine ⟨78227407720738030092796307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52151605147158686728530871 78227407720738030092796307)
          ·
            refine ⟨117341111581107045139194461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78227407720738030092796307 117341111581107045139194461)
            ·
              refine ⟨44002916842915141927197923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117341111581107045139194461 44002916842915141927197923)
              ·
                refine ⟨66004375264372712890796885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44002916842915141927197923 66004375264372712890796885)
                ·
                  refine ⟨386744386314683864594513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66004375264372712890796885 386744386314683864594513)
                  ·
                    rfl

theorem cell23_6778638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_6778638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778638 prefixEnd_6778638 := by exact prefixLift 6778638
  have htrace : WordTrace (prefixWord ++ tailWord_6778638) baseStart_6778638 baseEnd_6778638 := by
    simpa [prefixWord, tailWord_6778638, baseEnd_6778638] using wordTrace_append hprefix tailTrace_6778638
  have hstable : (prefixWord ++ tailWord_6778638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778638).length < 2 ^ (prefixWord ++ tailWord_6778638).sum := by decide
  have hdescent : baseEnd_6778638 < baseStart_6778638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778685 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_6778685 : Nat := 118140960795 + 6778685 * 2 ^ 59
def prefixEnd_6778685 : Nat := 4983230072969 + 3 ^ 40 * 6778685 * 2
def baseEnd_6778685 : Nat := 1160241203474305365820967

theorem tailTrace_6778685 : CollatzResearch.WordTrace tailWord_6778685 prefixEnd_6778685 1160241203474305365820967 := by
  unfold tailWord_6778685
  simp only [CollatzResearch.WordTrace]
  refine ⟨247238953446989427073329509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164825968964659618048886339 247238953446989427073329509)
  ·
    refine ⟨46357303771310517576249283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247238953446989427073329509 46357303771310517576249283)
    ·
      refine ⟨69535955656965776364373925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46357303771310517576249283 69535955656965776364373925)
      ·
        refine ⟨13037991685681083068320111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69535955656965776364373925 13037991685681083068320111)
        ·
          refine ⟨19556987528521624602480167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13037991685681083068320111 19556987528521624602480167)
          ·
            refine ⟨29335481292782436903720251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19556987528521624602480167 29335481292782436903720251)
            ·
              refine ⟨44003221939173655355580377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29335481292782436903720251 44003221939173655355580377)
              ·
                refine ⟨33002416454380241516685283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44003221939173655355580377 33002416454380241516685283)
                ·
                  refine ⟨49503624681570362275027925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33002416454380241516685283 49503624681570362275027925)
                  ·
                    refine ⟨1160241203474305365820967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49503624681570362275027925 1160241203474305365820967)
                    ·
                      rfl

theorem cell23_6778685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_6778685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778685 prefixEnd_6778685 := by exact prefixLift 6778685
  have htrace : WordTrace (prefixWord ++ tailWord_6778685) baseStart_6778685 baseEnd_6778685 := by
    simpa [prefixWord, tailWord_6778685, baseEnd_6778685] using wordTrace_append hprefix tailTrace_6778685
  have hstable : (prefixWord ++ tailWord_6778685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778685).length < 2 ^ (prefixWord ++ tailWord_6778685).sum := by decide
  have hdescent : baseEnd_6778685 < baseStart_6778685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778698 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 2, 8]
def baseStart_6778698 : Nat := 118140960795 + 6778698 * 2 ^ 59
def prefixEnd_6778698 : Nat := 4983230072969 + 3 ^ 40 * 6778698 * 2
def baseEnd_6778698 : Nat := 1160243428557141515533447

theorem tailTrace_6778698 : CollatzResearch.WordTrace tailWord_6778698 prefixEnd_6778698 1160243428557141515533447 := by
  unfold tailWord_6778698
  simp only [CollatzResearch.WordTrace]
  refine ⟨61809856898985582573388187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164826285063961553529035165 61809856898985582573388187)
  ·
    refine ⟨92714785348478373860082281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61809856898985582573388187 92714785348478373860082281)
    ·
      refine ⟨69536089011358780395061711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92714785348478373860082281 69536089011358780395061711)
      ·
        refine ⟨104304133517038170592592567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69536089011358780395061711 104304133517038170592592567)
        ·
          refine ⟨156456200275557255888888851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104304133517038170592592567 156456200275557255888888851)
          ·
            refine ⟨234684300413335883833333277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156456200275557255888888851 234684300413335883833333277)
            ·
              refine ⟨88006612655000956437499979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234684300413335883833333277 88006612655000956437499979)
              ·
                refine ⟨132009918982501434656249969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88006612655000956437499979 132009918982501434656249969)
                ·
                  refine ⟨99007439236876075992187477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132009918982501434656249969 99007439236876075992187477)
                  ·
                    refine ⟨1160243428557141515533447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99007439236876075992187477 1160243428557141515533447)
                    ·
                      rfl

theorem cell23_6778698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_6778698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778698 prefixEnd_6778698 := by exact prefixLift 6778698
  have htrace : WordTrace (prefixWord ++ tailWord_6778698) baseStart_6778698 baseEnd_6778698 := by
    simpa [prefixWord, tailWord_6778698, baseEnd_6778698] using wordTrace_append hprefix tailTrace_6778698
  have hstable : (prefixWord ++ tailWord_6778698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778698).length < 2 ^ (prefixWord ++ tailWord_6778698).sum := by decide
  have hdescent : baseEnd_6778698 < baseStart_6778698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778705 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_6778705 : Nat := 118140960795 + 6778705 * 2 ^ 59
def prefixEnd_6778705 : Nat := 4983230072969 + 3 ^ 40 * 6778705 * 2
def baseEnd_6778705 : Nat := 3480733880036006019212809

theorem tailTrace_6778705 : CollatzResearch.WordTrace tailWord_6778705 prefixEnd_6778705 3480733880036006019212809 := by
  unfold tailWord_6778705
  simp only [CollatzResearch.WordTrace]
  refine ⟨247239682906916970489057569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164826455271277980326038379 247239682906916970489057569)
  ·
    refine ⟨185429762180187727866793177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247239682906916970489057569 185429762180187727866793177)
    ·
      refine ⟨139072321635140795900094883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185429762180187727866793177 139072321635140795900094883)
      ·
        refine ⟨208608482452711193850142325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139072321635140795900094883 208608482452711193850142325)
        ·
          refine ⟨19557045229941674423450843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 208608482452711193850142325 19557045229941674423450843)
          ·
            refine ⟨29335567844912511635176265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19557045229941674423450843 29335567844912511635176265)
            ·
              refine ⟨22001675883684383726382199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29335567844912511635176265 22001675883684383726382199)
              ·
                refine ⟨33002513825526575589573299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22001675883684383726382199 33002513825526575589573299)
                ·
                  refine ⟨49503770738289863384359949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33002513825526575589573299 49503770738289863384359949)
                  ·
                    refine ⟨18563914026858698769134981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49503770738289863384359949 18563914026858698769134981)
                    ·
                      refine ⟨3480733880036006019212809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18563914026858698769134981 3480733880036006019212809)
                      ·
                        rfl

theorem cell23_6778705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_6778705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778705 prefixEnd_6778705 := by exact prefixLift 6778705
  have htrace : WordTrace (prefixWord ++ tailWord_6778705) baseStart_6778705 baseEnd_6778705 := by
    simpa [prefixWord, tailWord_6778705, baseEnd_6778705] using wordTrace_append hprefix tailTrace_6778705
  have hstable : (prefixWord ++ tailWord_6778705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778705).length < 2 ^ (prefixWord ++ tailWord_6778705).sum := by decide
  have hdescent : baseEnd_6778705 < baseStart_6778705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778722 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_6778722 : Nat := 118140960795 + 6778722 * 2 ^ 59
def prefixEnd_6778722 : Nat := 4983230072969 + 3 ^ 40 * 6778722 * 2
def baseEnd_6778722 : Nat := 3480742609207132452700231

theorem tailTrace_6778722 : CollatzResearch.WordTrace tailWord_6778722 prefixEnd_6778722 3480742609207132452700231 := by
  unfold tailWord_6778722
  simp only [CollatzResearch.WordTrace]
  refine ⟨61810075736963845598106605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164826868631903588261617613 61810075736963845598106605)
  ·
    refine ⟨23178778401361442099289977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61810075736963845598106605 23178778401361442099289977)
    ·
      refine ⟨17384083801021081574467483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23178778401361442099289977 17384083801021081574467483)
      ·
        refine ⟨26076125701531622361701225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17384083801021081574467483 26076125701531622361701225)
        ·
          refine ⟨19557094276148716771275919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26076125701531622361701225 19557094276148716771275919)
          ·
            refine ⟨29335641414223075156913879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19557094276148716771275919 29335641414223075156913879)
            ·
              refine ⟨44003462121334612735370819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29335641414223075156913879 44003462121334612735370819)
              ·
                refine ⟨66005193182001919103056229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44003462121334612735370819 66005193182001919103056229)
                ·
                  refine ⟨12375973721625359831823043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66005193182001919103056229 12375973721625359831823043)
                  ·
                    refine ⟨18563960582438039747734565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12375973721625359831823043 18563960582438039747734565)
                    ·
                      refine ⟨3480742609207132452700231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18563960582438039747734565 3480742609207132452700231)
                      ·
                        rfl

theorem cell23_6778722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_6778722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778722 prefixEnd_6778722 := by exact prefixLift 6778722
  have htrace : WordTrace (prefixWord ++ tailWord_6778722) baseStart_6778722 baseEnd_6778722 := by
    simpa [prefixWord, tailWord_6778722, baseEnd_6778722] using wordTrace_append hprefix tailTrace_6778722
  have hstable : (prefixWord ++ tailWord_6778722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778722).length < 2 ^ (prefixWord ++ tailWord_6778722).sum := by decide
  have hdescent : baseEnd_6778722 < baseStart_6778722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778732 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 3, 4]
def baseStart_6778732 : Nat := 118140960795 + 6778732 * 2 ^ 59
def prefixEnd_6778732 : Nat := 4983230072969 + 3 ^ 40 * 6778732 * 2
def baseEnd_6778732 : Nat := 1160249248004559137858395

theorem tailTrace_6778732 : CollatzResearch.WordTrace tailWord_6778732 prefixEnd_6778732 1160249248004559137858395 := by
  unfold tailWord_6778732
  simp only [CollatzResearch.WordTrace]
  refine ⟨123620333838909577050145225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164827111785212769400193633 123620333838909577050145225)
  ·
    refine ⟨92715250379182182787608919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123620333838909577050145225 92715250379182182787608919)
    ·
      refine ⟨139072875568773274181413379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92715250379182182787608919 139072875568773274181413379)
      ·
        refine ⟨208609313353159911272120069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139072875568773274181413379 208609313353159911272120069)
        ·
          refine ⟨39114246253717483363522513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208609313353159911272120069 39114246253717483363522513)
          ·
            refine ⟨29335684690288112522641885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39114246253717483363522513 29335684690288112522641885)
            ·
              refine ⟨11000881758858042195990707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29335684690288112522641885 11000881758858042195990707)
              ·
                refine ⟨16501322638287063293986061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11000881758858042195990707 16501322638287063293986061)
                ·
                  refine ⟨6187995989357648735244773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16501322638287063293986061 6187995989357648735244773)
                  ·
                    refine ⟨1160249248004559137858395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6187995989357648735244773 1160249248004559137858395)
                    ·
                      rfl

theorem cell23_6778732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_6778732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778732 prefixEnd_6778732 := by exact prefixLift 6778732
  have htrace : WordTrace (prefixWord ++ tailWord_6778732) baseStart_6778732 baseEnd_6778732 := by
    simpa [prefixWord, tailWord_6778732, baseEnd_6778732] using wordTrace_append hprefix tailTrace_6778732
  have hstable : (prefixWord ++ tailWord_6778732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778732).length < 2 ^ (prefixWord ++ tailWord_6778732).sum := by decide
  have hdescent : baseEnd_6778732 < baseStart_6778732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778745 : List Nat := [1, 2, 1, 3, 2, 2, 3, 3, 6]
def baseStart_6778745 : Nat := 118140960795 + 6778745 * 2 ^ 59
def prefixEnd_6778745 : Nat := 4983230072969 + 3 ^ 40 * 6778745 * 2
def baseEnd_6778745 : Nat := 386750491029131762523625

theorem tailTrace_6778745 : CollatzResearch.WordTrace tailWord_6778745 prefixEnd_6778745 386750491029131762523625 := by
  unfold tailWord_6778745
  simp only [CollatzResearch.WordTrace]
  refine ⟨247241141826772057320513689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164827427884514704880342459 247241141826772057320513689)
  ·
    refine ⟨185430856370079042990385267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247241141826772057320513689 185430856370079042990385267)
    ·
      refine ⟨278146284555118564485577901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185430856370079042990385267 278146284555118564485577901)
      ·
        refine ⟨104304856708169461682091713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278146284555118564485577901 104304856708169461682091713)
        ·
          refine ⟨78228642531127096261568785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104304856708169461682091713 78228642531127096261568785)
          ·
            refine ⟨58671481898345322196176589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78228642531127096261568785 58671481898345322196176589)
            ·
              refine ⟨22001805711879495823566221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58671481898345322196176589 22001805711879495823566221)
              ·
                refine ⟨8250677141954810933837333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22001805711879495823566221 8250677141954810933837333)
                ·
                  refine ⟨386750491029131762523625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8250677141954810933837333 386750491029131762523625)
                  ·
                    rfl

theorem cell23_6778745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 6].length) (baseStart_6778745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778745 prefixEnd_6778745 := by exact prefixLift 6778745
  have htrace : WordTrace (prefixWord ++ tailWord_6778745) baseStart_6778745 baseEnd_6778745 := by
    simpa [prefixWord, tailWord_6778745, baseEnd_6778745] using wordTrace_append hprefix tailTrace_6778745
  have hstable : (prefixWord ++ tailWord_6778745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778745).length < 2 ^ (prefixWord ++ tailWord_6778745).sum := by decide
  have hdescent : baseEnd_6778745 < baseStart_6778745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778759 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_6778759 : Nat := 118140960795 + 6778759 * 2 ^ 59
def prefixEnd_6778759 : Nat := 4983230072969 + 3 ^ 40 * 6778759 * 2
def baseEnd_6778759 : Nat := 3480761607991348807937561

theorem tailTrace_6778759 : CollatzResearch.WordTrace tailWord_6778759 prefixEnd_6778759 3480761607991348807937561 := by
  unfold tailWord_6778759
  simp only [CollatzResearch.WordTrace]
  refine ⟨247241652448721337711523331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164827768299147558474348887 247241652448721337711523331)
  ·
    refine ⟨370862478673082006567284997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247241652448721337711523331 370862478673082006567284997)
    ·
      refine ⟨69536714751202876231365937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370862478673082006567284997 69536714751202876231365937)
      ·
        refine ⟨52152536063402157173524453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69536714751202876231365937 52152536063402157173524453)
        ·
          refine ⟨9778600511887904470035835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52152536063402157173524453 9778600511887904470035835)
          ·
            refine ⟨14667900767831856705053753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9778600511887904470035835 14667900767831856705053753)
            ·
              refine ⟨11000925575873892528790315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14667900767831856705053753 11000925575873892528790315)
              ·
                refine ⟨16501388363810838793185473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11000925575873892528790315 16501388363810838793185473)
                ·
                  refine ⟨12376041272858129094889105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16501388363810838793185473 12376041272858129094889105)
                  ·
                    refine ⟨9282030954643596821166829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12376041272858129094889105 9282030954643596821166829)
                    ·
                      refine ⟨3480761607991348807937561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9282030954643596821166829 3480761607991348807937561)
                      ·
                        rfl

theorem cell23_6778759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_6778759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778759 prefixEnd_6778759 := by exact prefixLift 6778759
  have htrace : WordTrace (prefixWord ++ tailWord_6778759) baseStart_6778759 baseEnd_6778759 := by
    simpa [prefixWord, tailWord_6778759, baseEnd_6778759] using wordTrace_append hprefix tailTrace_6778759
  have hstable : (prefixWord ++ tailWord_6778759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778759).length < 2 ^ (prefixWord ++ tailWord_6778759).sum := by decide
  have hdescent : baseEnd_6778759 < baseStart_6778759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778783 : List Nat := [1, 1, 2, 5, 3, 2, 2, 2, 1, 4]
def baseStart_6778783 : Nat := 118140960795 + 6778783 * 2 ^ 59
def prefixEnd_6778783 : Nat := 4983230072969 + 3 ^ 40 * 6778783 * 2
def baseEnd_6778783 : Nat := 1160257977175685571345817

theorem tailTrace_6778783 : CollatzResearch.WordTrace tailWord_6778783 prefixEnd_6778783 1160257977175685571345817 := by
  unfold tailWord_6778783
  simp only [CollatzResearch.WordTrace]
  refine ⟨247242527800634389810397003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164828351867089593206931335 247242527800634389810397003)
  ·
    refine ⟨370863791700951584715595505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247242527800634389810397003 370863791700951584715595505)
    ·
      refine ⟨278147843775713688536696629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370863791700951584715595505 278147843775713688536696629)
      ·
        refine ⟨26076360353973158300315309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 278147843775713688536696629 26076360353973158300315309)
        ·
          refine ⟨9778635132739934362618241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26076360353973158300315309 9778635132739934362618241)
          ·
            refine ⟨7333976349554950771963681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9778635132739934362618241 7333976349554950771963681)
            ·
              refine ⟨5500482262166213078972761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7333976349554950771963681 5500482262166213078972761)
              ·
                refine ⟨4125361696624659809229571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5500482262166213078972761 4125361696624659809229571)
                ·
                  refine ⟨6188042544936989713844357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125361696624659809229571 6188042544936989713844357)
                  ·
                    refine ⟨1160257977175685571345817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6188042544936989713844357 1160257977175685571345817)
                    ·
                      rfl

theorem cell23_6778783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 1, 4].length) (baseStart_6778783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778783 prefixEnd_6778783 := by exact prefixLift 6778783
  have htrace : WordTrace (prefixWord ++ tailWord_6778783) baseStart_6778783 baseEnd_6778783 := by
    simpa [prefixWord, tailWord_6778783, baseEnd_6778783] using wordTrace_append hprefix tailTrace_6778783
  have hstable : (prefixWord ++ tailWord_6778783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778783).length < 2 ^ (prefixWord ++ tailWord_6778783).sum := by decide
  have hdescent : baseEnd_6778783 < baseStart_6778783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778875 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 5]
def baseStart_6778875 : Nat := 118140960795 + 6778875 * 2 ^ 59
def prefixEnd_6778875 : Nat := 4983230072969 + 3 ^ 40 * 6778875 * 2
def baseEnd_6778875 : Nat := 3480821171747270354087027

theorem tailTrace_6778875 : CollatzResearch.WordTrace tailWord_6778875 prefixEnd_6778875 3480821171747270354087027 := by
  unfold tailWord_6778875
  simp only [CollatzResearch.WordTrace]
  refine ⟨247245883316301089522746079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164830588877534059681830719 247245883316301089522746079)
  ·
    refine ⟨370868824974451634284119119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247245883316301089522746079 370868824974451634284119119)
    ·
      refine ⟨556303237461677451426178679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370868824974451634284119119 556303237461677451426178679)
      ·
        refine ⟨834454856192516177139268019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556303237461677451426178679 834454856192516177139268019)
        ·
          refine ⟨1251682284288774265708902029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834454856192516177139268019 1251682284288774265708902029)
          ·
            refine ⟨469380856608290349640838261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1251682284288774265708902029 469380856608290349640838261)
            ·
              refine ⟨44004455307027220278828587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 469380856608290349640838261 44004455307027220278828587)
              ·
                refine ⟨66006682960540830418242881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44004455307027220278828587 66006682960540830418242881)
                ·
                  refine ⟨49505012220405622813682161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66006682960540830418242881 49505012220405622813682161)
                  ·
                    refine ⟨37128759165304217110261621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49505012220405622813682161 37128759165304217110261621)
                    ·
                      refine ⟨3480821171747270354087027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37128759165304217110261621 3480821171747270354087027)
                      ·
                        rfl

theorem cell23_6778875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_6778875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778875 prefixEnd_6778875 := by exact prefixLift 6778875
  have htrace : WordTrace (prefixWord ++ tailWord_6778875) baseStart_6778875 baseEnd_6778875 := by
    simpa [prefixWord, tailWord_6778875, baseEnd_6778875] using wordTrace_append hprefix tailTrace_6778875
  have hstable : (prefixWord ++ tailWord_6778875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778875).length < 2 ^ (prefixWord ++ tailWord_6778875).sum := by decide
  have hdescent : baseEnd_6778875 < baseStart_6778875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778905 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 5]
def baseStart_6778905 : Nat := 118140960795 + 6778905 * 2 ^ 59
def prefixEnd_6778905 : Nat := 4983230072969 + 3 ^ 40 * 6778905 * 2
def baseEnd_6778905 : Nat := 3480836576166905236711889

theorem tailTrace_6778905 : CollatzResearch.WordTrace tailWord_6778905 prefixEnd_6778905 3480836576166905236711889 := by
  unfold tailWord_6778905
  simp only [CollatzResearch.WordTrace]
  refine ⟨247246977506192404646338169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164831318337461603097558779 247246977506192404646338169)
  ·
    refine ⟨185435233129644303484753627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247246977506192404646338169 185435233129644303484753627)
    ·
      refine ⟨278152849694466455227130441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185435233129644303484753627 278152849694466455227130441)
      ·
        refine ⟨208614637270849841420347831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278152849694466455227130441 208614637270849841420347831)
        ·
          refine ⟨312921955906274762130521747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208614637270849841420347831 312921955906274762130521747)
          ·
            refine ⟨469382933859412143195782621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312921955906274762130521747 469382933859412143195782621)
            ·
              refine ⟨176018600197279553698418483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 469382933859412143195782621 176018600197279553698418483)
              ·
                refine ⟨264027900295919330547627725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176018600197279553698418483 264027900295919330547627725)
                ·
                  refine ⟨99010462610969748955360397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264027900295919330547627725 99010462610969748955360397)
                  ·
                    refine ⟨37128923479113655858260149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99010462610969748955360397 37128923479113655858260149)
                    ·
                      refine ⟨3480836576166905236711889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37128923479113655858260149 3480836576166905236711889)
                      ·
                        rfl

theorem cell23_6778905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_6778905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778905 prefixEnd_6778905 := by exact prefixLift 6778905
  have htrace : WordTrace (prefixWord ++ tailWord_6778905) baseStart_6778905 baseEnd_6778905 := by
    simpa [prefixWord, tailWord_6778905, baseEnd_6778905] using wordTrace_append hprefix tailTrace_6778905
  have hstable : (prefixWord ++ tailWord_6778905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778905).length < 2 ^ (prefixWord ++ tailWord_6778905).sum := by decide
  have hdescent : baseEnd_6778905 < baseStart_6778905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778936 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 1, 4, 2]
def baseStart_6778936 : Nat := 118140960795 + 6778936 * 2 ^ 59
def prefixEnd_6778936 : Nat := 4983230072969 + 3 ^ 40 * 6778936 * 2
def baseEnd_6778936 : Nat := 3480852494067194615424247

theorem tailTrace_6778936 : CollatzResearch.WordTrace tailWord_6778936 prefixEnd_6778936 3480852494067194615424247 := by
  unfold tailWord_6778936
  simp only [CollatzResearch.WordTrace]
  refine ⟨123624054084540048470358331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164832072112720064627144441 123624054084540048470358331)
  ·
    refine ⟨185436081126810072705537497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123624054084540048470358331 185436081126810072705537497)
    ·
      refine ⟨139077060845107554529153123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185436081126810072705537497 139077060845107554529153123)
      ·
        refine ⟨208615591267661331793729685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139077060845107554529153123 208615591267661331793729685)
        ·
          refine ⟨9778855840671624927831079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 208615591267661331793729685 9778855840671624927831079)
          ·
            refine ⟨14668283761007437391746619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9778855840671624927831079 14668283761007437391746619)
            ·
              refine ⟨22002425641511156087619929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14668283761007437391746619 22002425641511156087619929)
              ·
                refine ⟨16501819231133367065714947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22002425641511156087619929 16501819231133367065714947)
                ·
                  refine ⟨24752728846700050598572421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16501819231133367065714947 24752728846700050598572421)
                  ·
                    refine ⟨4641136658756259487232329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24752728846700050598572421 4641136658756259487232329)
                    ·
                      refine ⟨3480852494067194615424247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4641136658756259487232329 3480852494067194615424247)
                      ·
                        rfl

theorem cell23_6778936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 4, 2].length) (baseStart_6778936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778936 prefixEnd_6778936 := by exact prefixLift 6778936
  have htrace : WordTrace (prefixWord ++ tailWord_6778936) baseStart_6778936 baseEnd_6778936 := by
    simpa [prefixWord, tailWord_6778936, baseEnd_6778936] using wordTrace_append hprefix tailTrace_6778936
  have hstable : (prefixWord ++ tailWord_6778936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778936).length < 2 ^ (prefixWord ++ tailWord_6778936).sum := by decide
  have hdescent : baseEnd_6778936 < baseStart_6778936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6778966 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_6778966 : Nat := 118140960795 + 6778966 * 2 ^ 59
def prefixEnd_6778966 : Nat := 4983230072969 + 3 ^ 40 * 6778966 * 2
def baseEnd_6778966 : Nat := 3480867898486829498049109

theorem tailTrace_6778966 : CollatzResearch.WordTrace tailWord_6778966 prefixEnd_6778966 3480867898486829498049109 := by
  unfold tailWord_6778966
  simp only [CollatzResearch.WordTrace]
  refine ⟨15453075147435713254019297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164832801572647608042872501 15453075147435713254019297)
  ·
    refine ⟨11589806360576784940514473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15453075147435713254019297 11589806360576784940514473)
    ·
      refine ⟨8692354770432588705385855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11589806360576784940514473 8692354770432588705385855)
      ·
        refine ⟨13038532155648883058078783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8692354770432588705385855 13038532155648883058078783)
        ·
          refine ⟨19557798233473324587118175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13038532155648883058078783 19557798233473324587118175)
          ·
            refine ⟨29336697350209986880677263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19557798233473324587118175 29336697350209986880677263)
            ·
              refine ⟨44005046025314980321015895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29336697350209986880677263 44005046025314980321015895)
              ·
                refine ⟨66007569037972470481523843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44005046025314980321015895 66007569037972470481523843)
                ·
                  refine ⟨99011353556958705722285765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66007569037972470481523843 99011353556958705722285765)
                  ·
                    refine ⟨18564628791929757322928581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99011353556958705722285765 18564628791929757322928581)
                    ·
                      refine ⟨3480867898486829498049109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18564628791929757322928581 3480867898486829498049109)
                      ·
                        rfl

theorem cell23_6778966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_6778966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6778966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6778966 prefixEnd_6778966 := by exact prefixLift 6778966
  have htrace : WordTrace (prefixWord ++ tailWord_6778966) baseStart_6778966 baseEnd_6778966 := by
    simpa [prefixWord, tailWord_6778966, baseEnd_6778966] using wordTrace_append hprefix tailTrace_6778966
  have hstable : (prefixWord ++ tailWord_6778966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6778966).length < 2 ^ (prefixWord ++ tailWord_6778966).sum := by decide
  have hdescent : baseEnd_6778966 < baseStart_6778966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6778966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779026 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_6779026 : Nat := 118140960795 + 6779026 * 2 ^ 59
def prefixEnd_6779026 : Nat := 4983230072969 + 3 ^ 40 * 6779026 * 2
def baseEnd_6779026 : Nat := 3480898707326099263298833

theorem tailTrace_6779026 : CollatzResearch.WordTrace tailWord_6779026 prefixEnd_6779026 3480898707326099263298833 := by
  unfold tailWord_6779026
  simp only [CollatzResearch.WordTrace]
  refine ⟨61812847684688510577873233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164834260492502694874328621 61812847684688510577873233)
  ·
    refine ⟨46359635763516382933404925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61812847684688510577873233 46359635763516382933404925)
    ·
      refine ⟨17384863411318643600026847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46359635763516382933404925 17384863411318643600026847)
      ·
        refine ⟨26077295116977965400040271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17384863411318643600026847 26077295116977965400040271)
        ·
          refine ⟨39115942675466948100060407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26077295116977965400040271 39115942675466948100060407)
          ·
            refine ⟨58673914013200422150090611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39115942675466948100060407 58673914013200422150090611)
            ·
              refine ⟨88010871019800633225135917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58673914013200422150090611 88010871019800633225135917)
              ·
                refine ⟨33004076632425237459425969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88010871019800633225135917 33004076632425237459425969)
                ·
                  refine ⟨24753057474318928094569477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33004076632425237459425969 24753057474318928094569477)
                  ·
                    refine ⟨4641198276434799017731777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24753057474318928094569477 4641198276434799017731777)
                    ·
                      refine ⟨3480898707326099263298833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4641198276434799017731777 3480898707326099263298833)
                      ·
                        rfl

theorem cell23_6779026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_6779026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779026 prefixEnd_6779026 := by exact prefixLift 6779026
  have htrace : WordTrace (prefixWord ++ tailWord_6779026) baseStart_6779026 baseEnd_6779026 := by
    simpa [prefixWord, tailWord_6779026, baseEnd_6779026] using wordTrace_append hprefix tailTrace_6779026
  have hstable : (prefixWord ++ tailWord_6779026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779026).length < 2 ^ (prefixWord ++ tailWord_6779026).sum := by decide
  have hdescent : baseEnd_6779026 < baseStart_6779026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779070 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_6779070 : Nat := 118140960795 + 6779070 * 2 ^ 59
def prefixEnd_6779070 : Nat := 4983230072969 + 3 ^ 40 * 6779070 * 2
def baseEnd_6779070 : Nat := 1160307100158299030382877

theorem tailTrace_6779070 : CollatzResearch.WordTrace tailWord_6779070 prefixEnd_6779070 1160307100158299030382877 := by
  unfold tailWord_6779070
  simp only [CollatzResearch.WordTrace]
  refine ⟨30906624443824329728261833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164835330367063091884063109 30906624443824329728261833)
  ·
    refine ⟨23179968332868247296196375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30906624443824329728261833 23179968332868247296196375)
    ·
      refine ⟨34769952499302370944294563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23179968332868247296196375 34769952499302370944294563)
      ·
        refine ⟨52154928748953556416441845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34769952499302370944294563 52154928748953556416441845)
        ·
          refine ⟨4889524570214395914041423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52154928748953556416441845 4889524570214395914041423)
          ·
            refine ⟨7334286855321593871062135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889524570214395914041423 7334286855321593871062135)
            ·
              refine ⟨11001430282982390806593203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7334286855321593871062135 11001430282982390806593203)
              ·
                refine ⟨16502145424473586209889805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11001430282982390806593203 16502145424473586209889805)
                ·
                  refine ⟨6188304534177594828708677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16502145424473586209889805 6188304534177594828708677)
                  ·
                    refine ⟨1160307100158299030382877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6188304534177594828708677 1160307100158299030382877)
                    ·
                      rfl

theorem cell23_6779070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_6779070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779070 prefixEnd_6779070 := by exact prefixLift 6779070
  have htrace : WordTrace (prefixWord ++ tailWord_6779070) baseStart_6779070 baseEnd_6779070 := by
    simpa [prefixWord, tailWord_6779070, baseEnd_6779070] using wordTrace_append hprefix tailTrace_6779070
  have hstable : (prefixWord ++ tailWord_6779070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779070).length < 2 ^ (prefixWord ++ tailWord_6779070).sum := by decide
  have hdescent : baseEnd_6779070 < baseStart_6779070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779096 : List Nat := [2, 1, 2, 2, 4, 1, 3, 2, 1, 5]
def baseStart_6779096 : Nat := 118140960795 + 6779096 * 2 ^ 59
def prefixEnd_6779096 : Nat := 4983230072969 + 3 ^ 40 * 6779096 * 2
def baseEnd_6779096 : Nat := 1160311550323971329807837

theorem tailTrace_6779096 : CollatzResearch.WordTrace tailWord_6779096 prefixEnd_6779096 1160311550323971329807837 := by
  unfold tailWord_6779096
  simp only [CollatzResearch.WordTrace]
  refine ⟨123626971924250222133270571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164835962565666962844360761 123626971924250222133270571)
  ·
    refine ⟨185440457886375333199905857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123626971924250222133270571 185440457886375333199905857)
    ·
      refine ⟨139080343414781499899929393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185440457886375333199905857 139080343414781499899929393)
      ·
        refine ⟨104310257561086124924947045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139080343414781499899929393 104310257561086124924947045)
        ·
          refine ⟨19558173292703648423427571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104310257561086124924947045 19558173292703648423427571)
          ·
            refine ⟨29337259939055472635141357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19558173292703648423427571 29337259939055472635141357)
            ·
              refine ⟨11001472477145802238178009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29337259939055472635141357 11001472477145802238178009)
              ·
                refine ⟨8251104357859351678633507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11001472477145802238178009 8251104357859351678633507)
                ·
                  refine ⟨12376656536789027517950261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8251104357859351678633507 12376656536789027517950261)
                  ·
                    refine ⟨1160311550323971329807837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12376656536789027517950261 1160311550323971329807837)
                    ·
                      rfl

theorem cell23_6779096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_6779096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779096 prefixEnd_6779096 := by exact prefixLift 6779096
  have htrace : WordTrace (prefixWord ++ tailWord_6779096) baseStart_6779096 baseEnd_6779096 := by
    simpa [prefixWord, tailWord_6779096, baseEnd_6779096] using wordTrace_append hprefix tailTrace_6779096
  have hstable : (prefixWord ++ tailWord_6779096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779096).length < 2 ^ (prefixWord ++ tailWord_6779096).sum := by decide
  have hdescent : baseEnd_6779096 < baseStart_6779096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779099 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 1, 8, 2]
def baseStart_6779099 : Nat := 118140960795 + 6779099 * 2 ^ 59
def prefixEnd_6779099 : Nat := 4983230072969 + 3 ^ 40 * 6779099 * 2
def baseEnd_6779099 : Nat := 3480936191413877477685997

theorem tailTrace_6779099 : CollatzResearch.WordTrace tailWord_6779099 prefixEnd_6779099 3480936191413877477685997 := by
  unfold tailWord_6779099
  simp only [CollatzResearch.WordTrace]
  refine ⟨247254053267489575778900351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164836035511659717185933567 247254053267489575778900351)
  ·
    refine ⟨370881079901234363668350527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247254053267489575778900351 370881079901234363668350527)
    ·
      refine ⟨556321619851851545502525791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370881079901234363668350527 556321619851851545502525791)
      ·
        refine ⟨834482429777777318253788687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556321619851851545502525791 834482429777777318253788687)
        ·
          refine ⟨1251723644666665977380683031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834482429777777318253788687 1251723644666665977380683031)
          ·
            refine ⟨1877585466999998966071024547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251723644666665977380683031 1877585466999998966071024547)
            ·
              refine ⟨2816378200499998449106536821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877585466999998966071024547 2816378200499998449106536821)
              ·
                refine ⟨264035456296874854603737827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2816378200499998449106536821 264035456296874854603737827)
                ·
                  refine ⟨396053184445312281905606741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264035456296874854603737827 396053184445312281905606741)
                  ·
                    refine ⟨4641248255218503303581329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 396053184445312281905606741 4641248255218503303581329)
                    ·
                      refine ⟨3480936191413877477685997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4641248255218503303581329 3480936191413877477685997)
                      ·
                        rfl

theorem cell23_6779099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 8, 2].length) (baseStart_6779099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779099 prefixEnd_6779099 := by exact prefixLift 6779099
  have htrace : WordTrace (prefixWord ++ tailWord_6779099) baseStart_6779099 baseEnd_6779099 := by
    simpa [prefixWord, tailWord_6779099, baseEnd_6779099] using wordTrace_append hprefix tailTrace_6779099
  have hstable : (prefixWord ++ tailWord_6779099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779099).length < 2 ^ (prefixWord ++ tailWord_6779099).sum := by decide
  have hdescent : baseEnd_6779099 < baseStart_6779099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779109 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 3, 6]
def baseStart_6779109 : Nat := 118140960795 + 6779109 * 2 ^ 59
def prefixEnd_6779109 : Nat := 4983230072969 + 3 ^ 40 * 6779109 * 2
def baseEnd_6779109 : Nat := 1160313775406807479520317

theorem tailTrace_6779109 : CollatzResearch.WordTrace tailWord_6779109 prefixEnd_6779109 1160313775406807479520317 := by
  unfold tailWord_6779109
  simp only [CollatzResearch.WordTrace]
  refine ⟨247254417997453347486764381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164836278664968898324509587 247254417997453347486764381)
  ·
    refine ⟨92720406749045005307536643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247254417997453347486764381 92720406749045005307536643)
    ·
      refine ⟨139080610123567507961304965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92720406749045005307536643 139080610123567507961304965)
      ·
        refine ⟨26077614398168907742744681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139080610123567507961304965 26077614398168907742744681)
        ·
          refine ⟨19558210798626680807058511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26077614398168907742744681 19558210798626680807058511)
          ·
            refine ⟨29337316197940021210587767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19558210798626680807058511 29337316197940021210587767)
            ·
              refine ⟨44005974296910031815881651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29337316197940021210587767 44005974296910031815881651)
              ·
                refine ⟨66008961445365047723822477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44005974296910031815881651 66008961445365047723822477)
                ·
                  refine ⟨24753360542011892896433429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66008961445365047723822477 24753360542011892896433429)
                  ·
                    refine ⟨1160313775406807479520317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24753360542011892896433429 1160313775406807479520317)
                    ·
                      rfl

theorem cell23_6779109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_6779109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779109 prefixEnd_6779109 := by exact prefixLift 6779109
  have htrace : WordTrace (prefixWord ++ tailWord_6779109) baseStart_6779109 baseEnd_6779109 := by
    simpa [prefixWord, tailWord_6779109, baseEnd_6779109] using wordTrace_append hprefix tailTrace_6779109
  have hstable : (prefixWord ++ tailWord_6779109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779109).length < 2 ^ (prefixWord ++ tailWord_6779109).sum := by decide
  have hdescent : baseEnd_6779109 < baseStart_6779109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779126 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_6779126 : Nat := 118140960795 + 6779126 * 2 ^ 59
def prefixEnd_6779126 : Nat := 4983230072969 + 3 ^ 40 * 6779126 * 2
def baseEnd_6779126 : Nat := 1160316685130516290682791

theorem tailTrace_6779126 : CollatzResearch.WordTrace tailWord_6779126 prefixEnd_6779126 1160316685130516290682791 := by
  unfold tailWord_6779126
  simp only [CollatzResearch.WordTrace]
  refine ⟨15453439877399484961883327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164836692025594506260088821 15453439877399484961883327)
  ·
    refine ⟨23180159816099227442824991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15453439877399484961883327 23180159816099227442824991)
    ·
      refine ⟨34770239724148841164237487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23180159816099227442824991 34770239724148841164237487)
      ·
        refine ⟨52155359586223261746356231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34770239724148841164237487 52155359586223261746356231)
        ·
          refine ⟨78233039379334892619534347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52155359586223261746356231 78233039379334892619534347)
          ·
            refine ⟨117349559069002338929301521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78233039379334892619534347 117349559069002338929301521)
            ·
              refine ⟨88012169301751754196976141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117349559069002338929301521 88012169301751754196976141)
              ·
                refine ⟨33004563488156907823866053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88012169301751754196976141 33004563488156907823866053)
                ·
                  refine ⟨6188355654029420216974885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33004563488156907823866053 6188355654029420216974885)
                  ·
                    refine ⟨1160316685130516290682791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6188355654029420216974885 1160316685130516290682791)
                    ·
                      rfl

theorem cell23_6779126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_6779126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779126 prefixEnd_6779126 := by exact prefixLift 6779126
  have htrace : WordTrace (prefixWord ++ tailWord_6779126) baseStart_6779126 baseEnd_6779126 := by
    simpa [prefixWord, tailWord_6779126, baseEnd_6779126] using wordTrace_append hprefix tailTrace_6779126
  have hstable : (prefixWord ++ tailWord_6779126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779126).length < 2 ^ (prefixWord ++ tailWord_6779126).sum := by decide
  have hdescent : baseEnd_6779126 < baseStart_6779126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779143 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 1, 6]
def baseStart_6779143 : Nat := 118140960795 + 6779143 * 2 ^ 59
def prefixEnd_6779143 : Nat := 4983230072969 + 3 ^ 40 * 6779143 * 2
def baseEnd_6779143 : Nat := 1160319594854225101845265

theorem tailTrace_6779143 : CollatzResearch.WordTrace tailWord_6779143 prefixEnd_6779143 1160319594854225101845265 := by
  unfold tailWord_6779143
  simp only [CollatzResearch.WordTrace]
  refine ⟨247255658079330171293502083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164837105386220114195668055 247255658079330171293502083)
  ·
    refine ⟨370883487118995256940253125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247255658079330171293502083 370883487118995256940253125)
    ·
      refine ⟨69540653834811610676297461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370883487118995256940253125 69540653834811610676297461)
      ·
        refine ⟨6519436297013588500902887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69540653834811610676297461 6519436297013588500902887)
        ·
          refine ⟨9779154445520382751354331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6519436297013588500902887 9779154445520382751354331)
          ·
            refine ⟨14668731668280574127031497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9779154445520382751354331 14668731668280574127031497)
            ·
              refine ⟨11001548751210430595273623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14668731668280574127031497 11001548751210430595273623)
              ·
                refine ⟨16502323126815645892910435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11001548751210430595273623 16502323126815645892910435)
                ·
                  refine ⟨24753484690223468839365653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16502323126815645892910435 24753484690223468839365653)
                  ·
                    refine ⟨1160319594854225101845265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24753484690223468839365653 1160319594854225101845265)
                    ·
                      rfl

theorem cell23_6779143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_6779143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779143 prefixEnd_6779143 := by exact prefixLift 6779143
  have htrace : WordTrace (prefixWord ++ tailWord_6779143) baseStart_6779143 baseEnd_6779143 := by
    simpa [prefixWord, tailWord_6779143, baseEnd_6779143] using wordTrace_append hprefix tailTrace_6779143
  have hstable : (prefixWord ++ tailWord_6779143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779143).length < 2 ^ (prefixWord ++ tailWord_6779143).sum := by decide
  have hdescent : baseEnd_6779143 < baseStart_6779143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779167 : List Nat := [1, 1, 2, 4, 3, 2, 2, 3, 1, 2, 2]
def baseStart_6779167 : Nat := 118140960795 + 6779167 * 2 ^ 59
def prefixEnd_6779167 : Nat := 4983230072969 + 3 ^ 40 * 6779167 * 2
def baseEnd_6779167 : Nat := 3480971108098383211635685

theorem tailTrace_6779167 : CollatzResearch.WordTrace tailWord_6779167 prefixEnd_6779167 3480971108098383211635685 := by
  unfold tailWord_6779167
  simp only [CollatzResearch.WordTrace]
  refine ⟨247256533431243223392375755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164837688954162148928250503 247256533431243223392375755)
  ·
    refine ⟨370884800146864835088563633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247256533431243223392375755 370884800146864835088563633)
    ·
      refine ⟨278163600110148626316422725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370884800146864835088563633 278163600110148626316422725)
      ·
        refine ⟨52155675020652867434329261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278163600110148626316422725 52155675020652867434329261)
        ·
          refine ⟨19558378132744825287873473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52155675020652867434329261 19558378132744825287873473)
          ·
            refine ⟨14668783599558618965905105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19558378132744825287873473 14668783599558618965905105)
            ·
              refine ⟨11001587699668964224428829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14668783599558618965905105 11001587699668964224428829)
              ·
                refine ⟨4125595387375861584160811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11001587699668964224428829 4125595387375861584160811)
                ·
                  refine ⟨6188393081063792376241217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125595387375861584160811 6188393081063792376241217)
                  ·
                    refine ⟨4641294810797844282180913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6188393081063792376241217 4641294810797844282180913)
                    ·
                      refine ⟨3480971108098383211635685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4641294810797844282180913 3480971108098383211635685)
                      ·
                        rfl

theorem cell23_6779167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_6779167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779167 prefixEnd_6779167 := by exact prefixLift 6779167
  have htrace : WordTrace (prefixWord ++ tailWord_6779167) baseStart_6779167 baseEnd_6779167 := by
    simpa [prefixWord, tailWord_6779167, baseEnd_6779167] using wordTrace_append hprefix tailTrace_6779167
  have hstable : (prefixWord ++ tailWord_6779167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779167).length < 2 ^ (prefixWord ++ tailWord_6779167).sum := by decide
  have hdescent : baseEnd_6779167 < baseStart_6779167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779170 : List Nat := [3, 3, 1, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_6779170 : Nat := 118140960795 + 6779170 * 2 ^ 59
def prefixEnd_6779170 : Nat := 4983230072969 + 3 ^ 40 * 6779170 * 2
def baseEnd_6779170 : Nat := 3480972648540346699898171

theorem tailTrace_6779170 : CollatzResearch.WordTrace tailWord_6779170 prefixEnd_6779170 3480972648540346699898171 := by
  unfold tailWord_6779170
  simp only [CollatzResearch.WordTrace]
  refine ⟨61814160712558088726183741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164837761900154903269823309 61814160712558088726183741)
  ·
    refine ⟨23180310267209283272318903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61814160712558088726183741 23180310267209283272318903)
    ·
      refine ⟨34770465400813924908478355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23180310267209283272318903 34770465400813924908478355)
      ·
        refine ⟨52155698101220887362717533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34770465400813924908478355 52155698101220887362717533)
        ·
          refine ⟨19558386787957832761019075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52155698101220887362717533 19558386787957832761019075)
          ·
            refine ⟨29337580181936749141528613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19558386787957832761019075 29337580181936749141528613)
            ·
              refine ⟨5500796284113140464036615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29337580181936749141528613 5500796284113140464036615)
              ·
                refine ⟨8251194426169710696054923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5500796284113140464036615 8251194426169710696054923)
                ·
                  refine ⟨12376791639254566044082385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8251194426169710696054923 12376791639254566044082385)
                  ·
                    refine ⟨9282593729440924533061789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12376791639254566044082385 9282593729440924533061789)
                    ·
                      refine ⟨3480972648540346699898171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9282593729440924533061789 3480972648540346699898171)
                      ·
                        rfl

theorem cell23_6779170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_6779170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779170 prefixEnd_6779170 := by exact prefixLift 6779170
  have htrace : WordTrace (prefixWord ++ tailWord_6779170) baseStart_6779170 baseEnd_6779170 := by
    simpa [prefixWord, tailWord_6779170, baseEnd_6779170] using wordTrace_append hprefix tailTrace_6779170
  have hstable : (prefixWord ++ tailWord_6779170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779170).length < 2 ^ (prefixWord ++ tailWord_6779170).sum := by decide
  have hdescent : baseEnd_6779170 < baseStart_6779170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779183 : List Nat := [1, 1, 2, 1, 2, 1, 7, 2, 2, 1, 3]
def baseStart_6779183 : Nat := 118140960795 + 6779183 * 2 ^ 59
def prefixEnd_6779183 : Nat := 4983230072969 + 3 ^ 40 * 6779183 * 2
def baseEnd_6779183 : Nat := 3480979323788855149035611

theorem tailTrace_6779183 : CollatzResearch.WordTrace tailWord_6779183 prefixEnd_6779183 3480979323788855149035611 := by
  unfold tailWord_6779183
  simp only [CollatzResearch.WordTrace]
  refine ⟨247257116999185258124958203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164838077999456838749972135 247257116999185258124958203)
  ·
    refine ⟨370885675498777887187437305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247257116999185258124958203 370885675498777887187437305)
    ·
      refine ⟨278164256624083415390577979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370885675498777887187437305 278164256624083415390577979)
      ·
        refine ⟨417246384936125123085866969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278164256624083415390577979 417246384936125123085866969)
        ·
          refine ⟨312934788702093842314400227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417246384936125123085866969 312934788702093842314400227)
          ·
            refine ⟨469402183053140763471600341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312934788702093842314400227 469402183053140763471600341)
            ·
              refine ⟨11001613665307986643865633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 469402183053140763471600341 11001613665307986643865633)
              ·
                refine ⟨8251210248980989982899225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11001613665307986643865633 8251210248980989982899225)
                ·
                  refine ⟨6188407686735742487174419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8251210248980989982899225 6188407686735742487174419)
                  ·
                    refine ⟨9282611530103613730761629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6188407686735742487174419 9282611530103613730761629)
                    ·
                      refine ⟨3480979323788855149035611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9282611530103613730761629 3480979323788855149035611)
                      ·
                        rfl

theorem cell23_6779183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 1, 3].length) (baseStart_6779183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779183 prefixEnd_6779183 := by exact prefixLift 6779183
  have htrace : WordTrace (prefixWord ++ tailWord_6779183) baseStart_6779183 baseEnd_6779183 := by
    simpa [prefixWord, tailWord_6779183, baseEnd_6779183] using wordTrace_append hprefix tailTrace_6779183
  have hstable : (prefixWord ++ tailWord_6779183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779183).length < 2 ^ (prefixWord ++ tailWord_6779183).sum := by decide
  have hdescent : baseEnd_6779183 < baseStart_6779183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779199 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 2, 6]
def baseStart_6779199 : Nat := 118140960795 + 6779199 * 2 ^ 59
def prefixEnd_6779199 : Nat := 4983230072969 + 3 ^ 40 * 6779199 * 2
def baseEnd_6779199 : Nat := 1160329179826442362145179

theorem tailTrace_6779199 : CollatzResearch.WordTrace tailWord_6779199 prefixEnd_6779199 1160329179826442362145179 := by
  unfold tailWord_6779199
  simp only [CollatzResearch.WordTrace]
  refine ⟨247257700567127292857540651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164838467044751528571693767 247257700567127292857540651)
  ·
    refine ⟨370886550850690939286310977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247257700567127292857540651 370886550850690939286310977)
    ·
      refine ⟨278164913138018204464733233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370886550850690939286310977 278164913138018204464733233)
      ·
        refine ⟨208623684853513653348549925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278164913138018204464733233 208623684853513653348549925)
        ·
          refine ⟨39116940910033810002853111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208623684853513653348549925 39116940910033810002853111)
          ·
            refine ⟨58675411365050715004279667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39116940910033810002853111 58675411365050715004279667)
            ·
              refine ⟨88013117047576072506419501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58675411365050715004279667 88013117047576072506419501)
              ·
                refine ⟨33004918892841027189907313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88013117047576072506419501 33004918892841027189907313)
                ·
                  refine ⟨24753689169630770392430485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33004918892841027189907313 24753689169630770392430485)
                  ·
                    refine ⟨1160329179826442362145179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24753689169630770392430485 1160329179826442362145179)
                    ·
                      rfl

theorem cell23_6779199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_6779199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779199 prefixEnd_6779199 := by exact prefixLift 6779199
  have htrace : WordTrace (prefixWord ++ tailWord_6779199) baseStart_6779199 baseEnd_6779199 := by
    simpa [prefixWord, tailWord_6779199, baseEnd_6779199] using wordTrace_append hprefix tailTrace_6779199
  have hstable : (prefixWord ++ tailWord_6779199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779199).length < 2 ^ (prefixWord ++ tailWord_6779199).sum := by decide
  have hdescent : baseEnd_6779199 < baseStart_6779199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779209 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 5]
def baseStart_6779209 : Nat := 118140960795 + 6779209 * 2 ^ 59
def prefixEnd_6779209 : Nat := 4983230072969 + 3 ^ 40 * 6779209 * 2
def baseEnd_6779209 : Nat := 3480992674285872047310491

theorem tailTrace_6779209 : CollatzResearch.WordTrace tailWord_6779209 prefixEnd_6779209 3480992674285872047310491 := by
  unfold tailWord_6779209
  simp only [CollatzResearch.WordTrace]
  refine ⟨247258065297091064565404681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164838710198060709710269787 247258065297091064565404681)
  ·
    refine ⟨185443548972818298424053511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247258065297091064565404681 185443548972818298424053511)
    ·
      refine ⟨278165323459227447636080267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185443548972818298424053511 278165323459227447636080267)
      ·
        refine ⟨417247985188841171454120401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278165323459227447636080267 417247985188841171454120401)
        ·
          refine ⟨312935988891630878590590301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417247985188841171454120401 312935988891630878590590301)
          ·
            refine ⟨117350995834361579471471363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312935988891630878590590301 117350995834361579471471363)
            ·
              refine ⟨176026493751542369207207045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117350995834361579471471363 176026493751542369207207045)
              ·
                refine ⟨33004967578414194226351321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176026493751542369207207045 33004967578414194226351321)
                ·
                  refine ⟨24753725683810645669763491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33004967578414194226351321 24753725683810645669763491)
                  ·
                    refine ⟨37130588525715968504645237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24753725683810645669763491 37130588525715968504645237)
                    ·
                      refine ⟨3480992674285872047310491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37130588525715968504645237 3480992674285872047310491)
                      ·
                        rfl

theorem cell23_6779209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_6779209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779209 prefixEnd_6779209 := by exact prefixLift 6779209
  have htrace : WordTrace (prefixWord ++ tailWord_6779209) baseStart_6779209 baseEnd_6779209 := by
    simpa [prefixWord, tailWord_6779209, baseEnd_6779209] using wordTrace_append hprefix tailTrace_6779209
  have hstable : (prefixWord ++ tailWord_6779209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779209).length < 2 ^ (prefixWord ++ tailWord_6779209).sum := by decide
  have hdescent : baseEnd_6779209 < baseStart_6779209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779219 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 4]
def baseStart_6779219 : Nat := 118140960795 + 6779219 * 2 ^ 59
def prefixEnd_6779219 : Nat := 4983230072969 + 3 ^ 40 * 6779219 * 2
def baseEnd_6779219 : Nat := 3480997809092417008185445

theorem tailTrace_6779219 : CollatzResearch.WordTrace tailWord_6779219 prefixEnd_6779219 3480997809092417008185445 := by
  unfold tailWord_6779219
  simp only [CollatzResearch.WordTrace]
  refine ⟨247258430027054836273268711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164838953351369890848845807 247258430027054836273268711)
  ·
    refine ⟨370887645040582254409903067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247258430027054836273268711 370887645040582254409903067)
    ·
      refine ⟨556331467560873381614854601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370887645040582254409903067 556331467560873381614854601)
      ·
        refine ⟨417248600670655036211140951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556331467560873381614854601 417248600670655036211140951)
        ·
          refine ⟨625872901005982554316711427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417248600670655036211140951 625872901005982554316711427)
          ·
            refine ⟨938809351508973831475067141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625872901005982554316711427 938809351508973831475067141)
            ·
              refine ⟨176026753407932593401575089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 938809351508973831475067141 176026753407932593401575089)
              ·
                refine ⟨132020065055949445051181317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176026753407932593401575089 132020065055949445051181317)
                ·
                  refine ⟨24753762197990520947096497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132020065055949445051181317 24753762197990520947096497)
                  ·
                    refine ⟨18565321648492890710322373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24753762197990520947096497 18565321648492890710322373)
                    ·
                      refine ⟨3480997809092417008185445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18565321648492890710322373 3480997809092417008185445)
                      ·
                        rfl

theorem cell23_6779219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_6779219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779219 prefixEnd_6779219 := by exact prefixLift 6779219
  have htrace : WordTrace (prefixWord ++ tailWord_6779219) baseStart_6779219 baseEnd_6779219 := by
    simpa [prefixWord, tailWord_6779219, baseEnd_6779219] using wordTrace_append hprefix tailTrace_6779219
  have hstable : (prefixWord ++ tailWord_6779219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779219).length < 2 ^ (prefixWord ++ tailWord_6779219).sum := by decide
  have hdescent : baseEnd_6779219 < baseStart_6779219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779223 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 6, 2, 2]
def baseStart_6779223 : Nat := 118140960795 + 6779223 * 2 ^ 59
def prefixEnd_6779223 : Nat := 4983230072969 + 3 ^ 40 * 6779223 * 2
def baseEnd_6779223 : Nat := 3480999863015034992535427

theorem tailTrace_6779223 : CollatzResearch.WordTrace tailWord_6779223 prefixEnd_6779223 3480999863015034992535427 := by
  unfold tailWord_6779223
  simp only [CollatzResearch.WordTrace]
  refine ⟨247258575919040344956414323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164839050612693563304276215 247258575919040344956414323)
  ·
    refine ⟨370887863878560517434621485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247258575919040344956414323 370887863878560517434621485)
    ·
      refine ⟨139082948954460194037983057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370887863878560517434621485 139082948954460194037983057)
      ·
        refine ⟨104312211715845145528487293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139082948954460194037983057 104312211715845145528487293)
        ·
          refine ⟨39117079393441929573182735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104312211715845145528487293 39117079393441929573182735)
          ·
            refine ⟨58675619090162894359774103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39117079393441929573182735 58675619090162894359774103)
            ·
              refine ⟨88013428635244341539661155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58675619090162894359774103 88013428635244341539661155)
              ·
                refine ⟨132020142952866512309491733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88013428635244341539661155 132020142952866512309491733)
                ·
                  refine ⟨6188444200915617764507425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132020142952866512309491733 6188444200915617764507425)
                  ·
                    refine ⟨4641333150686713323380569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6188444200915617764507425 4641333150686713323380569)
                    ·
                      refine ⟨3480999863015034992535427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4641333150686713323380569 3480999863015034992535427)
                      ·
                        rfl

theorem cell23_6779223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_6779223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779223 prefixEnd_6779223 := by exact prefixLift 6779223
  have htrace : WordTrace (prefixWord ++ tailWord_6779223) baseStart_6779223 baseEnd_6779223 := by
    simpa [prefixWord, tailWord_6779223, baseEnd_6779223] using wordTrace_append hprefix tailTrace_6779223
  have hstable : (prefixWord ++ tailWord_6779223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779223).length < 2 ^ (prefixWord ++ tailWord_6779223).sum := by decide
  have hdescent : baseEnd_6779223 < baseStart_6779223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779240 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_6779240 : Nat := 118140960795 + 6779240 * 2 ^ 59
def prefixEnd_6779240 : Nat := 4983230072969 + 3 ^ 40 * 6779240 * 2
def baseEnd_6779240 : Nat := 3481008592186161426022849

theorem tailTrace_6779240 : CollatzResearch.WordTrace tailWord_6779240 prefixEnd_6779240 3481008592186161426022849 := by
  unfold tailWord_6779240
  simp only [CollatzResearch.WordTrace]
  refine ⟨123629597979989378429891587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164839463973319171239855449 123629597979989378429891587)
  ·
    refine ⟨185444396969984067644837381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123629597979989378429891587 185444396969984067644837381)
    ·
      refine ⟨34770824431872012683407009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185444396969984067644837381 34770824431872012683407009)
      ·
        refine ⟨26078118323904009512555257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34770824431872012683407009 26078118323904009512555257)
        ·
          refine ⟨19558588742928007134416443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26078118323904009512555257 19558588742928007134416443)
          ·
            refine ⟨29337883114392010701624665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19558588742928007134416443 29337883114392010701624665)
            ·
              refine ⟨22003412335794008026218499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29337883114392010701624665 22003412335794008026218499)
              ·
                refine ⟨33005118503691012039327749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22003412335794008026218499 33005118503691012039327749)
                ·
                  refine ⟨6188459719442064757373953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33005118503691012039327749 6188459719442064757373953)
                  ·
                    refine ⟨4641344789581548568030465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6188459719442064757373953 4641344789581548568030465)
                    ·
                      refine ⟨3481008592186161426022849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4641344789581548568030465 3481008592186161426022849)
                      ·
                        rfl

theorem cell23_6779240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_6779240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779240 prefixEnd_6779240 := by exact prefixLift 6779240
  have htrace : WordTrace (prefixWord ++ tailWord_6779240) baseStart_6779240 baseEnd_6779240 := by
    simpa [prefixWord, tailWord_6779240, baseEnd_6779240] using wordTrace_append hprefix tailTrace_6779240
  have hstable : (prefixWord ++ tailWord_6779240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779240).length < 2 ^ (prefixWord ++ tailWord_6779240).sum := by decide
  have hdescent : baseEnd_6779240 < baseStart_6779240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779269 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_6779269 : Nat := 118140960795 + 6779269 * 2 ^ 59
def prefixEnd_6779269 : Nat := 4983230072969 + 3 ^ 40 * 6779269 * 2
def baseEnd_6779269 : Nat := 3481023483125141812560215

theorem tailTrace_6779269 : CollatzResearch.WordTrace tailWord_6779269 prefixEnd_6779269 3481023483125141812560215 := by
  unfold tailWord_6779269
  simp only [CollatzResearch.WordTrace]
  refine ⟨247260253676873694812588861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164840169117915796541725907 247260253676873694812588861)
  ·
    refine ⟨92722595128827635554720823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247260253676873694812588861 92722595128827635554720823)
    ·
      refine ⟨139083892693241453332081235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92722595128827635554720823 139083892693241453332081235)
      ·
        refine ⟨208625839039862179998121853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139083892693241453332081235 208625839039862179998121853)
        ·
          refine ⟨78234689639948317499295695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208625839039862179998121853 78234689639948317499295695)
          ·
            refine ⟨117352034459922476248943543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78234689639948317499295695 117352034459922476248943543)
            ·
              refine ⟨176028051689883714373415315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117352034459922476248943543 176028051689883714373415315)
              ·
                refine ⟨264042077534825571560122973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176028051689883714373415315 264042077534825571560122973)
                ·
                  refine ⟨99015779075559589335046115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264042077534825571560122973 99015779075559589335046115)
                  ·
                    refine ⟨148523668613339384002569173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99015779075559589335046115 148523668613339384002569173)
                    ·
                      refine ⟨3481023483125141812560215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148523668613339384002569173 3481023483125141812560215)
                      ·
                        rfl

theorem cell23_6779269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_6779269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779269 prefixEnd_6779269 := by exact prefixLift 6779269
  have htrace : WordTrace (prefixWord ++ tailWord_6779269) baseStart_6779269 baseEnd_6779269 := by
    simpa [prefixWord, tailWord_6779269, baseEnd_6779269] using wordTrace_append hprefix tailTrace_6779269
  have hstable : (prefixWord ++ tailWord_6779269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779269).length < 2 ^ (prefixWord ++ tailWord_6779269).sum := by decide
  have hdescent : baseEnd_6779269 < baseStart_6779269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779276 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 2, 5]
def baseStart_6779276 : Nat := 118140960795 + 6779276 * 2 ^ 59
def prefixEnd_6779276 : Nat := 4983230072969 + 3 ^ 40 * 6779276 * 2
def baseEnd_6779276 : Nat := 1160342359163241095057561

theorem tailTrace_6779276 : CollatzResearch.WordTrace tailWord_6779276 prefixEnd_6779276 1160342359163241095057561 := by
  unfold tailWord_6779276
  simp only [CollatzResearch.WordTrace]
  refine ⟨123630254493924167504046841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164840339325232223338729121 123630254493924167504046841)
  ·
    refine ⟨92722690870443125628035131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123630254493924167504046841 92722690870443125628035131)
    ·
      refine ⟨139084036305664688442052697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92722690870443125628035131 139084036305664688442052697)
      ·
        refine ⟨104313027229248516331539523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139084036305664688442052697 104313027229248516331539523)
        ·
          refine ⟨156469540843872774497309285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104313027229248516331539523 156469540843872774497309285)
          ·
            refine ⟨29338038908226145218245491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156469540843872774497309285 29338038908226145218245491)
            ·
              refine ⟨44007058362339217827368237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29338038908226145218245491 44007058362339217827368237)
              ·
                refine ⟨16502646885877206685263089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44007058362339217827368237 16502646885877206685263089)
                ·
                  refine ⟨12376985164407905013947317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16502646885877206685263089 12376985164407905013947317)
                  ·
                    refine ⟨1160342359163241095057561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12376985164407905013947317 1160342359163241095057561)
                    ·
                      rfl

theorem cell23_6779276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_6779276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779276 prefixEnd_6779276 := by exact prefixLift 6779276
  have htrace : WordTrace (prefixWord ++ tailWord_6779276) baseStart_6779276 baseEnd_6779276 := by
    simpa [prefixWord, tailWord_6779276, baseEnd_6779276] using wordTrace_append hprefix tailTrace_6779276
  have hstable : (prefixWord ++ tailWord_6779276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779276).length < 2 ^ (prefixWord ++ tailWord_6779276).sum := by decide
  have hdescent : baseEnd_6779276 < baseStart_6779276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779313 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 1, 6, 2]
def baseStart_6779313 : Nat := 118140960795 + 6779313 * 2 ^ 59
def prefixEnd_6779313 : Nat := 4983230072969 + 3 ^ 40 * 6779313 * 2
def baseEnd_6779313 : Nat := 3481046076273939640410013

theorem tailTrace_6779313 : CollatzResearch.WordTrace tailWord_6779313 prefixEnd_6779313 3481046076273939640410013 := by
  unfold tailWord_6779313
  simp only [CollatzResearch.WordTrace]
  refine ⟨247261858488714290327190593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164841238992476193551460395 247261858488714290327190593)
  ·
    refine ⟨185446393866535717745392945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247261858488714290327190593 185446393866535717745392945)
    ·
      refine ⟨139084795399901788309044709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185446393866535717745392945 139084795399901788309044709)
      ·
        refine ⟨26078399137481585307945883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139084795399901788309044709 26078399137481585307945883)
        ·
          refine ⟨39117598706222377961918825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26078399137481585307945883 39117598706222377961918825)
          ·
            refine ⟨29338199029666783471439119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39117598706222377961918825 29338199029666783471439119)
            ·
              refine ⟨44007298544500175207158679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29338199029666783471439119 44007298544500175207158679)
              ·
                refine ⟨66010947816750262810738019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44007298544500175207158679 66010947816750262810738019)
                ·
                  refine ⟨99016421725125394216107029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66010947816750262810738019 99016421725125394216107029)
                  ·
                    refine ⟨4641394768365252853880017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99016421725125394216107029 4641394768365252853880017)
                    ·
                      refine ⟨3481046076273939640410013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4641394768365252853880017 3481046076273939640410013)
                      ·
                        rfl

theorem cell23_6779313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_6779313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779313 prefixEnd_6779313 := by exact prefixLift 6779313
  have htrace : WordTrace (prefixWord ++ tailWord_6779313) baseStart_6779313 baseEnd_6779313 := by
    simpa [prefixWord, tailWord_6779313, baseEnd_6779313] using wordTrace_append hprefix tailTrace_6779313
  have hstable : (prefixWord ++ tailWord_6779313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779313).length < 2 ^ (prefixWord ++ tailWord_6779313).sum := by decide
  have hdescent : baseEnd_6779313 < baseStart_6779313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779350 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_6779350 : Nat := 118140960795 + 6779350 * 2 ^ 59
def prefixEnd_6779350 : Nat := 4983230072969 + 3 ^ 40 * 6779350 * 2
def baseEnd_6779350 : Nat := 3481065075058155995647343

theorem tailTrace_6779350 : CollatzResearch.WordTrace tailWord_6779350 prefixEnd_6779350 3481065075058155995647343 := by
  unfold tailWord_6779350
  simp only [CollatzResearch.WordTrace]
  refine ⟨15453950499348765352892969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164842138659720163764191669 15453950499348765352892969)
  ·
    refine ⟨11590462874511574014669727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15453950499348765352892969 11590462874511574014669727)
    ·
      refine ⟨17385694311767361022004591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11590462874511574014669727 17385694311767361022004591)
      ·
        refine ⟨26078541467651041533006887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17385694311767361022004591 26078541467651041533006887)
        ·
          refine ⟨39117812201476562299510331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26078541467651041533006887 39117812201476562299510331)
          ·
            refine ⟨58676718302214843449265497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39117812201476562299510331 58676718302214843449265497)
            ·
              refine ⟨44007538726661132586949123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58676718302214843449265497 44007538726661132586949123)
              ·
                refine ⟨66011308089991698880423685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44007538726661132586949123 66011308089991698880423685)
                ·
                  refine ⟨12377120266873443540079441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66011308089991698880423685 12377120266873443540079441)
                  ·
                    refine ⟨9282840200155082655059581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12377120266873443540079441 9282840200155082655059581)
                    ·
                      refine ⟨3481065075058155995647343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9282840200155082655059581 3481065075058155995647343)
                      ·
                        rfl

theorem cell23_6779350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_6779350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779350 prefixEnd_6779350 := by exact prefixLift 6779350
  have htrace : WordTrace (prefixWord ++ tailWord_6779350) baseStart_6779350 baseEnd_6779350 := by
    simpa [prefixWord, tailWord_6779350, baseEnd_6779350] using wordTrace_append hprefix tailTrace_6779350
  have hstable : (prefixWord ++ tailWord_6779350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779350).length < 2 ^ (prefixWord ++ tailWord_6779350).sum := by decide
  have hdescent : baseEnd_6779350 < baseStart_6779350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779370 : List Nat := [3, 1, 3, 1, 3, 2, 3, 1, 6]
def baseStart_6779370 : Nat := 118140960795 + 6779370 * 2 ^ 59
def prefixEnd_6779370 : Nat := 4983230072969 + 3 ^ 40 * 6779370 * 2
def baseEnd_6779370 : Nat := 386786149407916213044139

theorem tailTrace_6779370 : CollatzResearch.WordTrace tailWord_6779370 prefixEnd_6779370 386786149407916213044139 := by
  unfold tailWord_6779370
  simp only [CollatzResearch.WordTrace]
  refine ⟨61815984362376947265503891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164842624966338526041343709 61815984362376947265503891)
  ·
    refine ⟨92723976543565420898255837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61815984362376947265503891 92723976543565420898255837)
    ·
      refine ⟨34771491203837032836845939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92723976543565420898255837 34771491203837032836845939)
      ·
        refine ⟨52157236805755549255268909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34771491203837032836845939 52157236805755549255268909)
        ·
          refine ⟨19558963802158330970725841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52157236805755549255268909 19558963802158330970725841)
          ·
            refine ⟨14669222851618748228044381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19558963802158330970725841 14669222851618748228044381)
            ·
              refine ⟨5500958569357030585516643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14669222851618748228044381 5500958569357030585516643)
              ·
                refine ⟨8251437854035545878274965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5500958569357030585516643 8251437854035545878274965)
                ·
                  refine ⟨386786149407916213044139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8251437854035545878274965 386786149407916213044139)
                  ·
                    rfl

theorem cell23_6779370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_6779370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779370 prefixEnd_6779370 := by exact prefixLift 6779370
  have htrace : WordTrace (prefixWord ++ tailWord_6779370) baseStart_6779370 baseEnd_6779370 := by
    simpa [prefixWord, tailWord_6779370, baseEnd_6779370] using wordTrace_append hprefix tailTrace_6779370
  have hstable : (prefixWord ++ tailWord_6779370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779370).length < 2 ^ (prefixWord ++ tailWord_6779370).sum := by decide
  have hdescent : baseEnd_6779370 < baseStart_6779370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779397 : List Nat := [1, 3, 1, 1, 2, 2, 5, 3, 1, 1, 3]
def baseStart_6779397 : Nat := 118140960795 + 6779397 * 2 ^ 59
def prefixEnd_6779397 : Nat := 4983230072969 + 3 ^ 40 * 6779397 * 2
def baseEnd_6779397 : Nat := 3481089208648917311759627

theorem tailTrace_6779397 : CollatzResearch.WordTrace tailWord_6779397 prefixEnd_6779397 3481089208648917311759627 := by
  unfold tailWord_6779397
  simp only [CollatzResearch.WordTrace]
  refine ⟨247264922220409972673248445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164843281480273315115498963 247264922220409972673248445)
  ·
    refine ⟨92724345832653739752468167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247264922220409972673248445 92724345832653739752468167)
    ·
      refine ⟨139086518748980609628702251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92724345832653739752468167 139086518748980609628702251)
      ·
        refine ⟨208629778123470914443053377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139086518748980609628702251 208629778123470914443053377)
        ·
          refine ⟨156472333592603185832290033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208629778123470914443053377 156472333592603185832290033)
          ·
            refine ⟨117354250194452389374217525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156472333592603185832290033 117354250194452389374217525)
            ·
              refine ⟨11001960955729911503832893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117354250194452389374217525 11001960955729911503832893)
              ·
                refine ⟨4125735358398716813937335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11001960955729911503832893 4125735358398716813937335)
                ·
                  refine ⟨6188603037598075220906003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125735358398716813937335 6188603037598075220906003)
                  ·
                    refine ⟨9282904556397112831359005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6188603037598075220906003 9282904556397112831359005)
                    ·
                      refine ⟨3481089208648917311759627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9282904556397112831359005 3481089208648917311759627)
                      ·
                        rfl

theorem cell23_6779397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 1, 1, 3].length) (baseStart_6779397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779397 prefixEnd_6779397 := by exact prefixLift 6779397
  have htrace : WordTrace (prefixWord ++ tailWord_6779397) baseStart_6779397 baseEnd_6779397 := by
    simpa [prefixWord, tailWord_6779397, baseEnd_6779397] using wordTrace_append hprefix tailTrace_6779397
  have hstable : (prefixWord ++ tailWord_6779397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779397).length < 2 ^ (prefixWord ++ tailWord_6779397).sum := by decide
  have hdescent : baseEnd_6779397 < baseStart_6779397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779413 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 4, 4]
def baseStart_6779413 : Nat := 118140960795 + 6779413 * 2 ^ 59
def prefixEnd_6779413 : Nat := 4983230072969 + 3 ^ 40 * 6779413 * 2
def baseEnd_6779413 : Nat := 1160365808113129749719851

theorem tailTrace_6779413 : CollatzResearch.WordTrace tailWord_6779413 prefixEnd_6779413 1160365808113129749719851 := by
  unfold tailWord_6779413
  simp only [CollatzResearch.WordTrace]
  refine ⟨247265505788352007405830893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164843670525568004937220595 247265505788352007405830893)
  ·
    refine ⟨92724564670632002777186585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247265505788352007405830893 92724564670632002777186585)
    ·
      refine ⟨69543423502974002082889939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92724564670632002777186585 69543423502974002082889939)
      ·
        refine ⟨104315135254461003124334909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69543423502974002082889939 104315135254461003124334909)
        ·
          refine ⟨39118175720422876171625591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104315135254461003124334909 39118175720422876171625591)
          ·
            refine ⟨58677263580634314257438387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39118175720422876171625591 58677263580634314257438387)
            ·
              refine ⟨88015895370951471386157581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58677263580634314257438387 88015895370951471386157581)
              ·
                refine ⟨33005960764106801769809093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88015895370951471386157581 33005960764106801769809093)
                ·
                  refine ⟨6188617643270025331839205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33005960764106801769809093 6188617643270025331839205)
                  ·
                    refine ⟨1160365808113129749719851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6188617643270025331839205 1160365808113129749719851)
                    ·
                      rfl

theorem cell23_6779413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_6779413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779413 prefixEnd_6779413 := by exact prefixLift 6779413
  have htrace : WordTrace (prefixWord ++ tailWord_6779413) baseStart_6779413 baseEnd_6779413 := by
    simpa [prefixWord, tailWord_6779413, baseEnd_6779413] using wordTrace_append hprefix tailTrace_6779413
  have hstable : (prefixWord ++ tailWord_6779413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779413).length < 2 ^ (prefixWord ++ tailWord_6779413).sum := by decide
  have hdescent : baseEnd_6779413 < baseStart_6779413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779423 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 3]
def baseStart_6779423 : Nat := 118140960795 + 6779423 * 2 ^ 59
def prefixEnd_6779423 : Nat := 4983230072969 + 3 ^ 40 * 6779423 * 2
def baseEnd_6779423 : Nat := 3481102559145934210034507

theorem tailTrace_6779423 : CollatzResearch.WordTrace tailWord_6779423 prefixEnd_6779423 3481102559145934210034507 := by
  unfold tailWord_6779423
  simp only [CollatzResearch.WordTrace]
  refine ⟨247265870518315779113694923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164843913678877186075796615 247265870518315779113694923)
  ·
    refine ⟨370898805777473668670542385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247265870518315779113694923 370898805777473668670542385)
    ·
      refine ⟨278174104333105251502906789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370898805777473668670542385 278174104333105251502906789)
      ·
        refine ⟨52157644562457234656795023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278174104333105251502906789 52157644562457234656795023)
        ·
          refine ⟨78236466843685851985192535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52157644562457234656795023 78236466843685851985192535)
          ·
            refine ⟨117354700265528777977788803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78236466843685851985192535 117354700265528777977788803)
            ·
              refine ⟨176032050398293166966683205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117354700265528777977788803 176032050398293166966683205)
              ·
                refine ⟨33006009449679968806253101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176032050398293166966683205 33006009449679968806253101)
                ·
                  refine ⟨12377253543629988302344913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33006009449679968806253101 12377253543629988302344913)
                  ·
                    refine ⟨9282940157722491226758685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12377253543629988302344913 9282940157722491226758685)
                    ·
                      refine ⟨3481102559145934210034507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9282940157722491226758685 3481102559145934210034507)
                      ·
                        rfl

theorem cell23_6779423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_6779423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779423 prefixEnd_6779423 := by exact prefixLift 6779423
  have htrace : WordTrace (prefixWord ++ tailWord_6779423) baseStart_6779423 baseEnd_6779423 := by
    simpa [prefixWord, tailWord_6779423, baseEnd_6779423] using wordTrace_append hprefix tailTrace_6779423
  have hstable : (prefixWord ++ tailWord_6779423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779423).length < 2 ^ (prefixWord ++ tailWord_6779423).sum := by decide
  have hdescent : baseEnd_6779423 < baseStart_6779423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779440 : List Nat := [2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 3]
def baseStart_6779440 : Nat := 118140960795 + 6779440 * 2 ^ 59
def prefixEnd_6779440 : Nat := 4983230072969 + 3 ^ 40 * 6779440 * 2
def baseEnd_6779440 : Nat := 3481111288317060643521929

theorem tailTrace_6779440 : CollatzResearch.WordTrace tailWord_6779440 prefixEnd_6779440 3481111288317060643521929 := by
  unfold tailWord_6779440
  simp only [CollatzResearch.WordTrace]
  refine ⟨123633245279627095508531887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164844327039502794011375849 123633245279627095508531887)
  ·
    refine ⟨185449867919440643262797831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123633245279627095508531887 185449867919440643262797831)
    ·
      refine ⟨278174801879160964894196747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185449867919440643262797831 278174801879160964894196747)
      ·
        refine ⟨417262202818741447341295121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278174801879160964894196747 417262202818741447341295121)
        ·
          refine ⟨312946652114056085505971341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417262202818741447341295121 312946652114056085505971341)
          ·
            refine ⟨117354994542771032064739253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312946652114056085505971341 117354994542771032064739253)
            ·
              refine ⟨11002030738384784256069305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117354994542771032064739253 11002030738384784256069305)
              ·
                refine ⟨8251523053788588192051979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11002030738384784256069305 8251523053788588192051979)
                ·
                  refine ⟨12377284580682882288077969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8251523053788588192051979 12377284580682882288077969)
                  ·
                    refine ⟨9282963435512161716058477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12377284580682882288077969 9282963435512161716058477)
                    ·
                      refine ⟨3481111288317060643521929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9282963435512161716058477 3481111288317060643521929)
                      ·
                        rfl

theorem cell23_6779440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 3].length) (baseStart_6779440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779440 prefixEnd_6779440 := by exact prefixLift 6779440
  have htrace : WordTrace (prefixWord ++ tailWord_6779440) baseStart_6779440 baseEnd_6779440 := by
    simpa [prefixWord, tailWord_6779440, baseEnd_6779440] using wordTrace_append hprefix tailTrace_6779440
  have hstable : (prefixWord ++ tailWord_6779440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779440).length < 2 ^ (prefixWord ++ tailWord_6779440).sum := by decide
  have hdescent : baseEnd_6779440 < baseStart_6779440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779460 : List Nat := [2, 3, 5, 1, 12]
def baseStart_6779460 : Nat := 118140960795 + 6779460 * 2 ^ 59
def prefixEnd_6779460 : Nat := 4983230072969 + 3 ^ 40 * 6779460 * 2
def baseEnd_6779460 : Nat := 4775201039684705850853

theorem tailTrace_6779460 : CollatzResearch.WordTrace tailWord_6779460 prefixEnd_6779460 4775201039684705850853 := by
  unfold tailWord_6779460
  simp only [CollatzResearch.WordTrace]
  refine ⟨123633610009590867216395917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164844813346121156288527889 123633610009590867216395917)
  ·
    refine ⟨46362603753596575206148469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123633610009590867216395917 46362603753596575206148469)
    ·
      refine ⟨4346494101899678925576419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46362603753596575206148469 4346494101899678925576419)
      ·
        refine ⟨6519741152849518388364629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4346494101899678925576419 6519741152849518388364629)
        ·
          refine ⟨4775201039684705850853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6519741152849518388364629 4775201039684705850853)
          ·
            rfl

theorem cell23_6779460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 12].length) (baseStart_6779460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779460 prefixEnd_6779460 := by exact prefixLift 6779460
  have htrace : WordTrace (prefixWord ++ tailWord_6779460) baseStart_6779460 baseEnd_6779460 := by
    simpa [prefixWord, tailWord_6779460, baseEnd_6779460] using wordTrace_append hprefix tailTrace_6779460
  have hstable : (prefixWord ++ tailWord_6779460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779460).length < 2 ^ (prefixWord ++ tailWord_6779460).sum := by decide
  have hdescent : baseEnd_6779460 < baseStart_6779460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779470 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_6779470 : Nat := 118140960795 + 6779470 * 2 ^ 59
def prefixEnd_6779470 : Nat := 4983230072969 + 3 ^ 40 * 6779470 * 2
def baseEnd_6779470 : Nat := 3481126692736695526146791

theorem tailTrace_6779470 : CollatzResearch.WordTrace tailWord_6779470 prefixEnd_6779470 3481126692736695526146791 := by
  unfold tailWord_6779470
  simp only [CollatzResearch.WordTrace]
  refine ⟨30908448093643188267581983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164845056499430337427103909 30908448093643188267581983)
  ·
    refine ⟨46362672140464782401372975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30908448093643188267581983 46362672140464782401372975)
    ·
      refine ⟨69544008210697173602059463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46362672140464782401372975 69544008210697173602059463)
      ·
        refine ⟨104316012316045760403089195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69544008210697173602059463 104316012316045760403089195)
        ·
          refine ⟨156474018474068640604633793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104316012316045760403089195 156474018474068640604633793)
          ·
            refine ⟨117355513855551480453475345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156474018474068640604633793 117355513855551480453475345)
            ·
              refine ⟨88016635391663610340106509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117355513855551480453475345 88016635391663610340106509)
              ·
                refine ⟨33006238271873853877539941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88016635391663610340106509 33006238271873853877539941)
                ·
                  refine ⟨6188669675976347602038739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33006238271873853877539941 6188669675976347602038739)
                  ·
                    refine ⟨9283004513964521403058109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6188669675976347602038739 9283004513964521403058109)
                    ·
                      refine ⟨3481126692736695526146791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9283004513964521403058109 3481126692736695526146791)
                      ·
                        rfl

theorem cell23_6779470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_6779470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779470 prefixEnd_6779470 := by exact prefixLift 6779470
  have htrace : WordTrace (prefixWord ++ tailWord_6779470) baseStart_6779470 baseEnd_6779470 := by
    simpa [prefixWord, tailWord_6779470, baseEnd_6779470] using wordTrace_append hprefix tailTrace_6779470
  have hstable : (prefixWord ++ tailWord_6779470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779470).length < 2 ^ (prefixWord ++ tailWord_6779470).sum := by decide
  have hdescent : baseEnd_6779470 < baseStart_6779470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779480 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 3, 3, 2]
def baseStart_6779480 : Nat := 118140960795 + 6779480 * 2 ^ 59
def prefixEnd_6779480 : Nat := 4983230072969 + 3 ^ 40 * 6779480 * 2
def baseEnd_6779480 : Nat := 3481131827543240487021745

theorem tailTrace_6779480 : CollatzResearch.WordTrace tailWord_6779480 prefixEnd_6779480 3481131827543240487021745 := by
  unfold tailWord_6779480
  simp only [CollatzResearch.WordTrace]
  refine ⟨123633974739554638924259947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164845299652739518565679929 123633974739554638924259947)
  ·
    refine ⟨185450962109331958386389921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123633974739554638924259947 185450962109331958386389921)
    ·
      refine ⟨139088221581998968789792441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185450962109331958386389921 139088221581998968789792441)
      ·
        refine ⟨104316166186499226592344331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139088221581998968789792441 104316166186499226592344331)
        ·
          refine ⟨156474249279748839888516497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104316166186499226592344331 156474249279748839888516497)
          ·
            refine ⟨117355686959811629916387373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156474249279748839888516497 117355686959811629916387373)
            ·
              refine ⟨44008382609929361218645265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117355686959811629916387373 44008382609929361218645265)
              ·
                refine ⟨33006286957447020913983949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44008382609929361218645265 33006286957447020913983949)
                ·
                  refine ⟨12377357609042632842743981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33006286957447020913983949 12377357609042632842743981)
                  ·
                    refine ⟨4641509103390987316028993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12377357609042632842743981 4641509103390987316028993)
                    ·
                      refine ⟨3481131827543240487021745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4641509103390987316028993 3481131827543240487021745)
                      ·
                        rfl

theorem cell23_6779480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_6779480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779480 prefixEnd_6779480 := by exact prefixLift 6779480
  have htrace : WordTrace (prefixWord ++ tailWord_6779480) baseStart_6779480 baseEnd_6779480 := by
    simpa [prefixWord, tailWord_6779480, baseEnd_6779480] using wordTrace_append hprefix tailTrace_6779480
  have hstable : (prefixWord ++ tailWord_6779480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779480).length < 2 ^ (prefixWord ++ tailWord_6779480).sum := by decide
  have hdescent : baseEnd_6779480 < baseStart_6779480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779523 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 4]
def baseStart_6779523 : Nat := 118140960795 + 6779523 * 2 ^ 59
def prefixEnd_6779523 : Nat := 4983230072969 + 3 ^ 40 * 6779523 * 2
def baseEnd_6779523 : Nat := 3481153907211383818784047

theorem tailTrace_6779523 : CollatzResearch.WordTrace tailWord_6779523 prefixEnd_6779523 3481153907211383818784047 := by
  unfold tailWord_6779523
  simp only [CollatzResearch.WordTrace]
  refine ⟨247269517817953496192335223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164846345211968997461556815 247269517817953496192335223)
  ·
    refine ⟨370904276726930244288502835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247269517817953496192335223 370904276726930244288502835)
    ·
      refine ⟨556356415090395366432754253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370904276726930244288502835 556356415090395366432754253)
      ·
        refine ⟨208633655658898262412282845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 556356415090395366432754253 208633655658898262412282845)
        ·
          refine ⟨78237620872086848404606067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208633655658898262412282845 78237620872086848404606067)
          ·
            refine ⟨117356431308130272606909101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78237620872086848404606067 117356431308130272606909101)
            ·
              refine ⟨44008661740548852227590913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117356431308130272606909101 44008661740548852227590913)
              ·
                refine ⟨33006496305411639170693185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44008661740548852227590913 33006496305411639170693185)
                ·
                  refine ⟨24754872229058729378019889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33006496305411639170693185 24754872229058729378019889)
                  ·
                    refine ⟨18566154171794047033514917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24754872229058729378019889 18566154171794047033514917)
                    ·
                      refine ⟨3481153907211383818784047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18566154171794047033514917 3481153907211383818784047)
                      ·
                        rfl

theorem cell23_6779523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_6779523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779523 prefixEnd_6779523 := by exact prefixLift 6779523
  have htrace : WordTrace (prefixWord ++ tailWord_6779523) baseStart_6779523 baseEnd_6779523 := by
    simpa [prefixWord, tailWord_6779523, baseEnd_6779523] using wordTrace_append hprefix tailTrace_6779523
  have hstable : (prefixWord ++ tailWord_6779523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779523).length < 2 ^ (prefixWord ++ tailWord_6779523).sum := by decide
  have hdescent : baseEnd_6779523 < baseStart_6779523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779527 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 4, 2, 2]
def baseStart_6779527 : Nat := 118140960795 + 6779527 * 2 ^ 59
def prefixEnd_6779527 : Nat := 4983230072969 + 3 ^ 40 * 6779527 * 2
def baseEnd_6779527 : Nat := 3481155961134001803134029

theorem tailTrace_6779527 : CollatzResearch.WordTrace tailWord_6779527 prefixEnd_6779527 3481155961134001803134029 := by
  unfold tailWord_6779527
  simp only [CollatzResearch.WordTrace]
  refine ⟨247269663709939004875480835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164846442473292669916987223 247269663709939004875480835)
  ·
    refine ⟨370904495564908507313221253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247269663709939004875480835 370904495564908507313221253)
    ·
      refine ⟨69544592918420345121228985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370904495564908507313221253 69544592918420345121228985)
      ·
        refine ⟨52158444688815258840921739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69544592918420345121228985 52158444688815258840921739)
        ·
          refine ⟨78237667033222888261382609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52158444688815258840921739 78237667033222888261382609)
          ·
            refine ⟨58678250274917166196036957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78237667033222888261382609 58678250274917166196036957)
            ·
              refine ⟨22004343853093937323513859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58678250274917166196036957 22004343853093937323513859)
              ·
                refine ⟨33006515779640905985270789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22004343853093937323513859 33006515779640905985270789)
                ·
                  refine ⟨6188721708682669872238273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33006515779640905985270789 6188721708682669872238273)
                  ·
                    refine ⟨4641541281512002404178705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6188721708682669872238273 4641541281512002404178705)
                    ·
                      refine ⟨3481155961134001803134029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4641541281512002404178705 3481155961134001803134029)
                      ·
                        rfl

theorem cell23_6779527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_6779527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779527 prefixEnd_6779527 := by exact prefixLift 6779527
  have htrace : WordTrace (prefixWord ++ tailWord_6779527) baseStart_6779527 baseEnd_6779527 := by
    simpa [prefixWord, tailWord_6779527, baseEnd_6779527] using wordTrace_append hprefix tailTrace_6779527
  have hstable : (prefixWord ++ tailWord_6779527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779527).length < 2 ^ (prefixWord ++ tailWord_6779527).sum := by decide
  have hdescent : baseEnd_6779527 < baseStart_6779527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779550 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 7]
def baseStart_6779550 : Nat := 118140960795 + 6779550 * 2 ^ 59
def prefixEnd_6779550 : Nat := 4983230072969 + 3 ^ 40 * 6779550 * 2
def baseEnd_6779550 : Nat := 386796419021006134794047

theorem tailTrace_6779550 : CollatzResearch.WordTrace tailWord_6779550 prefixEnd_6779550 386796419021006134794047 := by
  unfold tailWord_6779550
  simp only [CollatzResearch.WordTrace]
  refine ⟨30908812823606959975446013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164847001725903786535712069 30908812823606959975446013)
  ·
    refine ⟨11590804808852609990792255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30908812823606959975446013 11590804808852609990792255)
    ·
      refine ⟨17386207213278914986188383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11590804808852609990792255 17386207213278914986188383)
      ·
        refine ⟨26079310819918372479282575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17386207213278914986188383 26079310819918372479282575)
        ·
          refine ⟨39118966229877558718923863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26079310819918372479282575 39118966229877558718923863)
          ·
            refine ⟨58678449344816338078385795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39118966229877558718923863 58678449344816338078385795)
            ·
              refine ⟨88017674017224507117578693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58678449344816338078385795 88017674017224507117578693)
              ·
                refine ⟨16503313878229595084546005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88017674017224507117578693 16503313878229595084546005)
                ·
                  refine ⟨386796419021006134794047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16503313878229595084546005 386796419021006134794047)
                  ·
                    rfl

theorem cell23_6779550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_6779550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779550 prefixEnd_6779550 := by exact prefixLift 6779550
  have htrace : WordTrace (prefixWord ++ tailWord_6779550) baseStart_6779550 baseEnd_6779550 := by
    simpa [prefixWord, tailWord_6779550, baseEnd_6779550] using wordTrace_append hprefix tailTrace_6779550
  have hstable : (prefixWord ++ tailWord_6779550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779550).length < 2 ^ (prefixWord ++ tailWord_6779550).sum := by decide
  have hdescent : baseEnd_6779550 < baseStart_6779550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779567 : List Nat := [1, 1, 2, 1, 2, 7, 1, 3, 5]
def baseStart_6779567 : Nat := 118140960795 + 6779567 * 2 ^ 59
def prefixEnd_6779567 : Nat := 4983230072969 + 3 ^ 40 * 6779567 * 2
def baseEnd_6779567 : Nat := 386797388928909071848205

theorem tailTrace_6779567 : CollatzResearch.WordTrace tailWord_6779567 prefixEnd_6779567 386797388928909071848205 := by
  unfold tailWord_6779567
  simp only [CollatzResearch.WordTrace]
  refine ⟨247271122629794091706936955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164847415086529394471291303 247271122629794091706936955)
  ·
    refine ⟨370906683944691137560405433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247271122629794091706936955 370906683944691137560405433)
    ·
      refine ⟨278180012958518353170304075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370906683944691137560405433 278180012958518353170304075)
      ·
        refine ⟨417270019437777529755456113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278180012958518353170304075 417270019437777529755456113)
        ·
          refine ⟨312952514578333147316592085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417270019437777529755456113 312952514578333147316592085)
          ·
            refine ⟨7334824560429683140232627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 312952514578333147316592085 7334824560429683140232627)
            ·
              refine ⟨11002236840644524710348941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7334824560429683140232627 11002236840644524710348941)
              ·
                refine ⟨4125838815241696766380853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11002236840644524710348941 4125838815241696766380853)
                ·
                  refine ⟨386797388928909071848205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4125838815241696766380853 386797388928909071848205)
                  ·
                    rfl

theorem cell23_6779567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 5].length) (baseStart_6779567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779567 prefixEnd_6779567 := by exact prefixLift 6779567
  have htrace : WordTrace (prefixWord ++ tailWord_6779567) baseStart_6779567 baseEnd_6779567 := by
    simpa [prefixWord, tailWord_6779567, baseEnd_6779567] using wordTrace_append hprefix tailTrace_6779567
  have hstable : (prefixWord ++ tailWord_6779567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779567).length < 2 ^ (prefixWord ++ tailWord_6779567).sum := by decide
  have hdescent : baseEnd_6779567 < baseStart_6779567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779570 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2]
def baseStart_6779570 : Nat := 118140960795 + 6779570 * 2 ^ 59
def prefixEnd_6779570 : Nat := 4983230072969 + 3 ^ 40 * 6779570 * 2
def baseEnd_6779570 : Nat := 3481178040802145134896331

theorem tailTrace_6779570 : CollatzResearch.WordTrace tailWord_6779570 prefixEnd_6779570 3481178040802145134896331 := by
  unfold tailWord_6779570
  simp only [CollatzResearch.WordTrace]
  refine ⟨61817808012195805804824041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164847488032522148812864109 61817808012195805804824041)
  ·
    refine ⟨46363356009146854353618031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61817808012195805804824041 46363356009146854353618031)
    ·
      refine ⟨69545034013720281530427047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46363356009146854353618031 69545034013720281530427047)
      ·
        refine ⟨104317551020580422295640571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69545034013720281530427047 104317551020580422295640571)
        ·
          refine ⟨156476326530870633443460857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104317551020580422295640571 156476326530870633443460857)
          ·
            refine ⟨117357244898152975082595643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156476326530870633443460857 117357244898152975082595643)
            ·
              refine ⟨176035867347229462623893465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117357244898152975082595643 176035867347229462623893465)
              ·
                refine ⟨132026900510422096967920099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176035867347229462623893465 132026900510422096967920099)
                ·
                  refine ⟨198040350765633145451880149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132026900510422096967920099 198040350765633145451880149)
                  ·
                    refine ⟨4641570721069526846528441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 198040350765633145451880149 4641570721069526846528441)
                    ·
                      refine ⟨3481178040802145134896331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4641570721069526846528441 3481178040802145134896331)
                      ·
                        rfl

theorem cell23_6779570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_6779570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779570 prefixEnd_6779570 := by exact prefixLift 6779570
  have htrace : WordTrace (prefixWord ++ tailWord_6779570) baseStart_6779570 baseEnd_6779570 := by
    simpa [prefixWord, tailWord_6779570, baseEnd_6779570] using wordTrace_append hprefix tailTrace_6779570
  have hstable : (prefixWord ++ tailWord_6779570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779570).length < 2 ^ (prefixWord ++ tailWord_6779570).sum := by decide
  have hdescent : baseEnd_6779570 < baseStart_6779570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779580 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 2, 5]
def baseStart_6779580 : Nat := 118140960795 + 6779580 * 2 ^ 59
def prefixEnd_6779580 : Nat := 4983230072969 + 3 ^ 40 * 6779580 * 2
def baseEnd_6779580 : Nat := 1160394391869563365257095

theorem tailTrace_6779580 : CollatzResearch.WordTrace tailWord_6779580 prefixEnd_6779580 1160394391869563365257095 := by
  unfold tailWord_6779580
  simp only [CollatzResearch.WordTrace]
  refine ⟨123635798389373497463580097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164847731185831329951440129 123635798389373497463580097)
  ·
    refine ⟨92726848792030123097685073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123635798389373497463580097 92726848792030123097685073)
    ·
      refine ⟨69545136594022592323263805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92726848792030123097685073 69545136594022592323263805)
      ·
        refine ⟨26079426222758472121223927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69545136594022592323263805 26079426222758472121223927)
        ·
          refine ⟨39119139334137708181835891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26079426222758472121223927 39119139334137708181835891)
          ·
            refine ⟨58678709001206562272753837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39119139334137708181835891 58678709001206562272753837)
            ·
              refine ⟨22004515875452460852282689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58678709001206562272753837 22004515875452460852282689)
              ·
                refine ⟨16503386906589345639212017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22004515875452460852282689 16503386906589345639212017)
                ·
                  refine ⟨12377540179942009229409013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16503386906589345639212017 12377540179942009229409013)
                  ·
                    refine ⟨1160394391869563365257095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12377540179942009229409013 1160394391869563365257095)
                    ·
                      rfl

theorem cell23_6779580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_6779580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779580 prefixEnd_6779580 := by exact prefixLift 6779580
  have htrace : WordTrace (prefixWord ++ tailWord_6779580) baseStart_6779580 baseEnd_6779580 := by
    simpa [prefixWord, tailWord_6779580, baseEnd_6779580] using wordTrace_append hprefix tailTrace_6779580
  have hstable : (prefixWord ++ tailWord_6779580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779580).length < 2 ^ (prefixWord ++ tailWord_6779580).sum := by decide
  have hdescent : baseEnd_6779580 < baseStart_6779580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779600 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 6, 4, 2]
def baseStart_6779600 : Nat := 118140960795 + 6779600 * 2 ^ 59
def prefixEnd_6779600 : Nat := 4983230072969 + 3 ^ 40 * 6779600 * 2
def baseEnd_6779600 : Nat := 3481193445221780017521193

theorem tailTrace_6779600 : CollatzResearch.WordTrace tailWord_6779600 prefixEnd_6779600 3481193445221780017521193 := by
  unfold tailWord_6779600
  simp only [CollatzResearch.WordTrace]
  refine ⟨123636163119337269171444127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164848217492449692228592169 123636163119337269171444127)
  ·
    refine ⟨185454244679005903757166191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123636163119337269171444127 185454244679005903757166191)
    ·
      refine ⟨278181367018508855635749287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185454244679005903757166191 278181367018508855635749287)
      ·
        refine ⟨417272050527763283453623931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278181367018508855635749287 417272050527763283453623931)
        ·
          refine ⟨625908075791644925180435897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417272050527763283453623931 625908075791644925180435897)
          ·
            refine ⟨469431056843733693885326923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625908075791644925180435897 469431056843733693885326923)
            ·
              refine ⟨704146585265600540827990385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469431056843733693885326923 704146585265600540827990385)
              ·
                refine ⟨528109938949200405620992789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704146585265600540827990385 528109938949200405620992789)
                ·
                  refine ⟨24755153388243769013484037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 528109938949200405620992789 24755153388243769013484037)
                  ·
                    refine ⟨4641591260295706690028257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24755153388243769013484037 4641591260295706690028257)
                    ·
                      refine ⟨3481193445221780017521193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4641591260295706690028257 3481193445221780017521193)
                      ·
                        rfl

theorem cell23_6779600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 4, 2].length) (baseStart_6779600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779600 prefixEnd_6779600 := by exact prefixLift 6779600
  have htrace : WordTrace (prefixWord ++ tailWord_6779600) baseStart_6779600 baseEnd_6779600 := by
    simpa [prefixWord, tailWord_6779600, baseEnd_6779600] using wordTrace_append hprefix tailTrace_6779600
  have hstable : (prefixWord ++ tailWord_6779600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779600).length < 2 ^ (prefixWord ++ tailWord_6779600).sum := by decide
  have hdescent : baseEnd_6779600 < baseStart_6779600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779610 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 5, 4]
def baseStart_6779610 : Nat := 118140960795 + 6779610 * 2 ^ 59
def prefixEnd_6779610 : Nat := 4983230072969 + 3 ^ 40 * 6779610 * 2
def baseEnd_6779610 : Nat := 1160399526676108326132049

theorem tailTrace_6779610 : CollatzResearch.WordTrace tailWord_6779610 prefixEnd_6779610 1160399526676108326132049 := by
  unfold tailWord_6779610
  simp only [CollatzResearch.WordTrace]
  refine ⟨61818172742159577512688071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164848460645758873367168189 61818172742159577512688071)
  ·
    refine ⟨92727259113239366269032107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61818172742159577512688071 92727259113239366269032107)
    ·
      refine ⟨139090888669859049403548161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92727259113239366269032107 139090888669859049403548161)
      ·
        refine ⟨104318166502394287052661121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139090888669859049403548161 104318166502394287052661121)
        ·
          refine ⟨78238624876795715289495841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104318166502394287052661121 78238624876795715289495841)
          ·
            refine ⟨58678968657596786467121881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78238624876795715289495841 58678968657596786467121881)
            ·
              refine ⟨44009226493197589850341411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58678968657596786467121881 44009226493197589850341411)
              ·
                refine ⟨66013839739796384775512117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44009226493197589850341411 66013839739796384775512117)
                ·
                  refine ⟨6188797475605911072704261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66013839739796384775512117 6188797475605911072704261)
                  ·
                    refine ⟨1160399526676108326132049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6188797475605911072704261 1160399526676108326132049)
                    ·
                      rfl

theorem cell23_6779610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_6779610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779610 prefixEnd_6779610 := by exact prefixLift 6779610
  have htrace : WordTrace (prefixWord ++ tailWord_6779610) baseStart_6779610 baseEnd_6779610 := by
    simpa [prefixWord, tailWord_6779610, baseEnd_6779610] using wordTrace_append hprefix tailTrace_6779610
  have hstable : (prefixWord ++ tailWord_6779610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779610).length < 2 ^ (prefixWord ++ tailWord_6779610).sum := by decide
  have hdescent : baseEnd_6779610 < baseStart_6779610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779617 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_6779617 : Nat := 118140960795 + 6779617 * 2 ^ 59
def prefixEnd_6779617 : Nat := 4983230072969 + 3 ^ 40 * 6779617 * 2
def baseEnd_6779617 : Nat := 3481202174392906451008615

theorem tailTrace_6779617 : CollatzResearch.WordTrace tailWord_6779617 prefixEnd_6779617 3481202174392906451008615 := by
  unfold tailWord_6779617
  simp only [CollatzResearch.WordTrace]
  refine ⟨247272946279612950246257105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164848630853075300164171403 247272946279612950246257105)
  ·
    refine ⟨185454709709709712684692829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247272946279612950246257105 185454709709709712684692829)
    ·
      refine ⟨69545516141141142256759811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185454709709709712684692829 69545516141141142256759811)
      ·
        refine ⟨104318274211711713385139717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69545516141141142256759811 104318274211711713385139717)
        ·
          refine ⟨19559676414695946259713697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104318274211711713385139717 19559676414695946259713697)
          ·
            refine ⟨14669757311021959694785273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19559676414695946259713697 14669757311021959694785273)
            ·
              refine ⟨11002317983266469771088955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14669757311021959694785273 11002317983266469771088955)
              ·
                refine ⟨16503476974899704656633433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11002317983266469771088955 16503476974899704656633433)
                ·
                  refine ⟨12377607731174778492475075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16503476974899704656633433 12377607731174778492475075)
                  ·
                    refine ⟨18566411596762167738712613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12377607731174778492475075 18566411596762167738712613)
                    ·
                      refine ⟨3481202174392906451008615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18566411596762167738712613 3481202174392906451008615)
                      ·
                        rfl

theorem cell23_6779617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_6779617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779617 prefixEnd_6779617 := by exact prefixLift 6779617
  have htrace : WordTrace (prefixWord ++ tailWord_6779617) baseStart_6779617 baseEnd_6779617 := by
    simpa [prefixWord, tailWord_6779617, baseEnd_6779617] using wordTrace_append hprefix tailTrace_6779617
  have hstable : (prefixWord ++ tailWord_6779617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779617).length < 2 ^ (prefixWord ++ tailWord_6779617).sum := by decide
  have hdescent : baseEnd_6779617 < baseStart_6779617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779627 : List Nat := [1, 1, 1, 1, 2, 4, 1, 7, 1, 4]
def baseStart_6779627 : Nat := 118140960795 + 6779627 * 2 ^ 59
def prefixEnd_6779627 : Nat := 4983230072969 + 3 ^ 40 * 6779627 * 2
def baseEnd_6779627 : Nat := 1160402436399817137294523

theorem tailTrace_6779627 : CollatzResearch.WordTrace tailWord_6779627 prefixEnd_6779627 1160402436399817137294523 := by
  unfold tailWord_6779627
  simp only [CollatzResearch.WordTrace]
  refine ⟨247273311009576721954121135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164848874006384481302747423 247273311009576721954121135)
  ·
    refine ⟨370909966514365082931181703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247273311009576721954121135 370909966514365082931181703)
    ·
      refine ⟨556364949771547624396772555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370909966514365082931181703 556364949771547624396772555)
      ·
        refine ⟨834547424657321436595158833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556364949771547624396772555 834547424657321436595158833)
        ·
          refine ⟨625910568492991077446369125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 834547424657321436595158833 625910568492991077446369125)
          ·
            refine ⟨117358231592435827021194211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 625910568492991077446369125 117358231592435827021194211)
            ·
              refine ⟨176037347388653740531791317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117358231592435827021194211 176037347388653740531791317)
              ·
                refine ⟨4125875329421572043713859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 176037347388653740531791317 4125875329421572043713859)
                ·
                  refine ⟨6188812994132358065570789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125875329421572043713859 6188812994132358065570789)
                  ·
                    refine ⟨1160402436399817137294523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6188812994132358065570789 1160402436399817137294523)
                    ·
                      rfl

theorem cell23_6779627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 1, 4].length) (baseStart_6779627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779627 prefixEnd_6779627 := by exact prefixLift 6779627
  have htrace : WordTrace (prefixWord ++ tailWord_6779627) baseStart_6779627 baseEnd_6779627 := by
    simpa [prefixWord, tailWord_6779627, baseEnd_6779627] using wordTrace_append hprefix tailTrace_6779627
  have hstable : (prefixWord ++ tailWord_6779627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779627).length < 2 ^ (prefixWord ++ tailWord_6779627).sum := by decide
  have hdescent : baseEnd_6779627 < baseStart_6779627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779640 : List Nat := [2, 1, 2, 1, 1, 2, 6, 2, 6]
def baseStart_6779640 : Nat := 118140960795 + 6779640 * 2 ^ 59
def prefixEnd_6779640 : Nat := 4983230072969 + 3 ^ 40 * 6779640 * 2
def baseEnd_6779640 : Nat := 386801553827551095669001

theorem tailTrace_6779640 : CollatzResearch.WordTrace tailWord_6779640 prefixEnd_6779640 386801553827551095669001 := by
  unfold tailWord_6779640
  simp only [CollatzResearch.WordTrace]
  refine ⟨123636892579264812587172187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164849190105686416782896249 123636892579264812587172187)
  ·
    refine ⟨185455338868897218880758281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123636892579264812587172187 185455338868897218880758281)
    ·
      refine ⟨139091504151672914160568711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185455338868897218880758281 139091504151672914160568711)
      ·
        refine ⟨208637256227509371240853067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139091504151672914160568711 208637256227509371240853067)
        ·
          refine ⟨312955884341264056861279601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208637256227509371240853067 312955884341264056861279601)
          ·
            refine ⟨234716913255948042645959701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312955884341264056861279601 234716913255948042645959701)
            ·
              refine ⟨11002355308872564499029361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234716913255948042645959701 11002355308872564499029361)
              ·
                refine ⟨8251766481654423374272021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11002355308872564499029361 8251766481654423374272021)
                ·
                  refine ⟨386801553827551095669001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8251766481654423374272021 386801553827551095669001)
                  ·
                    rfl

theorem cell23_6779640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 6].length) (baseStart_6779640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779640 prefixEnd_6779640 := by exact prefixLift 6779640
  have htrace : WordTrace (prefixWord ++ tailWord_6779640) baseStart_6779640 baseEnd_6779640 := by
    simpa [prefixWord, tailWord_6779640, baseEnd_6779640] using wordTrace_append hprefix tailTrace_6779640
  have hstable : (prefixWord ++ tailWord_6779640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779640).length < 2 ^ (prefixWord ++ tailWord_6779640).sum := by decide
  have hdescent : baseEnd_6779640 < baseStart_6779640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779644 : List Nat := [2, 2, 2, 1, 3, 3, 1, 4, 1, 4]
def baseStart_6779644 : Nat := 118140960795 + 6779644 * 2 ^ 59
def prefixEnd_6779644 : Nat := 4983230072969 + 3 ^ 40 * 6779644 * 2
def baseEnd_6779644 : Nat := 1160405346123525948456997

theorem tailTrace_6779644 : CollatzResearch.WordTrace tailWord_6779644 prefixEnd_6779644 1160405346123525948456997 := by
  unfold tailWord_6779644
  simp only [CollatzResearch.WordTrace]
  refine ⟨123636965525257566928744993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164849287367010089238326657 123636965525257566928744993)
  ·
    refine ⟨92727724143943175196558745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123636965525257566928744993 92727724143943175196558745)
    ·
      refine ⟨69545793107957381397419059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92727724143943175196558745 69545793107957381397419059)
      ·
        refine ⟨104318689661936072096128589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69545793107957381397419059 104318689661936072096128589)
        ·
          refine ⟨39119508623226027036048221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104318689661936072096128589 39119508623226027036048221)
          ·
            refine ⟨14669815733709760138518083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39119508623226027036048221 14669815733709760138518083)
            ·
              refine ⟨22004723600564640207777125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14669815733709760138518083 22004723600564640207777125)
              ·
                refine ⟨4125885675105870038958211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22004723600564640207777125 4125885675105870038958211)
                ·
                  refine ⟨6188828512658805058437317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125885675105870038958211 6188828512658805058437317)
                  ·
                    refine ⟨1160405346123525948456997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6188828512658805058437317 1160405346123525948456997)
                    ·
                      rfl

theorem cell23_6779644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_6779644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779644 prefixEnd_6779644 := by exact prefixLift 6779644
  have htrace : WordTrace (prefixWord ++ tailWord_6779644) baseStart_6779644 baseEnd_6779644 := by
    simpa [prefixWord, tailWord_6779644, baseEnd_6779644] using wordTrace_append hprefix tailTrace_6779644
  have hstable : (prefixWord ++ tailWord_6779644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779644).length < 2 ^ (prefixWord ++ tailWord_6779644).sum := by decide
  have hdescent : baseEnd_6779644 < baseStart_6779644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779663 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 7]
def baseStart_6779663 : Nat := 118140960795 + 6779663 * 2 ^ 59
def prefixEnd_6779663 : Nat := 4983230072969 + 3 ^ 40 * 6779663 * 2
def baseEnd_6779663 : Nat := 3481225794503013271033403

theorem tailTrace_6779663 : CollatzResearch.WordTrace tailWord_6779663 prefixEnd_6779663 3481225794503013271033403 := by
  unfold tailWord_6779663
  simp only [CollatzResearch.WordTrace]
  refine ⟨247274624037446300102431643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164849749358297533401621095 247274624037446300102431643)
  ·
    refine ⟨370911936056169450153647465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247274624037446300102431643 370911936056169450153647465)
    ·
      refine ⟨278183952042127087615235599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370911936056169450153647465 278183952042127087615235599)
      ·
        refine ⟨417275928063190631422853399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278183952042127087615235599 417275928063190631422853399)
        ·
          refine ⟨625913892094785947134280099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417275928063190631422853399 625913892094785947134280099)
          ·
            refine ⟨938870838142178920701420149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625913892094785947134280099 938870838142178920701420149)
            ·
              refine ⟨88019141075829273815758139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 938870838142178920701420149 88019141075829273815758139)
              ·
                refine ⟨132028711613743910723637209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88019141075829273815758139 132028711613743910723637209)
                ·
                  refine ⟨99021533710307933042727907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132028711613743910723637209 99021533710307933042727907)
                  ·
                    refine ⟨148532300565461899564091861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99021533710307933042727907 148532300565461899564091861)
                    ·
                      refine ⟨3481225794503013271033403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148532300565461899564091861 3481225794503013271033403)
                      ·
                        rfl

theorem cell23_6779663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_6779663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779663 prefixEnd_6779663 := by exact prefixLift 6779663
  have htrace : WordTrace (prefixWord ++ tailWord_6779663) baseStart_6779663 baseEnd_6779663 := by
    simpa [prefixWord, tailWord_6779663, baseEnd_6779663] using wordTrace_append hprefix tailTrace_6779663
  have hstable : (prefixWord ++ tailWord_6779663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779663).length < 2 ^ (prefixWord ++ tailWord_6779663).sum := by decide
  have hdescent : baseEnd_6779663 < baseStart_6779663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779667 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 3, 1, 3]
def baseStart_6779667 : Nat := 118140960795 + 6779667 * 2 ^ 59
def prefixEnd_6779667 : Nat := 4983230072969 + 3 ^ 40 * 6779667 * 2
def baseEnd_6779667 : Nat := 3481227848425631255383385

theorem tailTrace_6779667 : CollatzResearch.WordTrace tailWord_6779667 prefixEnd_6779667 3481227848425631255383385 := by
  unfold tailWord_6779667
  simp only [CollatzResearch.WordTrace]
  refine ⟨247274769929431808785577255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164849846619621205857051503 247274769929431808785577255)
  ·
    refine ⟨370912154894147713178365883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247274769929431808785577255 370912154894147713178365883)
    ·
      refine ⟨556368232341221569767548825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370912154894147713178365883 556368232341221569767548825)
      ·
        refine ⟨417276174255916177325661619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556368232341221569767548825 417276174255916177325661619)
        ·
          refine ⟨625914261383874265988492429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417276174255916177325661619 625914261383874265988492429)
          ·
            refine ⟨234717848018952849745684661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 625914261383874265988492429 234717848018952849745684661)
            ·
              refine ⟨22004798251776829663657937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 234717848018952849745684661 22004798251776829663657937)
              ·
                refine ⟨16503598688832622247743453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22004798251776829663657937 16503598688832622247743453)
                ·
                  refine ⟨6188849508312233342903795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16503598688832622247743453 6188849508312233342903795)
                  ·
                    refine ⟨9283274262468350014355693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6188849508312233342903795 9283274262468350014355693)
                    ·
                      refine ⟨3481227848425631255383385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9283274262468350014355693 3481227848425631255383385)
                      ·
                        rfl

theorem cell23_6779667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 1, 3].length) (baseStart_6779667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779667 prefixEnd_6779667 := by exact prefixLift 6779667
  have htrace : WordTrace (prefixWord ++ tailWord_6779667) baseStart_6779667 baseEnd_6779667 := by
    simpa [prefixWord, tailWord_6779667, baseEnd_6779667] using wordTrace_append hprefix tailTrace_6779667
  have hstable : (prefixWord ++ tailWord_6779667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779667).length < 2 ^ (prefixWord ++ tailWord_6779667).sum := by decide
  have hdescent : baseEnd_6779667 < baseStart_6779667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779671 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 2, 2, 3]
def baseStart_6779671 : Nat := 118140960795 + 6779671 * 2 ^ 59
def prefixEnd_6779671 : Nat := 4983230072969 + 3 ^ 40 * 6779671 * 2
def baseEnd_6779671 : Nat := 3481229902348249239733367

theorem tailTrace_6779671 : CollatzResearch.WordTrace tailWord_6779671 prefixEnd_6779671 3481229902348249239733367 := by
  unfold tailWord_6779671
  simp only [CollatzResearch.WordTrace]
  refine ⟨247274915821417317468722867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164849943880944878312481911 247274915821417317468722867)
  ·
    refine ⟨370912373732125976203084301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247274915821417317468722867 370912373732125976203084301)
    ·
      refine ⟨139092140149547241076156613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370912373732125976203084301 139092140149547241076156613)
      ·
        refine ⟨26079776278040107701779365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139092140149547241076156613 26079776278040107701779365)
        ·
          refine ⟨4889958052132520194083631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26079776278040107701779365 4889958052132520194083631)
          ·
            refine ⟨7334937078198780291125447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889958052132520194083631 7334937078198780291125447)
            ·
              refine ⟨11002405617298170436688171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7334937078198780291125447 11002405617298170436688171)
              ·
                refine ⟨16503608425947255655032257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11002405617298170436688171 16503608425947255655032257)
                ·
                  refine ⟨12377706319460441741274193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16503608425947255655032257 12377706319460441741274193)
                  ·
                    refine ⟨9283279739595331305955645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12377706319460441741274193 9283279739595331305955645)
                    ·
                      refine ⟨3481229902348249239733367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9283279739595331305955645 3481229902348249239733367)
                      ·
                        rfl

theorem cell23_6779671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_6779671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779671 prefixEnd_6779671 := by exact prefixLift 6779671
  have htrace : WordTrace (prefixWord ++ tailWord_6779671) baseStart_6779671 baseEnd_6779671 := by
    simpa [prefixWord, tailWord_6779671, baseEnd_6779671] using wordTrace_append hprefix tailTrace_6779671
  have hstable : (prefixWord ++ tailWord_6779671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779671).length < 2 ^ (prefixWord ++ tailWord_6779671).sum := by decide
  have hdescent : baseEnd_6779671 < baseStart_6779671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779701 : List Nat := [1, 3, 3, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_6779701 : Nat := 118140960795 + 6779701 * 2 ^ 59
def prefixEnd_6779701 : Nat := 4983230072969 + 3 ^ 40 * 6779701 * 2
def baseEnd_6779701 : Nat := 3481245306767884122358229

theorem tailTrace_6779701 : CollatzResearch.WordTrace tailWord_6779701 prefixEnd_6779701 3481245306767884122358229 := by
  unfold tailWord_6779701
  simp only [CollatzResearch.WordTrace]
  refine ⟨247276010011308632592314957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164850673340872421728209971 247276010011308632592314957)
  ·
    refine ⟨92728503754240737222118109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247276010011308632592314957 92728503754240737222118109)
    ·
      refine ⟨34773188907840276458294291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92728503754240737222118109 34773188907840276458294291)
      ·
        refine ⟨52159783361760414687441437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34773188907840276458294291 52159783361760414687441437)
        ·
          refine ⟨19559918760660155507790539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52159783361760414687441437 19559918760660155507790539)
          ·
            refine ⟨29339878140990233261685809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19559918760660155507790539 29339878140990233261685809)
            ·
              refine ⟨22004908605742674946264357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29339878140990233261685809 22004908605742674946264357)
              ·
                refine ⟨4125920363576751552424567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22004908605742674946264357 4125920363576751552424567)
                ·
                  refine ⟨6188880545365127328636851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125920363576751552424567 6188880545365127328636851)
                  ·
                    refine ⟨9283320818047690992955277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6188880545365127328636851 9283320818047690992955277)
                    ·
                      refine ⟨3481245306767884122358229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9283320818047690992955277 3481245306767884122358229)
                      ·
                        rfl

theorem cell23_6779701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_6779701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779701 prefixEnd_6779701 := by exact prefixLift 6779701
  have htrace : WordTrace (prefixWord ++ tailWord_6779701) baseStart_6779701 baseEnd_6779701 := by
    simpa [prefixWord, tailWord_6779701, baseEnd_6779701] using wordTrace_append hprefix tailTrace_6779701
  have hstable : (prefixWord ++ tailWord_6779701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779701).length < 2 ^ (prefixWord ++ tailWord_6779701).sum := by decide
  have hdescent : baseEnd_6779701 < baseStart_6779701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779720 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_6779720 : Nat := 118140960795 + 6779720 * 2 ^ 59
def prefixEnd_6779720 : Nat := 4983230072969 + 3 ^ 40 * 6779720 * 2
def baseEnd_6779720 : Nat := 3481255062900319548020641

theorem tailTrace_6779720 : CollatzResearch.WordTrace tailWord_6779720 prefixEnd_6779720 3481255062900319548020641 := by
  unfold tailWord_6779720
  simp only [CollatzResearch.WordTrace]
  refine ⟨123638351499119899418628307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164851135332159865891504409 123638351499119899418628307)
  ·
    refine ⟨185457527248679849127942461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123638351499119899418628307 185457527248679849127942461)
    ·
      refine ⟨69546572718254943422978423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185457527248679849127942461 69546572718254943422978423)
      ·
        refine ⟨104319859077382415134467635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69546572718254943422978423 104319859077382415134467635)
        ·
          refine ⟨156479788616073622701701453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104319859077382415134467635 156479788616073622701701453)
          ·
            refine ⟨58679920731027608513138045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156479788616073622701701453 58679920731027608513138045)
            ·
              refine ⟨22004970274135353192426767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58679920731027608513138045 22004970274135353192426767)
              ·
                refine ⟨33007455411203029788640151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22004970274135353192426767 33007455411203029788640151)
                ·
                  refine ⟨49511183116804544682960227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33007455411203029788640151 49511183116804544682960227)
                  ·
                    refine ⟨74266774675206817024440341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49511183116804544682960227 74266774675206817024440341)
                    ·
                      refine ⟨3481255062900319548020641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74266774675206817024440341 3481255062900319548020641)
                      ·
                        rfl

theorem cell23_6779720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_6779720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779720 prefixEnd_6779720 := by exact prefixLift 6779720
  have htrace : WordTrace (prefixWord ++ tailWord_6779720) baseStart_6779720 baseEnd_6779720 := by
    simpa [prefixWord, tailWord_6779720, baseEnd_6779720] using wordTrace_append hprefix tailTrace_6779720
  have hstable : (prefixWord ++ tailWord_6779720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779720).length < 2 ^ (prefixWord ++ tailWord_6779720).sum := by decide
  have hdescent : baseEnd_6779720 < baseStart_6779720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779724 : List Nat := [2, 2, 1, 3, 3, 2, 2, 2, 1, 1, 4]
def baseStart_6779724 : Nat := 118140960795 + 6779724 * 2 ^ 59
def prefixEnd_6779724 : Nat := 4983230072969 + 3 ^ 40 * 6779724 * 2
def baseEnd_6779724 : Nat := 3481257116822937532370623

theorem tailTrace_6779724 : CollatzResearch.WordTrace tailWord_6779724 prefixEnd_6779724 3481257116822937532370623 := by
  unfold tailWord_6779724
  simp only [CollatzResearch.WordTrace]
  refine ⟨123638424445112653760201113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164851232593483538346934817 123638424445112653760201113)
  ·
    refine ⟨92728818333834490320150835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123638424445112653760201113 92728818333834490320150835)
    ·
      refine ⟨139093227500751735480226253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92728818333834490320150835 139093227500751735480226253)
      ·
        refine ⟨52159960312781900805084845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139093227500751735480226253 52159960312781900805084845)
        ·
          refine ⟨19559985117293212801906817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52159960312781900805084845 19559985117293212801906817)
          ·
            refine ⟨14669988837969909601430113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19559985117293212801906817 14669988837969909601430113)
            ·
              refine ⟨11002491628477432201072585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14669988837969909601430113 11002491628477432201072585)
              ·
                refine ⟨8251868721358074150804439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11002491628477432201072585 8251868721358074150804439)
                ·
                  refine ⟨12377803082037111226206659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8251868721358074150804439 12377803082037111226206659)
                  ·
                    refine ⟨18566704623055666839309989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12377803082037111226206659 18566704623055666839309989)
                    ·
                      refine ⟨3481257116822937532370623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18566704623055666839309989 3481257116822937532370623)
                      ·
                        rfl

theorem cell23_6779724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_6779724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779724 prefixEnd_6779724 := by exact prefixLift 6779724
  have htrace : WordTrace (prefixWord ++ tailWord_6779724) baseStart_6779724 baseEnd_6779724 := by
    simpa [prefixWord, tailWord_6779724, baseEnd_6779724] using wordTrace_append hprefix tailTrace_6779724
  have hstable : (prefixWord ++ tailWord_6779724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779724).length < 2 ^ (prefixWord ++ tailWord_6779724).sum := by decide
  have hdescent : baseEnd_6779724 < baseStart_6779724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779730 : List Nat := [3, 2, 2, 1, 1, 2, 3, 9]
def baseStart_6779730 : Nat := 118140960795 + 6779730 * 2 ^ 59
def prefixEnd_6779730 : Nat := 4983230072969 + 3 ^ 40 * 6779730 * 2
def baseEnd_6779730 : Nat := 128935562878032018847985

theorem tailTrace_6779730 : CollatzResearch.WordTrace tailWord_6779730 prefixEnd_6779730 128935562878032018847985 := by
  unfold tailWord_6779730
  simp only [CollatzResearch.WordTrace]
  refine ⟨61819266932050892636280161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164851378485469047030080429 61819266932050892636280161)
  ·
    refine ⟨46364450199038169477210121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61819266932050892636280161 46364450199038169477210121)
    ·
      refine ⟨34773337649278627107907591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46364450199038169477210121 34773337649278627107907591)
      ·
        refine ⟨52160006473917940661861387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34773337649278627107907591 52160006473917940661861387)
        ·
          refine ⟨78240009710876910992792081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52160006473917940661861387 78240009710876910992792081)
          ·
            refine ⟨58680007283157683244594061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78240009710876910992792081 58680007283157683244594061)
            ·
              refine ⟨22005002731184131216722773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58680007283157683244594061 22005002731184131216722773)
              ·
                refine ⟨128935562878032018847985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22005002731184131216722773 128935562878032018847985)
                ·
                  rfl

theorem cell23_6779730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 9].length) (baseStart_6779730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779730 prefixEnd_6779730 := by exact prefixLift 6779730
  have htrace : WordTrace (prefixWord ++ tailWord_6779730) baseStart_6779730 baseEnd_6779730 := by
    simpa [prefixWord, tailWord_6779730, baseEnd_6779730] using wordTrace_append hprefix tailTrace_6779730
  have hstable : (prefixWord ++ tailWord_6779730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779730).length < 2 ^ (prefixWord ++ tailWord_6779730).sum := by decide
  have hdescent : baseEnd_6779730 < baseStart_6779730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779778 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_6779778 : Nat := 118140960795 + 6779778 * 2 ^ 59
def prefixEnd_6779778 : Nat := 4983230072969 + 3 ^ 40 * 6779778 * 2
def baseEnd_6779778 : Nat := 3481284844778280321095375

theorem tailTrace_6779778 : CollatzResearch.WordTrace tailWord_6779778 prefixEnd_6779778 3481284844778280321095375 := by
  unfold tailWord_6779778
  simp only [CollatzResearch.WordTrace]
  refine ⟨61819704608007418685716997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164852545621353116495245325 61819704608007418685716997)
  ·
    refine ⟨11591194614001391003571937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61819704608007418685716997 11591194614001391003571937)
    ·
      refine ⟨8693395960501043252678953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11591194614001391003571937 8693395960501043252678953)
      ·
        refine ⟨6520046970375782439509215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8693395960501043252678953 6520046970375782439509215)
        ·
          refine ⟨9780070455563673659263823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6520046970375782439509215 9780070455563673659263823)
          ·
            refine ⟨14670105683345510488895735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9780070455563673659263823 14670105683345510488895735)
            ·
              refine ⟨22005158525018265733343603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14670105683345510488895735 22005158525018265733343603)
              ·
                refine ⟨33007737787527398600015405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22005158525018265733343603 33007737787527398600015405)
                ·
                  refine ⟨12377901670322774475005777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33007737787527398600015405 12377901670322774475005777)
                  ·
                    refine ⟨9283426252742080856254333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12377901670322774475005777 9283426252742080856254333)
                    ·
                      refine ⟨3481284844778280321095375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9283426252742080856254333 3481284844778280321095375)
                      ·
                        rfl

theorem cell23_6779778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_6779778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779778 prefixEnd_6779778 := by exact prefixLift 6779778
  have htrace : WordTrace (prefixWord ++ tailWord_6779778) baseStart_6779778 baseEnd_6779778 := by
    simpa [prefixWord, tailWord_6779778, baseEnd_6779778] using wordTrace_append hprefix tailTrace_6779778
  have hstable : (prefixWord ++ tailWord_6779778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779778).length < 2 ^ (prefixWord ++ tailWord_6779778).sum := by decide
  have hdescent : baseEnd_6779778 < baseStart_6779778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779780 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_6779780 : Nat := 118140960795 + 6779780 * 2 ^ 59
def prefixEnd_6779780 : Nat := 4983230072969 + 3 ^ 40 * 6779780 * 2
def baseEnd_6779780 : Nat := 3481285871739589313270365

theorem tailTrace_6779780 : CollatzResearch.WordTrace tailWord_6779780 prefixEnd_6779780 3481285871739589313270365 := by
  unfold tailWord_6779780
  simp only [CollatzResearch.WordTrace]
  refine ⟨123639445689011214542220397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164852594252014952722960529 123639445689011214542220397)
  ·
    refine ⟨46364792133379205453332649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123639445689011214542220397 46364792133379205453332649)
    ·
      refine ⟨34773594100034404089999487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46364792133379205453332649 34773594100034404089999487)
      ·
        refine ⟨52160391150051606134999231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34773594100034404089999487 52160391150051606134999231)
        ·
          refine ⟨78240586725077409202498847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52160391150051606134999231 78240586725077409202498847)
          ·
            refine ⟨117360880087616113803748271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78240586725077409202498847 117360880087616113803748271)
            ·
              refine ⟨176041320131424170705622407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117360880087616113803748271 176041320131424170705622407)
              ·
                refine ⟨264061980197136256058433611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176041320131424170705622407 264061980197136256058433611)
                ·
                  refine ⟨396092970295704384087650417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264061980197136256058433611 396092970295704384087650417)
                  ·
                    refine ⟨297069727721778288065737813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 396092970295704384087650417 297069727721778288065737813)
                    ·
                      refine ⟨3481285871739589313270365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 297069727721778288065737813 3481285871739589313270365)
                      ·
                        rfl

theorem cell23_6779780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_6779780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779780 prefixEnd_6779780 := by exact prefixLift 6779780
  have htrace : WordTrace (prefixWord ++ tailWord_6779780) baseStart_6779780 baseEnd_6779780 := by
    simpa [prefixWord, tailWord_6779780, baseEnd_6779780] using wordTrace_append hprefix tailTrace_6779780
  have hstable : (prefixWord ++ tailWord_6779780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779780).length < 2 ^ (prefixWord ++ tailWord_6779780).sum := by decide
  have hdescent : baseEnd_6779780 < baseStart_6779780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779831 : List Nat := [1, 1, 3, 1, 3, 1, 4, 3, 2, 2, 2]
def baseStart_6779831 : Nat := 118140960795 + 6779831 * 2 ^ 59
def prefixEnd_6779831 : Nat := 4983230072969 + 3 ^ 40 * 6779831 * 2
def baseEnd_6779831 : Nat := 3481312059252968613732631

theorem tailTrace_6779831 : CollatzResearch.WordTrace tailWord_6779831 prefixEnd_6779831 3481312059252968613732631 := by
  unfold tailWord_6779831
  simp only [CollatzResearch.WordTrace]
  refine ⟨247280751500837664794547347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164853834333891776529698231 247280751500837664794547347)
  ·
    refine ⟨370921127251256497191821021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247280751500837664794547347 370921127251256497191821021)
    ·
      refine ⟨139095422719221186446932883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370921127251256497191821021 139095422719221186446932883)
      ·
        refine ⟨208643134078831779670399325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139095422719221186446932883 208643134078831779670399325)
        ·
          refine ⟨78241175279561917376399747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208643134078831779670399325 78241175279561917376399747)
          ·
            refine ⟨117361762919342876064599621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78241175279561917376399747 117361762919342876064599621)
            ·
              refine ⟨22005330547376789262112429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117361762919342876064599621 22005330547376789262112429)
              ·
                refine ⟨8251998955266295973292161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22005330547376789262112429 8251998955266295973292161)
                ·
                  refine ⟨6188999216449721979969121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8251998955266295973292161 6188999216449721979969121)
                  ·
                    refine ⟨4641749412337291484976841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6188999216449721979969121 4641749412337291484976841)
                    ·
                      refine ⟨3481312059252968613732631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4641749412337291484976841 3481312059252968613732631)
                      ·
                        rfl

theorem cell23_6779831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 2, 2].length) (baseStart_6779831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779831 prefixEnd_6779831 := by exact prefixLift 6779831
  have htrace : WordTrace (prefixWord ++ tailWord_6779831) baseStart_6779831 baseEnd_6779831 := by
    simpa [prefixWord, tailWord_6779831, baseEnd_6779831] using wordTrace_append hprefix tailTrace_6779831
  have hstable : (prefixWord ++ tailWord_6779831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779831).length < 2 ^ (prefixWord ++ tailWord_6779831).sum := by decide
  have hdescent : baseEnd_6779831 < baseStart_6779831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779846 : List Nat := [6, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_6779846 : Nat := 118140960795 + 6779846 * 2 ^ 59
def prefixEnd_6779846 : Nat := 4983230072969 + 3 ^ 40 * 6779846 * 2
def baseEnd_6779846 : Nat := 3481319761462786055045063

theorem tailTrace_6779846 : CollatzResearch.WordTrace tailWord_6779846 prefixEnd_6779846 3481319761462786055045063 := by
  unfold tailWord_6779846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7727540581118228823635731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 164854199063855548237562261 7727540581118228823635731)
  ·
    refine ⟨11591310871677343235453597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7727540581118228823635731 11591310871677343235453597)
    ·
      refine ⟨4346741576879003713295099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11591310871677343235453597 4346741576879003713295099)
      ·
        refine ⟨6520112365318505569942649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4346741576879003713295099 6520112365318505569942649)
        ·
          refine ⟨4890084273988879177456987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6520112365318505569942649 4890084273988879177456987)
          ·
            refine ⟨7335126410983318766185481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4890084273988879177456987 7335126410983318766185481)
            ·
              refine ⟨5501344808237489074639111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7335126410983318766185481 5501344808237489074639111)
              ·
                refine ⟨8252017212356233611958667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5501344808237489074639111 8252017212356233611958667)
                ·
                  refine ⟨12378025818534350417938001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8252017212356233611958667 12378025818534350417938001)
                  ·
                    refine ⟨9283519363900762813453501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12378025818534350417938001 9283519363900762813453501)
                    ·
                      refine ⟨3481319761462786055045063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9283519363900762813453501 3481319761462786055045063)
                      ·
                        rfl

theorem cell23_6779846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_6779846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779846 prefixEnd_6779846 := by exact prefixLift 6779846
  have htrace : WordTrace (prefixWord ++ tailWord_6779846) baseStart_6779846 baseEnd_6779846 := by
    simpa [prefixWord, tailWord_6779846, baseEnd_6779846] using wordTrace_append hprefix tailTrace_6779846
  have hstable : (prefixWord ++ tailWord_6779846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779846).length < 2 ^ (prefixWord ++ tailWord_6779846).sum := by decide
  have hdescent : baseEnd_6779846 < baseStart_6779846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779854 : List Nat := [4, 1, 1, 1, 2, 3, 1, 5, 5]
def baseStart_6779854 : Nat := 118140960795 + 6779854 * 2 ^ 59
def prefixEnd_6779854 : Nat := 4983230072969 + 3 ^ 40 * 6779854 * 2
def baseEnd_6779854 : Nat := 386813763256446891527225

theorem tailTrace_6779854 : CollatzResearch.WordTrace tailWord_6779854 prefixEnd_6779854 386813763256446891527225 := by
  unfold tailWord_6779854
  simp only [CollatzResearch.WordTrace]
  refine ⟨30910198797469292465329327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164854393586502893148423077 30910198797469292465329327)
  ·
    refine ⟨46365298196203938697993991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30910198797469292465329327 46365298196203938697993991)
    ·
      refine ⟨69547947294305908046990987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46365298196203938697993991 69547947294305908046990987)
      ·
        refine ⟨104321920941458862070486481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69547947294305908046990987 104321920941458862070486481)
        ·
          refine ⟨78241440706094146552864861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104321920941458862070486481 78241440706094146552864861)
          ·
            refine ⟨29340540264785304957324323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78241440706094146552864861 29340540264785304957324323)
            ·
              refine ⟨44010810397177957435986485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29340540264785304957324323 44010810397177957435986485)
              ·
                refine ⟨4126013474735433509623733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44010810397177957435986485 4126013474735433509623733)
                ·
                  refine ⟨386813763256446891527225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4126013474735433509623733 386813763256446891527225)
                  ·
                    rfl

theorem cell23_6779854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_6779854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779854 prefixEnd_6779854 := by exact prefixLift 6779854
  have htrace : WordTrace (prefixWord ++ tailWord_6779854) baseStart_6779854 baseEnd_6779854 := by
    simpa [prefixWord, tailWord_6779854, baseEnd_6779854] using wordTrace_append hprefix tailTrace_6779854
  have hstable : (prefixWord ++ tailWord_6779854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779854).length < 2 ^ (prefixWord ++ tailWord_6779854).sum := by decide
  have hdescent : baseEnd_6779854 < baseStart_6779854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779887 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 4]
def baseStart_6779887 : Nat := 118140960795 + 6779887 * 2 ^ 59
def prefixEnd_6779887 : Nat := 4983230072969 + 3 ^ 40 * 6779887 * 2
def baseEnd_6779887 : Nat := 3481340814169620394632373

theorem tailTrace_6779887 : CollatzResearch.WordTrace tailWord_6779887 prefixEnd_6779887 3481340814169620394632373 := by
  unfold tailWord_6779887
  simp only [CollatzResearch.WordTrace]
  refine ⟨247282793988634786358585915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164855195992423190905723943 247282793988634786358585915)
  ·
    refine ⟨370924190982952179537878873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247282793988634786358585915 370924190982952179537878873)
    ·
      refine ⟨278193143237214134653409155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370924190982952179537878873 278193143237214134653409155)
      ·
        refine ⟨417289714855821201980113733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278193143237214134653409155 417289714855821201980113733)
        ·
          refine ⟨78241821535466475371271325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 417289714855821201980113733 78241821535466475371271325)
          ·
            refine ⟨29340683075799928264226747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78241821535466475371271325 29340683075799928264226747)
            ·
              refine ⟨44011024613699892396340121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29340683075799928264226747 44011024613699892396340121)
              ·
                refine ⟨33008268460274919297255091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44011024613699892396340121 33008268460274919297255091)
                ·
                  refine ⟨49512402690412378945882637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33008268460274919297255091 49512402690412378945882637)
                  ·
                    refine ⟨18567151008904642104705989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49512402690412378945882637 18567151008904642104705989)
                    ·
                      refine ⟨3481340814169620394632373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18567151008904642104705989 3481340814169620394632373)
                      ·
                        rfl

theorem cell23_6779887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_6779887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779887 prefixEnd_6779887 := by exact prefixLift 6779887
  have htrace : WordTrace (prefixWord ++ tailWord_6779887) baseStart_6779887 baseEnd_6779887 := by
    simpa [prefixWord, tailWord_6779887, baseEnd_6779887] using wordTrace_append hprefix tailTrace_6779887
  have hstable : (prefixWord ++ tailWord_6779887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779887).length < 2 ^ (prefixWord ++ tailWord_6779887).sum := by decide
  have hdescent : baseEnd_6779887 < baseStart_6779887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779922 : List Nat := [3, 2, 5, 1, 1, 1, 3, 2, 5]
def baseStart_6779922 : Nat := 118140960795 + 6779922 * 2 ^ 59
def prefixEnd_6779922 : Nat := 4983230072969 + 3 ^ 40 * 6779922 * 2
def baseEnd_6779922 : Nat := 386817642888058639743857

theorem tailTrace_6779922 : CollatzResearch.WordTrace tailWord_6779922 prefixEnd_6779922 386817642888058639743857 := by
  unfold tailWord_6779922
  simp only [CollatzResearch.WordTrace]
  refine ⟨61821017635876996834027505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164856047029005324890740013 61821017635876996834027505)
  ·
    refine ⟨46365763226907747625520629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61821017635876996834027505 46365763226907747625520629)
    ·
      refine ⟨4346790302522601339892559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46365763226907747625520629 4346790302522601339892559)
      ·
        refine ⟨6520185453783902009838839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4346790302522601339892559 6520185453783902009838839)
        ·
          refine ⟨9780278180675853014758259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6520185453783902009838839 9780278180675853014758259)
          ·
            refine ⟨14670417271013779522137389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9780278180675853014758259 14670417271013779522137389)
            ·
              refine ⟨5501406476630167320801521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14670417271013779522137389 5501406476630167320801521)
              ·
                refine ⟨4126054857472625490601141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5501406476630167320801521 4126054857472625490601141)
                ·
                  refine ⟨386817642888058639743857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4126054857472625490601141 386817642888058639743857)
                  ·
                    rfl

theorem cell23_6779922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_6779922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779922 prefixEnd_6779922 := by exact prefixLift 6779922
  have htrace : WordTrace (prefixWord ++ tailWord_6779922) baseStart_6779922 baseEnd_6779922 := by
    simpa [prefixWord, tailWord_6779922, baseEnd_6779922] using wordTrace_append hprefix tailTrace_6779922
  have hstable : (prefixWord ++ tailWord_6779922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779922).length < 2 ^ (prefixWord ++ tailWord_6779922).sum := by decide
  have hdescent : baseEnd_6779922 < baseStart_6779922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6779958 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_6779958 : Nat := 118140960795 + 6779958 * 2 ^ 59
def prefixEnd_6779958 : Nat := 4983230072969 + 3 ^ 40 * 6779958 * 2
def baseEnd_6779958 : Nat := 3481377271296089616844547

theorem tailTrace_6779958 : CollatzResearch.WordTrace tailWord_6779958 prefixEnd_6779958 3481377271296089616844547 := by
  unfold tailWord_6779958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15455336473211097842776283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164856922380918376989613685 15455336473211097842776283)
  ·
    refine ⟨23183004709816646764164425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15455336473211097842776283 23183004709816646764164425)
    ·
      refine ⟨17387253532362485073123319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23183004709816646764164425 17387253532362485073123319)
      ·
        refine ⟨26080880298543727609684979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17387253532362485073123319 26080880298543727609684979)
        ·
          refine ⟨39121320447815591414527469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26080880298543727609684979 39121320447815591414527469)
          ·
            refine ⟨14670495167930846780447801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39121320447815591414527469 14670495167930846780447801)
            ·
              refine ⟨11002871375948135085335851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14670495167930846780447801 11002871375948135085335851)
              ·
                refine ⟨16504307063922202628003777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11002871375948135085335851 16504307063922202628003777)
                ·
                  refine ⟨12378230297941651971002833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16504307063922202628003777 12378230297941651971002833)
                  ·
                    refine ⟨9283672723456238978252125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12378230297941651971002833 9283672723456238978252125)
                    ·
                      refine ⟨3481377271296089616844547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9283672723456238978252125 3481377271296089616844547)
                      ·
                        rfl

theorem cell23_6779958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_6779958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6779958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6779958 prefixEnd_6779958 := by exact prefixLift 6779958
  have htrace : WordTrace (prefixWord ++ tailWord_6779958) baseStart_6779958 baseEnd_6779958 := by
    simpa [prefixWord, tailWord_6779958, baseEnd_6779958] using wordTrace_append hprefix tailTrace_6779958
  have hstable : (prefixWord ++ tailWord_6779958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6779958).length < 2 ^ (prefixWord ++ tailWord_6779958).sum := by decide
  have hdescent : baseEnd_6779958 < baseStart_6779958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6779958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780004 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_6780004 : Nat := 118140960795 + 6780004 * 2 ^ 59
def prefixEnd_6780004 : Nat := 4983230072969 + 3 ^ 40 * 6780004 * 2
def baseEnd_6780004 : Nat := 1160466963802065478956445

theorem tailTrace_6780004 : CollatzResearch.WordTrace tailWord_6780004 prefixEnd_6780004 1160466963802065478956445 := by
  unfold tailWord_6780004
  simp only [CollatzResearch.WordTrace]
  refine ⟨123643530664605457670297533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164858040886140610227063377 123643530664605457670297533)
  ·
    refine ⟨46366323999227046626361575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123643530664605457670297533 46366323999227046626361575)
    ·
      refine ⟨69549485998840569939542363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46366323999227046626361575 69549485998840569939542363)
      ·
        refine ⟨104324228998260854909313545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69549485998840569939542363 104324228998260854909313545)
        ·
          refine ⟨78243171748695641181985159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104324228998260854909313545 78243171748695641181985159)
          ·
            refine ⟨117364757623043461772977739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78243171748695641181985159 117364757623043461772977739)
            ·
              refine ⟨176047136434565192659466609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117364757623043461772977739 176047136434565192659466609)
              ·
                refine ⟨132035352325923894494599957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176047136434565192659466609 132035352325923894494599957)
                ·
                  refine ⟨6189157140277682554434373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132035352325923894494599957 6189157140277682554434373)
                  ·
                    refine ⟨1160466963802065478956445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6189157140277682554434373 1160466963802065478956445)
                    ·
                      rfl

theorem cell23_6780004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_6780004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780004 prefixEnd_6780004 := by exact prefixLift 6780004
  have htrace : WordTrace (prefixWord ++ tailWord_6780004) baseStart_6780004 baseEnd_6780004 := by
    simpa [prefixWord, tailWord_6780004, baseEnd_6780004] using wordTrace_append hprefix tailTrace_6780004
  have hstable : (prefixWord ++ tailWord_6780004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780004).length < 2 ^ (prefixWord ++ tailWord_6780004).sum := by decide
  have hdescent : baseEnd_6780004 < baseStart_6780004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780024 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_6780024 : Nat := 118140960795 + 6780024 * 2 ^ 59
def prefixEnd_6780024 : Nat := 4983230072969 + 3 ^ 40 * 6780024 * 2
def baseEnd_6780024 : Nat := 3481411161019286358619243

theorem tailTrace_6780024 : CollatzResearch.WordTrace tailWord_6780024 prefixEnd_6780024 3481411161019286358619243 := by
  unfold tailWord_6780024
  simp only [CollatzResearch.WordTrace]
  refine ⟨123643895394569229378161563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164858527192758972504215417 123643895394569229378161563)
  ·
    refine ⟨185465843091853844067242345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123643895394569229378161563 185465843091853844067242345)
    ·
      refine ⟨139099382318890383050431759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185465843091853844067242345 139099382318890383050431759)
      ·
        refine ⟨208649073478335574575647639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139099382318890383050431759 208649073478335574575647639)
        ·
          refine ⟨312973610217503361863471459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208649073478335574575647639 312973610217503361863471459)
          ·
            refine ⟨469460415326255042795207189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312973610217503361863471459 469460415326255042795207189)
            ·
              refine ⟨22005956968418205131025337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 469460415326255042795207189 22005956968418205131025337)
              ·
                refine ⟨16504467726313653848269003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22005956968418205131025337 16504467726313653848269003)
                ·
                  refine ⟨24756701589470480772403505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16504467726313653848269003 24756701589470480772403505)
                  ·
                    refine ⟨18567526192102860579302629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24756701589470480772403505 18567526192102860579302629)
                    ·
                      refine ⟨3481411161019286358619243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18567526192102860579302629 3481411161019286358619243)
                      ·
                        rfl

theorem cell23_6780024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_6780024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780024 prefixEnd_6780024 := by exact prefixLift 6780024
  have htrace : WordTrace (prefixWord ++ tailWord_6780024) baseStart_6780024 baseEnd_6780024 := by
    simpa [prefixWord, tailWord_6780024, baseEnd_6780024] using wordTrace_append hprefix tailTrace_6780024
  have hstable : (prefixWord ++ tailWord_6780024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780024).length < 2 ^ (prefixWord ++ tailWord_6780024).sum := by decide
  have hdescent : baseEnd_6780024 < baseStart_6780024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780025 : List Nat := [1, 2, 1, 3, 6, 1, 2, 1, 1, 5]
def baseStart_6780025 : Nat := 118140960795 + 6780025 * 2 ^ 59
def prefixEnd_6780025 : Nat := 4983230072969 + 3 ^ 40 * 6780025 * 2
def baseEnd_6780025 : Nat := 1160470558166646951568913

theorem tailTrace_6780025 : CollatzResearch.WordTrace tailWord_6780025 prefixEnd_6780025 1160470558166646951568913 := by
  unfold tailWord_6780025
  simp only [CollatzResearch.WordTrace]
  refine ⟨247287827262134835927109529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164858551508089890618073019 247287827262134835927109529)
  ·
    refine ⟨185465870446601126945332147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247287827262134835927109529 185465870446601126945332147)
    ·
      refine ⟨278198805669901690417998221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185465870446601126945332147 278198805669901690417998221)
      ·
        refine ⟨104324552126213133906749333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278198805669901690417998221 104324552126213133906749333)
        ·
          refine ⟨4890213380916240651878875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104324552126213133906749333 4890213380916240651878875)
          ·
            refine ⟨7335320071374360977818313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4890213380916240651878875 7335320071374360977818313)
            ·
              refine ⟨5501490053530770733363735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7335320071374360977818313 5501490053530770733363735)
              ·
                refine ⟨8252235080296156100045603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5501490053530770733363735 8252235080296156100045603)
                ·
                  refine ⟨12378352620444234150068405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8252235080296156100045603 12378352620444234150068405)
                  ·
                    refine ⟨1160470558166646951568913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12378352620444234150068405 1160470558166646951568913)
                    ·
                      rfl

theorem cell23_6780025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 1, 5].length) (baseStart_6780025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780025 prefixEnd_6780025 := by exact prefixLift 6780025
  have htrace : WordTrace (prefixWord ++ tailWord_6780025) baseStart_6780025 baseEnd_6780025 := by
    simpa [prefixWord, tailWord_6780025, baseEnd_6780025] using wordTrace_append hprefix tailTrace_6780025
  have hstable : (prefixWord ++ tailWord_6780025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780025).length < 2 ^ (prefixWord ++ tailWord_6780025).sum := by decide
  have hdescent : baseEnd_6780025 < baseStart_6780025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780044 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 3, 3, 3]
def baseStart_6780044 : Nat := 118140960795 + 6780044 * 2 ^ 59
def prefixEnd_6780044 : Nat := 4983230072969 + 3 ^ 40 * 6780044 * 2
def baseEnd_6780044 : Nat := 3481421430632376280369151

theorem tailTrace_6780044 : CollatzResearch.WordTrace tailWord_6780044 prefixEnd_6780044 3481421430632376280369151 := by
  unfold tailWord_6780044
  simp only [CollatzResearch.WordTrace]
  refine ⟨123644260124533001086025593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164859013499377334781367457 123644260124533001086025593)
  ·
    refine ⟨92733195093399750814519195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123644260124533001086025593 92733195093399750814519195)
    ·
      refine ⟨139099792640099626221778793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92733195093399750814519195 139099792640099626221778793)
      ·
        refine ⟨104324844480074719666334095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139099792640099626221778793 104324844480074719666334095)
        ·
          refine ⟨156487266720112079499501143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104324844480074719666334095 156487266720112079499501143)
          ·
            refine ⟨234730900080168119249251715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156487266720112079499501143 234730900080168119249251715)
            ·
              refine ⟨352096350120252178873877573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234730900080168119249251715 352096350120252178873877573)
              ·
                refine ⟨66018065647547283538852045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352096350120252178873877573 66018065647547283538852045)
                ·
                  refine ⟨24756774617830231327069517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66018065647547283538852045 24756774617830231327069517)
                  ·
                    refine ⟨9283790481686336747651069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24756774617830231327069517 9283790481686336747651069)
                    ·
                      refine ⟨3481421430632376280369151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9283790481686336747651069 3481421430632376280369151)
                      ·
                        rfl

theorem cell23_6780044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_6780044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780044 prefixEnd_6780044 := by exact prefixLift 6780044
  have htrace : WordTrace (prefixWord ++ tailWord_6780044) baseStart_6780044 baseEnd_6780044 := by
    simpa [prefixWord, tailWord_6780044, baseEnd_6780044] using wordTrace_append hprefix tailTrace_6780044
  have hstable : (prefixWord ++ tailWord_6780044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780044).length < 2 ^ (prefixWord ++ tailWord_6780044).sum := by decide
  have hdescent : baseEnd_6780044 < baseStart_6780044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780047 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 6, 7]
def baseStart_6780047 : Nat := 118140960795 + 6780047 * 2 ^ 59
def prefixEnd_6780047 : Nat := 4983230072969 + 3 ^ 40 * 6780047 * 2
def baseEnd_6780047 : Nat := 1160474323691446589543879

theorem tailTrace_6780047 : CollatzResearch.WordTrace tailWord_6780047 prefixEnd_6780047 1160474323691446589543879 := by
  unfold tailWord_6780047
  simp only [CollatzResearch.WordTrace]
  refine ⟨247288629668055133684410395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164859086445370089122940263 247288629668055133684410395)
  ·
    refine ⟨370932944502082700526615593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247288629668055133684410395 370932944502082700526615593)
    ·
      refine ⟨278199708376562025394961695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370932944502082700526615593 278199708376562025394961695)
      ·
        refine ⟨417299562564843038092442543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278199708376562025394961695 417299562564843038092442543)
        ·
          refine ⟨625949343847264557138663815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417299562564843038092442543 625949343847264557138663815)
          ·
            refine ⟨938924015770896835707995723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625949343847264557138663815 938924015770896835707995723)
            ·
              refine ⟨1408386023656345253561993585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938924015770896835707995723 1408386023656345253561993585)
              ·
                refine ⟨1056289517742258940171495189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408386023656345253561993585 1056289517742258940171495189)
                ·
                  refine ⟨49513571144168387820538837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1056289517742258940171495189 49513571144168387820538837)
                  ·
                    refine ⟨1160474323691446589543879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49513571144168387820538837 1160474323691446589543879)
                    ·
                      rfl

theorem cell23_6780047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_6780047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780047 prefixEnd_6780047 := by exact prefixLift 6780047
  have htrace : WordTrace (prefixWord ++ tailWord_6780047) baseStart_6780047 baseEnd_6780047 := by
    simpa [prefixWord, tailWord_6780047, baseEnd_6780047] using wordTrace_append hprefix tailTrace_6780047
  have hstable : (prefixWord ++ tailWord_6780047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780047).length < 2 ^ (prefixWord ++ tailWord_6780047).sum := by decide
  have hdescent : baseEnd_6780047 < baseStart_6780047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780058 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4]
def baseStart_6780058 : Nat := 118140960795 + 6780058 * 2 ^ 59
def prefixEnd_6780058 : Nat := 4983230072969 + 3 ^ 40 * 6780058 * 2
def baseEnd_6780058 : Nat := 3481428619361539225594087

theorem tailTrace_6780058 : CollatzResearch.WordTrace tailWord_6780058 prefixEnd_6780058 3481428619361539225594087 := by
  unfold tailWord_6780058
  simp only [CollatzResearch.WordTrace]
  refine ⟨61822257717753820640765207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164859353914010188375373885 61822257717753820640765207)
  ·
    refine ⟨92733386576630730961147811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61822257717753820640765207 92733386576630730961147811)
    ·
      refine ⟨139100079864946096441721717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92733386576630730961147811 139100079864946096441721717)
      ·
        refine ⟨13040632487338696541411411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139100079864946096441721717 13040632487338696541411411)
        ·
          refine ⟨19560948731008044812117117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13040632487338696541411411 19560948731008044812117117)
          ·
            refine ⟨7335355774128016804543919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19560948731008044812117117 7335355774128016804543919)
            ·
              refine ⟨11003033661192025206815879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7335355774128016804543919 11003033661192025206815879)
              ·
                refine ⟨16504550491788037810223819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11003033661192025206815879 16504550491788037810223819)
                ·
                  refine ⟨24756825737682056715335729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16504550491788037810223819 24756825737682056715335729)
                  ·
                    refine ⟨18567619303261542536501797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24756825737682056715335729 18567619303261542536501797)
                    ·
                      refine ⟨3481428619361539225594087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18567619303261542536501797 3481428619361539225594087)
                      ·
                        rfl

theorem cell23_6780058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_6780058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780058 prefixEnd_6780058 := by exact prefixLift 6780058
  have htrace : WordTrace (prefixWord ++ tailWord_6780058) baseStart_6780058 baseEnd_6780058 := by
    simpa [prefixWord, tailWord_6780058, baseEnd_6780058] using wordTrace_append hprefix tailTrace_6780058
  have hstable : (prefixWord ++ tailWord_6780058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780058).length < 2 ^ (prefixWord ++ tailWord_6780058).sum := by decide
  have hdescent : baseEnd_6780058 < baseStart_6780058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780135 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_6780135 : Nat := 118140960795 + 6780135 * 2 ^ 59
def prefixEnd_6780135 : Nat := 4983230072969 + 3 ^ 40 * 6780135 * 2
def baseEnd_6780135 : Nat := 3481468157371935424331233

theorem tailTrace_6780135 : CollatzResearch.WordTrace tailWord_6780135 prefixEnd_6780135 3481468157371935424331233 := by
  unfold tailWord_6780135
  simp only [CollatzResearch.WordTrace]
  refine ⟨247291839291736324713613859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164861226194490883142409239 247291839291736324713613859)
  ·
    refine ⟨370937758937604487070420789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247291839291736324713613859 370937758937604487070420789)
    ·
      refine ⟨34775414900400420662851949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 370937758937604487070420789 34775414900400420662851949)
      ·
        refine ⟨13040780587650157748569481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34775414900400420662851949 13040780587650157748569481)
        ·
          refine ⟨9780585440737618311427111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13040780587650157748569481 9780585440737618311427111)
          ·
            refine ⟨14670878161106427467140667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9780585440737618311427111 14670878161106427467140667)
            ·
              refine ⟨22006317241659641200711001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14670878161106427467140667 22006317241659641200711001)
              ·
                refine ⟨16504737931244730900533251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22006317241659641200711001 16504737931244730900533251)
                ·
                  refine ⟨24757106896867096350799877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16504737931244730900533251 24757106896867096350799877)
                  ·
                    refine ⟨4641957543162580565774977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24757106896867096350799877 4641957543162580565774977)
                    ·
                      refine ⟨3481468157371935424331233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4641957543162580565774977 3481468157371935424331233)
                      ·
                        rfl

theorem cell23_6780135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_6780135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780135 prefixEnd_6780135 := by exact prefixLift 6780135
  have htrace : WordTrace (prefixWord ++ tailWord_6780135) baseStart_6780135 baseEnd_6780135 := by
    simpa [prefixWord, tailWord_6780135, baseEnd_6780135] using wordTrace_append hprefix tailTrace_6780135
  have hstable : (prefixWord ++ tailWord_6780135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780135).length < 2 ^ (prefixWord ++ tailWord_6780135).sum := by decide
  have hdescent : baseEnd_6780135 < baseStart_6780135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780168 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_6780168 : Nat := 118140960795 + 6780168 * 2 ^ 59
def prefixEnd_6780168 : Nat := 4983230072969 + 3 ^ 40 * 6780168 * 2
def baseEnd_6780168 : Nat := 3481485102233533795218581

theorem tailTrace_6780168 : CollatzResearch.WordTrace tailWord_6780168 prefixEnd_6780168 3481485102233533795218581 := by
  unfold tailWord_6780168
  simp only [CollatzResearch.WordTrace]
  refine ⟨123646521450308385674782579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164862028600411180899710105 123646521450308385674782579)
  ·
    refine ⟨185469782175462578512173869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123646521450308385674782579 185469782175462578512173869)
    ·
      refine ⟨69551168315798466942065201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185469782175462578512173869 69551168315798466942065201)
      ·
        refine ⟨52163376236848850206548901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69551168315798466942065201 52163376236848850206548901)
        ·
          refine ⟨9780633044409159413727919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52163376236848850206548901 9780633044409159413727919)
          ·
            refine ⟨14670949566613739120591879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9780633044409159413727919 14670949566613739120591879)
            ·
              refine ⟨22006424349920608680887819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14670949566613739120591879 22006424349920608680887819)
              ·
                refine ⟨33009636524880913021331729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22006424349920608680887819 33009636524880913021331729)
                ·
                  refine ⟨24757227393660684765998797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33009636524880913021331729 24757227393660684765998797)
                  ·
                    refine ⟨9283960272622756787249549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24757227393660684765998797 9283960272622756787249549)
                    ·
                      refine ⟨3481485102233533795218581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9283960272622756787249549 3481485102233533795218581)
                      ·
                        rfl

theorem cell23_6780168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_6780168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780168 prefixEnd_6780168 := by exact prefixLift 6780168
  have htrace : WordTrace (prefixWord ++ tailWord_6780168) baseStart_6780168 baseEnd_6780168 := by
    simpa [prefixWord, tailWord_6780168, baseEnd_6780168] using wordTrace_append hprefix tailTrace_6780168
  have hstable : (prefixWord ++ tailWord_6780168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780168).length < 2 ^ (prefixWord ++ tailWord_6780168).sum := by decide
  have hdescent : baseEnd_6780168 < baseStart_6780168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780218 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 3, 4]
def baseStart_6780218 : Nat := 118140960795 + 6780218 * 2 ^ 59
def prefixEnd_6780218 : Nat := 4983230072969 + 3 ^ 40 * 6780218 * 2
def baseEnd_6780218 : Nat := 1160503592088752866531117

theorem tailTrace_6780218 : CollatzResearch.WordTrace tailWord_6780218 prefixEnd_6780218 1160503592088752866531117 := by
  unfold tailWord_6780218
  simp only [CollatzResearch.WordTrace]
  refine ⟨61823716637608907472221327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164863244366957086592590205 61823716637608907472221327)
  ·
    refine ⟨92735574956413361208331991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61823716637608907472221327 92735574956413361208331991)
    ·
      refine ⟨139103362434620041812497987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92735574956413361208331991 139103362434620041812497987)
      ·
        refine ⟨208655043651930062718746981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139103362434620041812497987 208655043651930062718746981)
        ·
          refine ⟨39122820684736886759765059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208655043651930062718746981 39122820684736886759765059)
          ·
            refine ⟨58684231027105330139647589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39122820684736886759765059 58684231027105330139647589)
            ·
              refine ⟨11003293317582249401183923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58684231027105330139647589 11003293317582249401183923)
              ·
                refine ⟨16504939976373374101775885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11003293317582249401183923 16504939976373374101775885)
                ·
                  refine ⟨6189352491140015288165957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16504939976373374101775885 6189352491140015288165957)
                  ·
                    refine ⟨1160503592088752866531117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6189352491140015288165957 1160503592088752866531117)
                    ·
                      rfl

theorem cell23_6780218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_6780218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780218 prefixEnd_6780218 := by exact prefixLift 6780218
  have htrace : WordTrace (prefixWord ++ tailWord_6780218) baseStart_6780218 baseEnd_6780218 := by
    simpa [prefixWord, tailWord_6780218, baseEnd_6780218] using wordTrace_append hprefix tailTrace_6780218
  have hstable : (prefixWord ++ tailWord_6780218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780218).length < 2 ^ (prefixWord ++ tailWord_6780218).sum := by decide
  have hdescent : baseEnd_6780218 < baseStart_6780218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780225 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6780225 : Nat := 118140960795 + 6780225 * 2 ^ 59
def prefixEnd_6780225 : Nat := 4983230072969 + 3 ^ 40 * 6780225 * 2
def baseEnd_6780225 : Nat := 3481514370630840072205819

theorem tailTrace_6780225 : CollatzResearch.WordTrace tailWord_6780225 prefixEnd_6780225 3481514370630840072205819 := by
  unfold tailWord_6780225
  simp only [CollatzResearch.WordTrace]
  refine ⟨247295121861410270084390129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164863414574273513389593419 247295121861410270084390129)
  ·
    refine ⟨185471341396057702563292597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247295121861410270084390129 185471341396057702563292597)
    ·
      refine ⟨17387938255880409615308681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185471341396057702563292597 17387938255880409615308681)
      ·
        refine ⟨13040953691910307211481511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17387938255880409615308681 13040953691910307211481511)
        ·
          refine ⟨19561430537865460817222267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13040953691910307211481511 19561430537865460817222267)
          ·
            refine ⟨29342145806798191225833401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19561430537865460817222267 29342145806798191225833401)
            ·
              refine ⟨22006609355098643419375051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29342145806798191225833401 22006609355098643419375051)
              ·
                refine ⟨33009914032647965129062577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22006609355098643419375051 33009914032647965129062577)
                ·
                  refine ⟨24757435524485973846796933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33009914032647965129062577 24757435524485973846796933)
                  ·
                    refine ⟨4642019160841120096274425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24757435524485973846796933 4642019160841120096274425)
                    ·
                      refine ⟨3481514370630840072205819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642019160841120096274425 3481514370630840072205819)
                      ·
                        rfl

theorem cell23_6780225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6780225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780225 prefixEnd_6780225 := by exact prefixLift 6780225
  have htrace : WordTrace (prefixWord ++ tailWord_6780225) baseStart_6780225 baseEnd_6780225 := by
    simpa [prefixWord, tailWord_6780225, baseEnd_6780225] using wordTrace_append hprefix tailTrace_6780225
  have hstable : (prefixWord ++ tailWord_6780225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780225).length < 2 ^ (prefixWord ++ tailWord_6780225).sum := by decide
  have hdescent : baseEnd_6780225 < baseStart_6780225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780241 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 2, 5, 3]
def baseStart_6780241 : Nat := 118140960795 + 6780241 * 2 ^ 59
def prefixEnd_6780241 : Nat := 4983230072969 + 3 ^ 40 * 6780241 * 2
def baseEnd_6780241 : Nat := 3481522586321312009605745

theorem tailTrace_6780241 : CollatzResearch.WordTrace tailWord_6780241 prefixEnd_6780241 3481522586321312009605745 := by
  unfold tailWord_6780241
  simp only [CollatzResearch.WordTrace]
  refine ⟨247295705429352304816972577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164863803619568203211315051 247295705429352304816972577)
  ·
    refine ⟨185471779072014228612729433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247295705429352304816972577 185471779072014228612729433)
    ·
      refine ⟨139103834304010671459547075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185471779072014228612729433 139103834304010671459547075)
      ·
        refine ⟨208655751456016007189320613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139103834304010671459547075 208655751456016007189320613)
        ·
          refine ⟨39122953398003001347997615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208655751456016007189320613 39122953398003001347997615)
          ·
            refine ⟨58684430097004502021996423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39122953398003001347997615 58684430097004502021996423)
            ·
              refine ⟨88026645145506753032994635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58684430097004502021996423 88026645145506753032994635)
              ·
                refine ⟨132039967718260129549491953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88026645145506753032994635 132039967718260129549491953)
                ·
                  refine ⟨99029975788695097162118965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132039967718260129549491953 99029975788695097162118965)
                  ·
                    refine ⟨9284060230190165358948653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99029975788695097162118965 9284060230190165358948653)
                    ·
                      refine ⟨3481522586321312009605745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9284060230190165358948653 3481522586321312009605745)
                      ·
                        rfl

theorem cell23_6780241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_6780241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780241 prefixEnd_6780241 := by exact prefixLift 6780241
  have htrace : WordTrace (prefixWord ++ tailWord_6780241) baseStart_6780241 baseEnd_6780241 := by
    simpa [prefixWord, tailWord_6780241, baseEnd_6780241] using wordTrace_append hprefix tailTrace_6780241
  have hstable : (prefixWord ++ tailWord_6780241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780241).length < 2 ^ (prefixWord ++ tailWord_6780241).sum := by decide
  have hdescent : baseEnd_6780241 < baseStart_6780241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780295 : List Nat := [1, 1, 4, 2, 2, 4, 1, 2, 1, 5]
def baseStart_6780295 : Nat := 118140960795 + 6780295 * 2 ^ 59
def prefixEnd_6780295 : Nat := 4983230072969 + 3 ^ 40 * 6780295 * 2
def baseEnd_6780295 : Nat := 1160516771425551599443499

theorem tailTrace_6780295 : CollatzResearch.WordTrace tailWord_6780295 prefixEnd_6780295 1160516771425551599443499 := by
  unfold tailWord_6780295
  simp only [CollatzResearch.WordTrace]
  refine ⟨247297674971156672039438339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164865116647437781359625559 247297674971156672039438339)
  ·
    refine ⟨370946512456735008059157509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247297674971156672039438339 370946512456735008059157509)
    ·
      refine ⟨69552471085637814011092033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370946512456735008059157509 69552471085637814011092033)
      ·
        refine ⟨52164353314228360508319025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69552471085637814011092033 52164353314228360508319025)
        ·
          refine ⟨39123264985671270381239269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52164353314228360508319025 39123264985671270381239269)
          ·
            refine ⟨7335612184813363196482363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39123264985671270381239269 7335612184813363196482363)
            ·
              refine ⟨11003418277220044794723545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7335612184813363196482363 11003418277220044794723545)
              ·
                refine ⟨8252563707915033596042659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11003418277220044794723545 8252563707915033596042659)
                ·
                  refine ⟨12378845561872550394063989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8252563707915033596042659 12378845561872550394063989)
                  ·
                    refine ⟨1160516771425551599443499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12378845561872550394063989 1160516771425551599443499)
                    ·
                      rfl

theorem cell23_6780295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_6780295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780295 prefixEnd_6780295 := by exact prefixLift 6780295
  have htrace : WordTrace (prefixWord ++ tailWord_6780295) baseStart_6780295 baseEnd_6780295 := by
    simpa [prefixWord, tailWord_6780295, baseEnd_6780295] using wordTrace_append hprefix tailTrace_6780295
  have hstable : (prefixWord ++ tailWord_6780295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780295).length < 2 ^ (prefixWord ++ tailWord_6780295).sum := by decide
  have hdescent : baseEnd_6780295 < baseStart_6780295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780308 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_6780308 : Nat := 118140960795 + 6780308 * 2 ^ 59
def prefixEnd_6780308 : Nat := 4983230072969 + 3 ^ 40 * 6780308 * 2
def baseEnd_6780308 : Nat := 1160518996508387749155979

theorem tailTrace_6780308 : CollatzResearch.WordTrace tailWord_6780308 prefixEnd_6780308 1160518996508387749155979 := by
  unfold tailWord_6780308
  simp only [CollatzResearch.WordTrace]
  refine ⟨123649074560054787629830789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164865432746739716839774385 123649074560054787629830789)
  ·
    refine ⟨23184201480010272680593273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123649074560054787629830789 23184201480010272680593273)
    ·
      refine ⟨17388151110007704510444955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23184201480010272680593273 17388151110007704510444955)
      ·
        refine ⟨26082226665011556765667433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17388151110007704510444955 26082226665011556765667433)
        ·
          refine ⟨19561669998758667574250575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26082226665011556765667433 19561669998758667574250575)
          ·
            refine ⟨29342504998138001361375863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19561669998758667574250575 29342504998138001361375863)
            ·
              refine ⟨44013757497207002042063795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29342504998138001361375863 44013757497207002042063795)
              ·
                refine ⟨66020636245810503063095693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44013757497207002042063795 66020636245810503063095693)
                ·
                  refine ⟨24757738592178938648660885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66020636245810503063095693 24757738592178938648660885)
                  ·
                    refine ⟨1160518996508387749155979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24757738592178938648660885 1160518996508387749155979)
                    ·
                      rfl

theorem cell23_6780308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_6780308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780308 prefixEnd_6780308 := by exact prefixLift 6780308
  have htrace : WordTrace (prefixWord ++ tailWord_6780308) baseStart_6780308 baseEnd_6780308 := by
    simpa [prefixWord, tailWord_6780308, baseEnd_6780308] using wordTrace_append hprefix tailTrace_6780308
  have hstable : (prefixWord ++ tailWord_6780308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780308).length < 2 ^ (prefixWord ++ tailWord_6780308).sum := by decide
  have hdescent : baseEnd_6780308 < baseStart_6780308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780312 : List Nat := [2, 1, 2, 5, 2, 1, 3, 1, 1, 5]
def baseStart_6780312 : Nat := 118140960795 + 6780312 * 2 ^ 59
def prefixEnd_6780312 : Nat := 4983230072969 + 3 ^ 40 * 6780312 * 2
def baseEnd_6780312 : Nat := 1160519681149260410605973

theorem tailTrace_6780312 : CollatzResearch.WordTrace tailWord_6780312 prefixEnd_6780312 1160519681149260410605973 := by
  unfold tailWord_6780312
  simp only [CollatzResearch.WordTrace]
  refine ⟨123649147506047541971403595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164865530008063389295204793 123649147506047541971403595)
  ·
    refine ⟨185473721259071312957105393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123649147506047541971403595 185473721259071312957105393)
    ·
      refine ⟨139105290944303484717829045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185473721259071312957105393 139105290944303484717829045)
      ·
        refine ⟨13041121026028451692296473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139105290944303484717829045 13041121026028451692296473)
        ·
          refine ⟨9780840769521338769222355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13041121026028451692296473 9780840769521338769222355)
          ·
            refine ⟨14671261154282008153833533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9780840769521338769222355 14671261154282008153833533)
            ·
              refine ⟨5501722932855753057687575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14671261154282008153833533 5501722932855753057687575)
              ·
                refine ⟨8252584399283629586531363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5501722932855753057687575 8252584399283629586531363)
                ·
                  refine ⟨12378876598925444379797045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8252584399283629586531363 12378876598925444379797045)
                  ·
                    refine ⟨1160519681149260410605973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12378876598925444379797045 1160519681149260410605973)
                    ·
                      rfl

theorem cell23_6780312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_6780312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780312 prefixEnd_6780312 := by exact prefixLift 6780312
  have htrace : WordTrace (prefixWord ++ tailWord_6780312) baseStart_6780312 baseEnd_6780312 := by
    simpa [prefixWord, tailWord_6780312, baseEnd_6780312] using wordTrace_append hprefix tailTrace_6780312
  have hstable : (prefixWord ++ tailWord_6780312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780312).length < 2 ^ (prefixWord ++ tailWord_6780312).sum := by decide
  have hdescent : baseEnd_6780312 < baseStart_6780312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780345 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 1, 2, 4]
def baseStart_6780345 : Nat := 118140960795 + 6780345 * 2 ^ 59
def prefixEnd_6780345 : Nat := 4983230072969 + 3 ^ 40 * 6780345 * 2
def baseEnd_6780345 : Nat := 3481575988309379602705267

theorem tailTrace_6780345 : CollatzResearch.WordTrace tailWord_6780345 prefixEnd_6780345 3481575988309379602705267 := by
  unfold tailWord_6780345
  simp only [CollatzResearch.WordTrace]
  refine ⟨247299498620975530578758489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164866332413983687052505659 247299498620975530578758489)
  ·
    refine ⟨185474623965731647934068867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247299498620975530578758489 185474623965731647934068867)
    ·
      refine ⟨278211935948597471901103301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185474623965731647934068867 278211935948597471901103301)
      ·
        refine ⟨52164737990362025981456869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278211935948597471901103301 52164737990362025981456869)
        ·
          refine ⟨9780888373192879871523163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52164737990362025981456869 9780888373192879871523163)
          ·
            refine ⟨14671332559789319807284745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9780888373192879871523163 14671332559789319807284745)
            ·
              refine ⟨11003499419841989855463559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14671332559789319807284745 11003499419841989855463559)
              ·
                refine ⟨16505249129762984783195339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11003499419841989855463559 16505249129762984783195339)
                ·
                  refine ⟨24757873694644477174793009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16505249129762984783195339 24757873694644477174793009)
                  ·
                    refine ⟨18568405270983357881094757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24757873694644477174793009 18568405270983357881094757)
                    ·
                      refine ⟨3481575988309379602705267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18568405270983357881094757 3481575988309379602705267)
                      ·
                        rfl

theorem cell23_6780345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_6780345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780345 prefixEnd_6780345 := by exact prefixLift 6780345
  have htrace : WordTrace (prefixWord ++ tailWord_6780345) baseStart_6780345 baseEnd_6780345 := by
    simpa [prefixWord, tailWord_6780345, baseEnd_6780345] using wordTrace_append hprefix tailTrace_6780345
  have hstable : (prefixWord ++ tailWord_6780345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780345).length < 2 ^ (prefixWord ++ tailWord_6780345).sum := by decide
  have hdescent : baseEnd_6780345 < baseStart_6780345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780361 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 5]
def baseStart_6780361 : Nat := 118140960795 + 6780361 * 2 ^ 59
def prefixEnd_6780361 : Nat := 4983230072969 + 3 ^ 40 * 6780361 * 2
def baseEnd_6780361 : Nat := 3481584203999851540105193

theorem tailTrace_6780361 : CollatzResearch.WordTrace tailWord_6780361 prefixEnd_6780361 3481584203999851540105193 := by
  unfold tailWord_6780361
  simp only [CollatzResearch.WordTrace]
  refine ⟨247300082188917565311340937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164866721459278376874227291 247300082188917565311340937)
  ·
    refine ⟨185475061641688173983505703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247300082188917565311340937 185475061641688173983505703)
    ·
      refine ⟨278212592462532260975258555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185475061641688173983505703 278212592462532260975258555)
      ·
        refine ⟨417318888693798391462887833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278212592462532260975258555 417318888693798391462887833)
        ·
          refine ⟨312989166520348793597165875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417318888693798391462887833 312989166520348793597165875)
          ·
            refine ⟨469483749780523190395748813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312989166520348793597165875 469483749780523190395748813)
            ·
              refine ⟨176056406167696196398405805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 469483749780523190395748813 176056406167696196398405805)
              ·
                refine ⟨66021152312886073649402177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176056406167696196398405805 66021152312886073649402177)
                ·
                  refine ⟨49515864234664555237051633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66021152312886073649402177 49515864234664555237051633)
                  ·
                    refine ⟨37136898175998416427788725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49515864234664555237051633 37136898175998416427788725)
                    ·
                      refine ⟨3481584203999851540105193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37136898175998416427788725 3481584203999851540105193)
                      ·
                        rfl

theorem cell23_6780361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_6780361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780361 prefixEnd_6780361 := by exact prefixLift 6780361
  have htrace : WordTrace (prefixWord ++ tailWord_6780361) baseStart_6780361 baseEnd_6780361 := by
    simpa [prefixWord, tailWord_6780361, baseEnd_6780361] using wordTrace_append hprefix tailTrace_6780361
  have hstable : (prefixWord ++ tailWord_6780361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780361).length < 2 ^ (prefixWord ++ tailWord_6780361).sum := by decide
  have hdescent : baseEnd_6780361 < baseStart_6780361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780398 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_6780398 : Nat := 118140960795 + 6780398 * 2 ^ 59
def prefixEnd_6780398 : Nat := 4983230072969 + 3 ^ 40 * 6780398 * 2
def baseEnd_6780398 : Nat := 1160534400928022631780841

theorem tailTrace_6780398 : CollatzResearch.WordTrace tailWord_6780398 prefixEnd_6780398 1160534400928022631780841 := by
  unfold tailWord_6780398
  simp only [CollatzResearch.WordTrace]
  refine ⟨30912678961222940078804731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164867621126522347086958565 30912678961222940078804731)
  ·
    refine ⟨46369018441834410118207097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30912678961222940078804731 46369018441834410118207097)
    ·
      refine ⟨34776763831375807588655323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46369018441834410118207097 34776763831375807588655323)
      ·
        refine ⟨52165145747063711382982985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34776763831375807588655323 52165145747063711382982985)
        ·
          refine ⟨39123859310297783537237239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52165145747063711382982985 39123859310297783537237239)
          ·
            refine ⟨58685788965446675305855859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39123859310297783537237239 58685788965446675305855859)
            ·
              refine ⟨88028683448170012958783789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58685788965446675305855859 88028683448170012958783789)
              ·
                refine ⟨33010756293063754859543921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88028683448170012958783789 33010756293063754859543921)
                ·
                  refine ⟨24758067219797816144657941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33010756293063754859543921 24758067219797816144657941)
                  ·
                    refine ⟨1160534400928022631780841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24758067219797816144657941 1160534400928022631780841)
                    ·
                      rfl

theorem cell23_6780398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_6780398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780398 prefixEnd_6780398 := by exact prefixLift 6780398
  have htrace : WordTrace (prefixWord ++ tailWord_6780398) baseStart_6780398 baseEnd_6780398 := by
    simpa [prefixWord, tailWord_6780398, baseEnd_6780398] using wordTrace_append hprefix tailTrace_6780398
  have hstable : (prefixWord ++ tailWord_6780398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780398).length < 2 ^ (prefixWord ++ tailWord_6780398).sum := by decide
  have hdescent : baseEnd_6780398 < baseStart_6780398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780431 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 8]
def baseStart_6780431 : Nat := 118140960795 + 6780431 * 2 ^ 59
def prefixEnd_6780431 : Nat := 4983230072969 + 3 ^ 40 * 6780431 * 2
def baseEnd_6780431 : Nat := 3481620147645666266229871

theorem tailTrace_6780431 : CollatzResearch.WordTrace tailWord_6780431 prefixEnd_6780431 3481620147645666266229871 := by
  unfold tailWord_6780431
  simp only [CollatzResearch.WordTrace]
  refine ⟨247302635298663967266389147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164868423532442644844259431 247302635298663967266389147)
  ·
    refine ⟨370953952947995950899583721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247302635298663967266389147 370953952947995950899583721)
    ·
      refine ⟨278215464710996963174687791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370953952947995950899583721 278215464710996963174687791)
      ·
        refine ⟨417323197066495444762031687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278215464710996963174687791 417323197066495444762031687)
        ·
          refine ⟨625984795599743167143047531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417323197066495444762031687 625984795599743167143047531)
          ·
            refine ⟨938977193399614750714571297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625984795599743167143047531 938977193399614750714571297)
            ·
              refine ⟨704232895049711063035928473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 938977193399614750714571297 704232895049711063035928473)
              ·
                refine ⟨528174671287283297276946355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704232895049711063035928473 528174671287283297276946355)
                ·
                  refine ⟨792262006930924945915419533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528174671287283297276946355 792262006930924945915419533)
                  ·
                    refine ⟨297098252599096854718282325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 792262006930924945915419533 297098252599096854718282325)
                    ·
                      refine ⟨3481620147645666266229871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 297098252599096854718282325 3481620147645666266229871)
                      ·
                        rfl

theorem cell23_6780431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_6780431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780431 prefixEnd_6780431 := by exact prefixLift 6780431
  have htrace : WordTrace (prefixWord ++ tailWord_6780431) baseStart_6780431 baseEnd_6780431 := by
    simpa [prefixWord, tailWord_6780431, baseEnd_6780431] using wordTrace_append hprefix tailTrace_6780431
  have hstable : (prefixWord ++ tailWord_6780431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780431).length < 2 ^ (prefixWord ++ tailWord_6780431).sum := by decide
  have hdescent : baseEnd_6780431 < baseStart_6780431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780456 : List Nat := [2, 1, 5, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_6780456 : Nat := 118140960795 + 6780456 * 2 ^ 59
def prefixEnd_6780456 : Nat := 4983230072969 + 3 ^ 40 * 6780456 * 2
def baseEnd_6780456 : Nat := 3481632984662028668417257

theorem tailTrace_6780456 : CollatzResearch.WordTrace tailWord_6780456 prefixEnd_6780456 3481632984662028668417257 := by
  unfold tailWord_6780456
  simp only [CollatzResearch.WordTrace]
  refine ⟨123651773561786698268024611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164869031415715597690699481 123651773561786698268024611)
  ·
    refine ⟨185477660342680047402036917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123651773561786698268024611 185477660342680047402036917)
    ·
      refine ⟨17388530657126254443940961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185477660342680047402036917 17388530657126254443940961)
      ·
        refine ⟨13041397992844690832955721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17388530657126254443940961 13041397992844690832955721)
        ·
          refine ⟨9781048494633518124716791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13041397992844690832955721 9781048494633518124716791)
          ·
            refine ⟨14671572741950277187075187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9781048494633518124716791 14671572741950277187075187)
            ·
              refine ⟨22007359112925415780612781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14671572741950277187075187 22007359112925415780612781)
              ·
                refine ⟨8252759667347030917729793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22007359112925415780612781 8252759667347030917729793)
                ·
                  refine ⟨6189569750510273188297345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8252759667347030917729793 6189569750510273188297345)
                  ·
                    refine ⟨4642177312882704891223009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6189569750510273188297345 4642177312882704891223009)
                    ·
                      refine ⟨3481632984662028668417257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642177312882704891223009 3481632984662028668417257)
                      ·
                        rfl

theorem cell23_6780456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_6780456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780456 prefixEnd_6780456 := by exact prefixLift 6780456
  have htrace : WordTrace (prefixWord ++ tailWord_6780456) baseStart_6780456 baseEnd_6780456 := by
    simpa [prefixWord, tailWord_6780456, baseEnd_6780456] using wordTrace_append hprefix tailTrace_6780456
  have hstable : (prefixWord ++ tailWord_6780456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780456).length < 2 ^ (prefixWord ++ tailWord_6780456).sum := by decide
  have hdescent : baseEnd_6780456 < baseStart_6780456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780495 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 2, 4, 2]
def baseStart_6780495 : Nat := 118140960795 + 6780495 * 2 ^ 59
def prefixEnd_6780495 : Nat := 4983230072969 + 3 ^ 40 * 6780495 * 2
def baseEnd_6780495 : Nat := 3481653010407554015829577

theorem tailTrace_6780495 : CollatzResearch.WordTrace tailWord_6780495 prefixEnd_6780495 3481653010407554015829577 := by
  unfold tailWord_6780495
  simp only [CollatzResearch.WordTrace]
  refine ⟨247304969570432106196718939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164869979713621404131145959 247304969570432106196718939)
  ·
    refine ⟨370957454355648159295078409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247304969570432106196718939 370957454355648159295078409)
    ·
      refine ⟨278218090766736119471308807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370957454355648159295078409 278218090766736119471308807)
      ·
        refine ⟨417327136150104179206963211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278218090766736119471308807 417327136150104179206963211)
        ·
          refine ⟨625990704225156268810444817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417327136150104179206963211 625990704225156268810444817)
          ·
            refine ⟨469493028168867201607833613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625990704225156268810444817 469493028168867201607833613)
            ·
              refine ⟨176059885563325200602937605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 469493028168867201607833613 176059885563325200602937605)
              ·
                refine ⟨33011228543123475113050801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176059885563325200602937605 33011228543123475113050801)
                ·
                  refine ⟨24758421407342606334788101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33011228543123475113050801 24758421407342606334788101)
                  ·
                    refine ⟨4642204013876738687772769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24758421407342606334788101 4642204013876738687772769)
                    ·
                      refine ⟨3481653010407554015829577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642204013876738687772769 3481653010407554015829577)
                      ·
                        rfl

theorem cell23_6780495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 4, 2].length) (baseStart_6780495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780495 prefixEnd_6780495 := by exact prefixLift 6780495
  have htrace : WordTrace (prefixWord ++ tailWord_6780495) baseStart_6780495 baseEnd_6780495 := by
    simpa [prefixWord, tailWord_6780495, baseEnd_6780495] using wordTrace_append hprefix tailTrace_6780495
  have hstable : (prefixWord ++ tailWord_6780495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780495).length < 2 ^ (prefixWord ++ tailWord_6780495).sum := by decide
  have hdescent : baseEnd_6780495 < baseStart_6780495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780522 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 3, 4]
def baseStart_6780522 : Nat := 118140960795 + 6780522 * 2 ^ 59
def prefixEnd_6780522 : Nat := 4983230072969 + 3 ^ 40 * 6780522 * 2
def baseEnd_6780522 : Nat := 1160555624795075136730651

theorem tailTrace_6780522 : CollatzResearch.WordTrace tailWord_6780522 prefixEnd_6780522 1160555624795075136730651 := by
  unfold tailWord_6780522
  simp only [CollatzResearch.WordTrace]
  refine ⟨61826488585333572451987955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164870636227556193205301213 61826488585333572451987955)
  ·
    refine ⟨92739732878000358677981933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61826488585333572451987955 92739732878000358677981933)
    ·
      refine ⟨34777399829250134504243225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92739732878000358677981933 34777399829250134504243225)
      ·
        refine ⟨26083049871937600878182419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34777399829250134504243225 26083049871937600878182419)
        ·
          refine ⟨39124574807906401317273629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26083049871937600878182419 39124574807906401317273629)
          ·
            refine ⟨14671715552964900493977611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39124574807906401317273629 14671715552964900493977611)
            ·
              refine ⟨22007573329447350740966417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14671715552964900493977611 22007573329447350740966417)
              ·
                refine ⟨16505679997085513055724813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22007573329447350740966417 16505679997085513055724813)
                ·
                  refine ⟨6189629998907067395896805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16505679997085513055724813 6189629998907067395896805)
                  ·
                    refine ⟨1160555624795075136730651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6189629998907067395896805 1160555624795075136730651)
                    ·
                      rfl

theorem cell23_6780522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_6780522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780522 prefixEnd_6780522 := by exact prefixLift 6780522
  have htrace : WordTrace (prefixWord ++ tailWord_6780522) baseStart_6780522 baseEnd_6780522 := by
    simpa [prefixWord, tailWord_6780522, baseEnd_6780522] using wordTrace_append hprefix tailTrace_6780522
  have hstable : (prefixWord ++ tailWord_6780522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780522).length < 2 ^ (prefixWord ++ tailWord_6780522).sum := by decide
  have hdescent : baseEnd_6780522 < baseStart_6780522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780552 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 8]
def baseStart_6780552 : Nat := 118140960795 + 6780552 * 2 ^ 59
def prefixEnd_6780552 : Nat := 4983230072969 + 3 ^ 40 * 6780552 * 2
def baseEnd_6780552 : Nat := 386853586533873365868535

theorem tailTrace_6780552 : CollatzResearch.WordTrace tailWord_6780552 prefixEnd_6780552 386853586533873365868535 := by
  unfold tailWord_6780552
  simp only [CollatzResearch.WordTrace]
  refine ⟨123653524265612802465771955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164871365687483736621029273 123653524265612802465771955)
  ·
    refine ⟨185480286398419203698657933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123653524265612802465771955 185480286398419203698657933)
    ·
      refine ⟨69555107399407201386996725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185480286398419203698657933 69555107399407201386996725)
      ·
        refine ⟨6520791318694425130030943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69555107399407201386996725 6520791318694425130030943)
        ·
          refine ⟨9781186978041637695046415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6520791318694425130030943 9781186978041637695046415)
          ·
            refine ⟨14671780467062456542569623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9781186978041637695046415 14671780467062456542569623)
            ·
              refine ⟨22007670700593684813854435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14671780467062456542569623 22007670700593684813854435)
              ·
                refine ⟨33011506050890527220781653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22007670700593684813854435 33011506050890527220781653)
                ·
                  refine ⟨386853586533873365868535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33011506050890527220781653 386853586533873365868535)
                  ·
                    rfl

theorem cell23_6780552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 8].length) (baseStart_6780552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780552 prefixEnd_6780552 := by exact prefixLift 6780552
  have htrace : WordTrace (prefixWord ++ tailWord_6780552) baseStart_6780552 baseEnd_6780552 := by
    simpa [prefixWord, tailWord_6780552, baseEnd_6780552] using wordTrace_append hprefix tailTrace_6780552
  have hstable : (prefixWord ++ tailWord_6780552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780552).length < 2 ^ (prefixWord ++ tailWord_6780552).sum := by decide
  have hdescent : baseEnd_6780552 < baseStart_6780552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780589 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_6780589 : Nat := 118140960795 + 6780589 * 2 ^ 59
def prefixEnd_6780589 : Nat := 4983230072969 + 3 ^ 40 * 6780589 * 2
def baseEnd_6780589 : Nat := 3481701277589076648054145

theorem tailTrace_6780589 : CollatzResearch.WordTrace tailWord_6780589 prefixEnd_6780589 3481701277589076648054145 := by
  unfold tailWord_6780589
  simp only [CollatzResearch.WordTrace]
  refine ⟨247308398032091560250640821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164872265354727706833760547 247308398032091560250640821)
  ·
    refine ⟨23185162315508583773497577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247308398032091560250640821 23185162315508583773497577)
    ·
      refine ⟨17388871736631437830123183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23185162315508583773497577 17388871736631437830123183)
      ·
        refine ⟨26083307604947156745184775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17388871736631437830123183 26083307604947156745184775)
        ·
          refine ⟨39124961407420735117777163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26083307604947156745184775 39124961407420735117777163)
          ·
            refine ⟨58687442111131102676665745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39124961407420735117777163 58687442111131102676665745)
            ·
              refine ⟨44015581583348327007499309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58687442111131102676665745 44015581583348327007499309)
              ·
                refine ⟨16505843093755622627812241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44015581583348327007499309 16505843093755622627812241)
                ·
                  refine ⟨12379382320316716970859181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16505843093755622627812241 12379382320316716970859181)
                  ·
                    refine ⟨4642268370118768864072193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12379382320316716970859181 4642268370118768864072193)
                    ·
                      refine ⟨3481701277589076648054145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642268370118768864072193 3481701277589076648054145)
                      ·
                        rfl

theorem cell23_6780589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_6780589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780589 prefixEnd_6780589 := by exact prefixLift 6780589
  have htrace : WordTrace (prefixWord ++ tailWord_6780589) baseStart_6780589 baseEnd_6780589 := by
    simpa [prefixWord, tailWord_6780589, baseEnd_6780589] using wordTrace_append hprefix tailTrace_6780589
  have hstable : (prefixWord ++ tailWord_6780589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780589).length < 2 ^ (prefixWord ++ tailWord_6780589).sum := by decide
  have hdescent : baseEnd_6780589 < baseStart_6780589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780590 : List Nat := [4, 1, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_6780590 : Nat := 118140960795 + 6780590 * 2 ^ 59
def prefixEnd_6780590 : Nat := 4983230072969 + 3 ^ 40 * 6780590 * 2
def baseEnd_6780590 : Nat := 1160567263689910381380547

theorem tailTrace_6780590 : CollatzResearch.WordTrace tailWord_6780590 prefixEnd_6780590 1160567263689910381380547 := by
  unfold tailWord_6780590
  simp only [CollatzResearch.WordTrace]
  refine ⟨30913554313135992177678403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164872289670058624947618149 30913554313135992177678403)
  ·
    refine ⟨46370331469703988266517605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30913554313135992177678403 46370331469703988266517605)
    ·
      refine ⟨8694437150569497799972051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46370331469703988266517605 8694437150569497799972051)
      ·
        refine ⟨13041655725854246699958077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8694437150569497799972051 13041655725854246699958077)
        ·
          refine ⟨4890620897195342512484279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13041655725854246699958077 4890620897195342512484279)
          ·
            refine ⟨7335931345793013768726419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4890620897195342512484279 7335931345793013768726419)
            ·
              refine ⟨11003897018689520653089629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7335931345793013768726419 11003897018689520653089629)
              ·
                refine ⟨4126461382008570244908611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11003897018689520653089629 4126461382008570244908611)
                ·
                  refine ⟨6189692073012855367362917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4126461382008570244908611 6189692073012855367362917)
                  ·
                    refine ⟨1160567263689910381380547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6189692073012855367362917 1160567263689910381380547)
                    ·
                      rfl

theorem cell23_6780590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_6780590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780590 prefixEnd_6780590 := by exact prefixLift 6780590
  have htrace : WordTrace (prefixWord ++ tailWord_6780590) baseStart_6780590 baseEnd_6780590 := by
    simpa [prefixWord, tailWord_6780590, baseEnd_6780590] using wordTrace_append hprefix tailTrace_6780590
  have hstable : (prefixWord ++ tailWord_6780590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780590).length < 2 ^ (prefixWord ++ tailWord_6780590).sum := by decide
  have hdescent : baseEnd_6780590 < baseStart_6780590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780595 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 6, 4]
def baseStart_6780595 : Nat := 118140960795 + 6780595 * 2 ^ 59
def prefixEnd_6780595 : Nat := 4983230072969 + 3 ^ 40 * 6780595 * 2
def baseEnd_6780595 : Nat := 1160568119491001208193039

theorem tailTrace_6780595 : CollatzResearch.WordTrace tailWord_6780595 prefixEnd_6780595 1160568119491001208193039 := by
  unfold tailWord_6780595
  simp only [CollatzResearch.WordTrace]
  refine ⟨247308616870069823275359239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164872411246713215516906159 247308616870069823275359239)
  ·
    refine ⟨370962925305104734913038859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247308616870069823275359239 370962925305104734913038859)
    ·
      refine ⟨556444387957657102369558289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370962925305104734913038859 556444387957657102369558289)
      ·
        refine ⟨417333290968242826777168717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556444387957657102369558289 417333290968242826777168717)
        ·
          refine ⟨156499984113091060041438269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 417333290968242826777168717 156499984113091060041438269)
          ·
            refine ⟨58687494042409147515539351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156499984113091060041438269 58687494042409147515539351)
            ·
              refine ⟨88031241063613721273309027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58687494042409147515539351 88031241063613721273309027)
              ·
                refine ⟨132046861595420581909963541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88031241063613721273309027 132046861595420581909963541)
                ·
                  refine ⟨6189696637285339777029541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132046861595420581909963541 6189696637285339777029541)
                  ·
                    refine ⟨1160568119491001208193039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6189696637285339777029541 1160568119491001208193039)
                    ·
                      rfl

theorem cell23_6780595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 4].length) (baseStart_6780595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780595 prefixEnd_6780595 := by exact prefixLift 6780595
  have htrace : WordTrace (prefixWord ++ tailWord_6780595) baseStart_6780595 baseEnd_6780595 := by
    simpa [prefixWord, tailWord_6780595, baseEnd_6780595] using wordTrace_append hprefix tailTrace_6780595
  have hstable : (prefixWord ++ tailWord_6780595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780595).length < 2 ^ (prefixWord ++ tailWord_6780595).sum := by decide
  have hdescent : baseEnd_6780595 < baseStart_6780595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780602 : List Nat := [3, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4]
def baseStart_6780602 : Nat := 118140960795 + 6780602 * 2 ^ 59
def prefixEnd_6780602 : Nat := 4983230072969 + 3 ^ 40 * 6780602 * 2
def baseEnd_6780602 : Nat := 3481707952837585097191585

theorem tailTrace_6780602 : CollatzResearch.WordTrace tailWord_6780602 prefixEnd_6780602 3481707952837585097191585 := by
  unfold tailWord_6780602
  simp only [CollatzResearch.WordTrace]
  refine ⟨61827218045261115867716015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164872581454029642313909373 61827218045261115867716015)
  ·
    refine ⟨92740827067891673801574023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61827218045261115867716015 92740827067891673801574023)
    ·
      refine ⟨139111240601837510702361035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92740827067891673801574023 139111240601837510702361035)
      ·
        refine ⟨208666860902756266053541553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139111240601837510702361035 208666860902756266053541553)
        ·
          refine ⟨156500145677067199540156165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208666860902756266053541553 156500145677067199540156165)
          ·
            refine ⟨29343777314450099913779281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156500145677067199540156165 29343777314450099913779281)
            ·
              refine ⟨22007832985837574935334461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29343777314450099913779281 22007832985837574935334461)
              ·
                refine ⟨8252937369689090600750423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22007832985837574935334461 8252937369689090600750423)
                ·
                  refine ⟨12379406054533635901125635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8252937369689090600750423 12379406054533635901125635)
                  ·
                    refine ⟨18569109081800453851688453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12379406054533635901125635 18569109081800453851688453)
                    ·
                      refine ⟨3481707952837585097191585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18569109081800453851688453 3481707952837585097191585)
                      ·
                        rfl

theorem cell23_6780602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_6780602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780602 prefixEnd_6780602 := by exact prefixLift 6780602
  have htrace : WordTrace (prefixWord ++ tailWord_6780602) baseStart_6780602 baseEnd_6780602 := by
    simpa [prefixWord, tailWord_6780602, baseEnd_6780602] using wordTrace_append hprefix tailTrace_6780602
  have hstable : (prefixWord ++ tailWord_6780602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780602).length < 2 ^ (prefixWord ++ tailWord_6780602).sum := by decide
  have hdescent : baseEnd_6780602 < baseStart_6780602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780612 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_6780612 : Nat := 118140960795 + 6780612 * 2 ^ 59
def prefixEnd_6780612 : Nat := 4983230072969 + 3 ^ 40 * 6780612 * 2
def baseEnd_6780612 : Nat := 1160571029214710019355513

theorem tailTrace_6780612 : CollatzResearch.WordTrace tailWord_6780612 prefixEnd_6780612 1160571029214710019355513 := by
  unfold tailWord_6780612
  simp only [CollatzResearch.WordTrace]
  refine ⟨123654618455504117589364045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164872824607338823452485393 123654618455504117589364045)
  ·
    refine ⟨46370481920814044096011517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123654618455504117589364045 46370481920814044096011517)
    ·
      refine ⟨17388930720305266536004319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46370481920814044096011517 17388930720305266536004319)
      ·
        refine ⟨26083396080457899804006479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17388930720305266536004319 26083396080457899804006479)
        ·
          refine ⟨39125094120686849706009719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26083396080457899804006479 39125094120686849706009719)
          ·
            refine ⟨58687641181030274559014579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39125094120686849706009719 58687641181030274559014579)
            ·
              refine ⟨88031461771545411838521869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58687641181030274559014579 88031461771545411838521869)
              ·
                refine ⟨33011798164329529439445701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88031461771545411838521869 33011798164329529439445701)
                ·
                  refine ⟨6189712155811786769896069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33011798164329529439445701 6189712155811786769896069)
                  ·
                    refine ⟨1160571029214710019355513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6189712155811786769896069 1160571029214710019355513)
                    ·
                      rfl

theorem cell23_6780612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_6780612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780612 prefixEnd_6780612 := by exact prefixLift 6780612
  have htrace : WordTrace (prefixWord ++ tailWord_6780612) baseStart_6780612 baseEnd_6780612 := by
    simpa [prefixWord, tailWord_6780612, baseEnd_6780612] using wordTrace_append hprefix tailTrace_6780612
  have hstable : (prefixWord ++ tailWord_6780612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780612).length < 2 ^ (prefixWord ++ tailWord_6780612).sum := by decide
  have hdescent : baseEnd_6780612 < baseStart_6780612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780622 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_6780622 : Nat := 118140960795 + 6780622 * 2 ^ 59
def prefixEnd_6780622 : Nat := 4983230072969 + 3 ^ 40 * 6780622 * 2
def baseEnd_6780622 : Nat := 3481718222450675018941493

theorem tailTrace_6780622 : CollatzResearch.WordTrace tailWord_6780622 prefixEnd_6780622 3481718222450675018941493 := by
  unfold tailWord_6780622
  simp only [CollatzResearch.WordTrace]
  refine ⟨30913700205121500860824015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164873067760648004591061413 30913700205121500860824015)
  ·
    refine ⟨46370550307682251291236023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30913700205121500860824015 46370550307682251291236023)
    ·
      refine ⟨69555825461523376936854035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46370550307682251291236023 69555825461523376936854035)
      ·
        refine ⟨104333738192285065405281053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69555825461523376936854035 104333738192285065405281053)
        ·
          refine ⟨39125151822106899526980395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104333738192285065405281053 39125151822106899526980395)
          ·
            refine ⟨58687727733160349290470593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39125151822106899526980395 58687727733160349290470593)
            ·
              refine ⟨44015795799870261967852945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58687727733160349290470593 44015795799870261967852945)
              ·
                refine ⟨33011846849902696475889709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44015795799870261967852945 33011846849902696475889709)
                ·
                  refine ⟨12379442568713511178458641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33011846849902696475889709 12379442568713511178458641)
                  ·
                    refine ⟨9284581926535133383843981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12379442568713511178458641 9284581926535133383843981)
                    ·
                      refine ⟨3481718222450675018941493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9284581926535133383843981 3481718222450675018941493)
                      ·
                        rfl

theorem cell23_6780622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_6780622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780622 prefixEnd_6780622 := by exact prefixLift 6780622
  have htrace : WordTrace (prefixWord ++ tailWord_6780622) baseStart_6780622 baseEnd_6780622 := by
    simpa [prefixWord, tailWord_6780622, baseEnd_6780622] using wordTrace_append hprefix tailTrace_6780622
  have hstable : (prefixWord ++ tailWord_6780622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780622).length < 2 ^ (prefixWord ++ tailWord_6780622).sum := by decide
  have hdescent : baseEnd_6780622 < baseStart_6780622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780625 : List Nat := [1, 2, 2, 1, 2, 5, 2, 8]
def baseStart_6780625 : Nat := 118140960795 + 6780625 * 2 ^ 59
def prefixEnd_6780625 : Nat := 4983230072969 + 3 ^ 40 * 6780625 * 2
def baseEnd_6780625 : Nat := 128952583810838463229777

theorem tailTrace_6780625 : CollatzResearch.WordTrace tailWord_6780625 prefixEnd_6780625 128952583810838463229777 := by
  unfold tailWord_6780625
  simp only [CollatzResearch.WordTrace]
  refine ⟨247309711059961138398951329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164873140706640758932634219 247309711059961138398951329)
  ·
    refine ⟨185482283294970853799213497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247309711059961138398951329 185482283294970853799213497)
    ·
      refine ⟨139111712471228140349410123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185482283294970853799213497 139111712471228140349410123)
      ·
        refine ⟨208667568706842210524115185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139111712471228140349410123 208667568706842210524115185)
        ·
          refine ⟨156500676530131657893086389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208667568706842210524115185 156500676530131657893086389)
          ·
            refine ⟨14671938424699842927476849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156500676530131657893086389 14671938424699842927476849)
            ·
              refine ⟨11003953818524882195607637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14671938424699842927476849 11003953818524882195607637)
              ·
                refine ⟨128952583810838463229777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11003953818524882195607637 128952583810838463229777)
                ·
                  rfl

theorem cell23_6780625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 8].length) (baseStart_6780625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780625 prefixEnd_6780625 := by exact prefixLift 6780625
  have htrace : WordTrace (prefixWord ++ tailWord_6780625) baseStart_6780625 baseEnd_6780625 := by
    simpa [prefixWord, tailWord_6780625, baseEnd_6780625] using wordTrace_append hprefix tailTrace_6780625
  have hstable : (prefixWord ++ tailWord_6780625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780625).length < 2 ^ (prefixWord ++ tailWord_6780625).sum := by decide
  have hdescent : baseEnd_6780625 < baseStart_6780625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780652 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 3]
def baseStart_6780652 : Nat := 118140960795 + 6780652 * 2 ^ 59
def prefixEnd_6780652 : Nat := 4983230072969 + 3 ^ 40 * 6780652 * 2
def baseEnd_6780652 : Nat := 3481733626870309901566355

theorem tailTrace_6780652 : CollatzResearch.WordTrace tailWord_6780652 prefixEnd_6780652 3481733626870309901566355 := by
  unfold tailWord_6780652
  simp only [CollatzResearch.WordTrace]
  refine ⟨123655347915431661005092105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164873797220575548006789473 123655347915431661005092105)
  ·
    refine ⟨92741510936573745753819079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123655347915431661005092105 92741510936573745753819079)
    ·
      refine ⟨139112266404860618630728619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92741510936573745753819079 139112266404860618630728619)
      ·
        refine ⟨208668399607290927946092929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139112266404860618630728619 208668399607290927946092929)
        ·
          refine ⟨156501299705468195959569697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208668399607290927946092929 156501299705468195959569697)
          ·
            refine ⟨117375974779101146969677273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156501299705468195959569697 117375974779101146969677273)
            ·
              refine ⟨88031981084325860227257955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117375974779101146969677273 88031981084325860227257955)
              ·
                refine ⟨132047971626488790340886933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88031981084325860227257955 132047971626488790340886933)
                ·
                  refine ⟨6189748669991662047229075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132047971626488790340886933 6189748669991662047229075)
                  ·
                    refine ⟨9284623004987493070843613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6189748669991662047229075 9284623004987493070843613)
                    ·
                      refine ⟨3481733626870309901566355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9284623004987493070843613 3481733626870309901566355)
                      ·
                        rfl

theorem cell23_6780652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_6780652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780652 prefixEnd_6780652 := by exact prefixLift 6780652
  have htrace : WordTrace (prefixWord ++ tailWord_6780652) baseStart_6780652 baseEnd_6780652 := by
    simpa [prefixWord, tailWord_6780652, baseEnd_6780652] using wordTrace_append hprefix tailTrace_6780652
  have hstable : (prefixWord ++ tailWord_6780652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780652).length < 2 ^ (prefixWord ++ tailWord_6780652).sum := by decide
  have hdescent : baseEnd_6780652 < baseStart_6780652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780670 : List Nat := [4, 2, 2, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_6780670 : Nat := 118140960795 + 6780670 * 2 ^ 59
def prefixEnd_6780670 : Nat := 4983230072969 + 3 ^ 40 * 6780670 * 2
def baseEnd_6780670 : Nat := 3481742869522090831141273

theorem tailTrace_6780670 : CollatzResearch.WordTrace tailWord_6780670 prefixEnd_6780670 3481742869522090831141273 := by
  unfold tailWord_6780670
  simp only [CollatzResearch.WordTrace]
  refine ⟨30913919043099763885542433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164874234896532074056226309 30913919043099763885542433)
  ·
    refine ⟨23185439282324822914156825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30913919043099763885542433 23185439282324822914156825)
    ·
      refine ⟨17389079461743617185617619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23185439282324822914156825 17389079461743617185617619)
      ·
        refine ⟨26083619192615425778426429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17389079461743617185617619 26083619192615425778426429)
        ·
          refine ⟨9781357197230784666909911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26083619192615425778426429 9781357197230784666909911)
          ·
            refine ⟨14672035795846177000364867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9781357197230784666909911 14672035795846177000364867)
            ·
              refine ⟨22008053693769265500547301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14672035795846177000364867 22008053693769265500547301)
              ·
                refine ⟨4126510067581737281352619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22008053693769265500547301 4126510067581737281352619)
                ·
                  refine ⟨6189765101372605922028929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4126510067581737281352619 6189765101372605922028929)
                  ·
                    refine ⟨4642323826029454441521697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6189765101372605922028929 4642323826029454441521697)
                    ·
                      refine ⟨3481742869522090831141273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642323826029454441521697 3481742869522090831141273)
                      ·
                        rfl

theorem cell23_6780670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_6780670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780670 prefixEnd_6780670 := by exact prefixLift 6780670
  have htrace : WordTrace (prefixWord ++ tailWord_6780670) baseStart_6780670 baseEnd_6780670 := by
    simpa [prefixWord, tailWord_6780670, baseEnd_6780670] using wordTrace_append hprefix tailTrace_6780670
  have hstable : (prefixWord ++ tailWord_6780670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780670).length < 2 ^ (prefixWord ++ tailWord_6780670).sum := by decide
  have hdescent : baseEnd_6780670 < baseStart_6780670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780675 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 4]
def baseStart_6780675 : Nat := 118140960795 + 6780675 * 2 ^ 59
def prefixEnd_6780675 : Nat := 4983230072969 + 3 ^ 40 * 6780675 * 2
def baseEnd_6780675 : Nat := 3481745436925363311578749

theorem tailTrace_6780675 : CollatzResearch.WordTrace tailWord_6780675 prefixEnd_6780675 3481745436925363311578749 := by
  unfold tailWord_6780675
  simp only [CollatzResearch.WordTrace]
  refine ⟨247311534709779996938271479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164874356473186664625514319 247311534709779996938271479)
  ·
    refine ⟨370967302064669995407407219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247311534709779996938271479 370967302064669995407407219)
    ·
      refine ⟨556450953097004993111110829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370967302064669995407407219 556450953097004993111110829)
      ·
        refine ⟨208669107411376872416666561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 556450953097004993111110829 208669107411376872416666561)
        ·
          refine ⟨156501830558532654312499921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208669107411376872416666561 156501830558532654312499921)
          ·
            refine ⟨117376372918899490734374941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156501830558532654312499921 117376372918899490734374941)
            ·
              refine ⟨44016139844587309025390603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117376372918899490734374941 44016139844587309025390603)
              ·
                refine ⟨66024209766880963538085905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44016139844587309025390603 66024209766880963538085905)
                ·
                  refine ⟨49518157325160722653564429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66024209766880963538085905 49518157325160722653564429)
                  ·
                    refine ⟨18569308996935270995086661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49518157325160722653564429 18569308996935270995086661)
                    ·
                      refine ⟨3481745436925363311578749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18569308996935270995086661 3481745436925363311578749)
                      ·
                        rfl

theorem cell23_6780675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_6780675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780675 prefixEnd_6780675 := by exact prefixLift 6780675
  have htrace : WordTrace (prefixWord ++ tailWord_6780675) baseStart_6780675 baseEnd_6780675 := by
    simpa [prefixWord, tailWord_6780675, baseEnd_6780675] using wordTrace_append hprefix tailTrace_6780675
  have hstable : (prefixWord ++ tailWord_6780675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780675).length < 2 ^ (prefixWord ++ tailWord_6780675).sum := by decide
  have hdescent : baseEnd_6780675 < baseStart_6780675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780709 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 1, 4, 2]
def baseStart_6780709 : Nat := 118140960795 + 6780709 * 2 ^ 59
def prefixEnd_6780709 : Nat := 4983230072969 + 3 ^ 40 * 6780709 * 2
def baseEnd_6780709 : Nat := 3481762895267616178553593

theorem tailTrace_6780709 : CollatzResearch.WordTrace tailWord_6780709 prefixEnd_6780709 3481762895267616178553593 := by
  unfold tailWord_6780709
  simp only [CollatzResearch.WordTrace]
  refine ⟨247312774791656820745009181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164875183194437880496672787 247312774791656820745009181)
  ·
    refine ⟨92742290546871307779378443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247312774791656820745009181 92742290546871307779378443)
    ·
      refine ⟨139113435820306961669067665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92742290546871307779378443 139113435820306961669067665)
      ·
        refine ⟨104335076865230221251800749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139113435820306961669067665 104335076865230221251800749)
        ·
          refine ⟨39125653824461332969425281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104335076865230221251800749 39125653824461332969425281)
          ·
            refine ⟨29344240368345999727068961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39125653824461332969425281 29344240368345999727068961)
            ·
              refine ⟨22008180276259499795301721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29344240368345999727068961 22008180276259499795301721)
              ·
                refine ⟨16506135207194624846476291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22008180276259499795301721 16506135207194624846476291)
                ·
                  refine ⟨24759202810791937269714437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16506135207194624846476291 24759202810791937269714437)
                  ·
                    refine ⟨4642350527023488238071457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24759202810791937269714437 4642350527023488238071457)
                    ·
                      refine ⟨3481762895267616178553593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642350527023488238071457 3481762895267616178553593)
                      ·
                        rfl

theorem cell23_6780709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_6780709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780709 prefixEnd_6780709 := by exact prefixLift 6780709
  have htrace : WordTrace (prefixWord ++ tailWord_6780709) baseStart_6780709 baseEnd_6780709 := by
    simpa [prefixWord, tailWord_6780709, baseEnd_6780709] using wordTrace_append hprefix tailTrace_6780709
  have hstable : (prefixWord ++ tailWord_6780709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780709).length < 2 ^ (prefixWord ++ tailWord_6780709).sum := by decide
  have hdescent : baseEnd_6780709 < baseStart_6780709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780722 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_6780722 : Nat := 118140960795 + 6780722 * 2 ^ 59
def prefixEnd_6780722 : Nat := 4983230072969 + 3 ^ 40 * 6780722 * 2
def baseEnd_6780722 : Nat := 3481769570516124627691033

theorem tailTrace_6780722 : CollatzResearch.WordTrace tailWord_6780722 prefixEnd_6780722 3481769570516124627691033 := by
  unfold tailWord_6780722
  simp only [CollatzResearch.WordTrace]
  refine ⟨61828312235152430991308105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164875499293739815976821613 61828312235152430991308105)
  ·
    refine ⟨46371234176364323243481079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61828312235152430991308105 46371234176364323243481079)
    ·
      refine ⟨69556851264546484865221619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46371234176364323243481079 69556851264546484865221619)
      ·
        refine ⟨104335276896819727297832429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69556851264546484865221619 104335276896819727297832429)
        ·
          refine ⟨39125728836307397736687161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104335276896819727297832429 39125728836307397736687161)
          ·
            refine ⟨29344296627230548302515371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39125728836307397736687161 29344296627230548302515371)
            ·
              refine ⟨44016444940845822453773057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29344296627230548302515371 44016444940845822453773057)
              ·
                refine ⟨33012333705634366840329793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44016444940845822453773057 33012333705634366840329793)
                ·
                  refine ⟨24759250279225775130247345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33012333705634366840329793 24759250279225775130247345)
                  ·
                    refine ⟨18569437709419331347685509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24759250279225775130247345 18569437709419331347685509)
                    ·
                      refine ⟨3481769570516124627691033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18569437709419331347685509 3481769570516124627691033)
                      ·
                        rfl

theorem cell23_6780722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_6780722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780722 prefixEnd_6780722 := by exact prefixLift 6780722
  have htrace : WordTrace (prefixWord ++ tailWord_6780722) baseStart_6780722 baseEnd_6780722 := by
    simpa [prefixWord, tailWord_6780722, baseEnd_6780722] using wordTrace_append hprefix tailTrace_6780722
  have hstable : (prefixWord ++ tailWord_6780722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780722).length < 2 ^ (prefixWord ++ tailWord_6780722).sum := by decide
  have hdescent : baseEnd_6780722 < baseStart_6780722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780745 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 3, 7]
def baseStart_6780745 : Nat := 118140960795 + 6780745 * 2 ^ 59
def prefixEnd_6780745 : Nat := 4983230072969 + 3 ^ 40 * 6780745 * 2
def baseEnd_6780745 : Nat := 1160593793523726012567809

theorem tailTrace_6780745 : CollatzResearch.WordTrace tailWord_6780745 prefixEnd_6780745 1160593793523726012567809 := by
  unfold tailWord_6780745
  simp only [CollatzResearch.WordTrace]
  refine ⟨247314087819526398893319689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164876058546350932595546459 247314087819526398893319689)
  ·
    refine ⟨185485565864644799169989767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247314087819526398893319689 185485565864644799169989767)
    ·
      refine ⟨278228348796967198754984651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185485565864644799169989767 278228348796967198754984651)
      ·
        refine ⟨417342523195450798132476977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278228348796967198754984651 417342523195450798132476977)
        ·
          refine ⟨313006892396588098599357733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417342523195450798132476977 313006892396588098599357733)
          ·
            refine ⟨58688792324360268487379575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313006892396588098599357733 58688792324360268487379575)
            ·
              refine ⟨88033188486540402731069363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58688792324360268487379575 88033188486540402731069363)
              ·
                refine ⟨132049782729810604096604045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88033188486540402731069363 132049782729810604096604045)
                ·
                  refine ⟨49518668523678976536226517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132049782729810604096604045 49518668523678976536226517)
                  ·
                    refine ⟨1160593793523726012567809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49518668523678976536226517 1160593793523726012567809)
                    ·
                      rfl

theorem cell23_6780745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_6780745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780745 prefixEnd_6780745 := by exact prefixLift 6780745
  have htrace : WordTrace (prefixWord ++ tailWord_6780745) baseStart_6780745 baseEnd_6780745 := by
    simpa [prefixWord, tailWord_6780745, baseEnd_6780745] using wordTrace_append hprefix tailTrace_6780745
  have hstable : (prefixWord ++ tailWord_6780745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780745).length < 2 ^ (prefixWord ++ tailWord_6780745).sum := by decide
  have hdescent : baseEnd_6780745 < baseStart_6780745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780749 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 7]
def baseStart_6780749 : Nat := 118140960795 + 6780749 * 2 ^ 59
def prefixEnd_6780749 : Nat := 4983230072969 + 3 ^ 40 * 6780749 * 2
def baseEnd_6780749 : Nat := 386864826054866224672601

theorem tailTrace_6780749 : CollatzResearch.WordTrace tailWord_6780749 prefixEnd_6780749 386864826054866224672601 := by
  unfold tailWord_6780749
  simp only [CollatzResearch.WordTrace]
  refine ⟨247314233711511907576465301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164876155807674605050976867 247314233711511907576465301)
  ·
    refine ⟨11592854705227120667646811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 247314233711511907576465301 11592854705227120667646811)
    ·
      refine ⟨17389282057840681001470217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11592854705227120667646811 17389282057840681001470217)
      ·
        refine ⟨13041961543380510751102663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17389282057840681001470217 13041961543380510751102663)
        ·
          refine ⟨19562942315070766126653995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13041961543380510751102663 19562942315070766126653995)
          ·
            refine ⟨29344413472606149189980993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19562942315070766126653995 29344413472606149189980993)
            ·
              refine ⟨22008310104454611892485745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29344413472606149189980993 22008310104454611892485745)
              ·
                refine ⟨16506232578340958919364309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22008310104454611892485745 16506232578340958919364309)
                ·
                  refine ⟨386864826054866224672601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16506232578340958919364309 386864826054866224672601)
                  ·
                    rfl

theorem cell23_6780749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_6780749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780749 prefixEnd_6780749 := by exact prefixLift 6780749
  have htrace : WordTrace (prefixWord ++ tailWord_6780749) baseStart_6780749 baseEnd_6780749 := by
    simpa [prefixWord, tailWord_6780749, baseEnd_6780749] using wordTrace_append hprefix tailTrace_6780749
  have hstable : (prefixWord ++ tailWord_6780749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780749).length < 2 ^ (prefixWord ++ tailWord_6780749).sum := by decide
  have hdescent : baseEnd_6780749 < baseStart_6780749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780755 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 5]
def baseStart_6780755 : Nat := 118140960795 + 6780755 * 2 ^ 59
def prefixEnd_6780755 : Nat := 4983230072969 + 3 ^ 40 * 6780755 * 2
def baseEnd_6780755 : Nat := 3481786515377722998578381

theorem tailTrace_6780755 : CollatzResearch.WordTrace tailWord_6780755 prefixEnd_6780755 3481786515377722998578381 := by
  unfold tailWord_6780755
  simp only [CollatzResearch.WordTrace]
  refine ⟨247314452549490170601183719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164876301699660113734122479 247314452549490170601183719)
  ·
    refine ⟨370971678824235255901775579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247314452549490170601183719 370971678824235255901775579)
    ·
      refine ⟨556457518236352883852663369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370971678824235255901775579 556457518236352883852663369)
      ·
        refine ⟨417343138677264662889497527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556457518236352883852663369 417343138677264662889497527)
        ·
          refine ⟨626014708015896994334246291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417343138677264662889497527 626014708015896994334246291)
          ·
            refine ⟨939022062023845491501369437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626014708015896994334246291 939022062023845491501369437)
            ·
              refine ⟨352133273258942059313013539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 939022062023845491501369437 352133273258942059313013539)
              ·
                refine ⟨528199909888413088969520309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352133273258942059313013539 528199909888413088969520309)
                ·
                  refine ⟨49518741552038727090892529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 528199909888413088969520309 49518741552038727090892529)
                  ·
                    refine ⟨37139056164029045318169397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49518741552038727090892529 37139056164029045318169397)
                    ·
                      refine ⟨3481786515377722998578381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37139056164029045318169397 3481786515377722998578381)
                      ·
                        rfl

theorem cell23_6780755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_6780755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780755 prefixEnd_6780755 := by exact prefixLift 6780755
  have htrace : WordTrace (prefixWord ++ tailWord_6780755) baseStart_6780755 baseEnd_6780755 := by
    simpa [prefixWord, tailWord_6780755, baseEnd_6780755] using wordTrace_append hprefix tailTrace_6780755
  have hstable : (prefixWord ++ tailWord_6780755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780755).length < 2 ^ (prefixWord ++ tailWord_6780755).sum := by decide
  have hdescent : baseEnd_6780755 < baseStart_6780755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780762 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 2, 5]
def baseStart_6780762 : Nat := 118140960795 + 6780762 * 2 ^ 59
def prefixEnd_6780762 : Nat := 4983230072969 + 3 ^ 40 * 6780762 * 2
def baseEnd_6780762 : Nat := 1160596703247434823730283

theorem tailTrace_6780762 : CollatzResearch.WordTrace tailWord_6780762 prefixEnd_6780762 1160596703247434823730283 := by
  unfold tailWord_6780762
  simp only [CollatzResearch.WordTrace]
  refine ⟨61828676965116202699172135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164876471906976540531125693 61828676965116202699172135)
  ·
    refine ⟨92743015447674304048758203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61828676965116202699172135 92743015447674304048758203)
    ·
      refine ⟨139114523171511456073137305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92743015447674304048758203 139114523171511456073137305)
      ·
        refine ⟨104335892378633592054852979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139114523171511456073137305 104335892378633592054852979)
        ·
          refine ⟨156503838567950388082279469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104335892378633592054852979 156503838567950388082279469)
          ·
            refine ⟨58688939462981395530854801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156503838567950388082279469 58688939462981395530854801)
            ·
              refine ⟨44016704597236046648141101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58688939462981395530854801 44016704597236046648141101)
              ·
                refine ⟨16506264223963517493052913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44016704597236046648141101 16506264223963517493052913)
                ·
                  refine ⟨12379698167972638119789685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16506264223963517493052913 12379698167972638119789685)
                  ·
                    refine ⟨1160596703247434823730283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12379698167972638119789685 1160596703247434823730283)
                    ·
                      rfl

theorem cell23_6780762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_6780762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780762 prefixEnd_6780762 := by exact prefixLift 6780762
  have htrace : WordTrace (prefixWord ++ tailWord_6780762) baseStart_6780762 baseEnd_6780762 := by
    simpa [prefixWord, tailWord_6780762, baseEnd_6780762] using wordTrace_append hprefix tailTrace_6780762
  have hstable : (prefixWord ++ tailWord_6780762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780762).length < 2 ^ (prefixWord ++ tailWord_6780762).sum := by decide
  have hdescent : baseEnd_6780762 < baseStart_6780762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780839 : List Nat := [1, 1, 6, 1, 2, 1, 1, 4, 6]
def baseStart_6780839 : Nat := 118140960795 + 6780839 * 2 ^ 59
def prefixEnd_6780839 : Nat := 4983230072969 + 3 ^ 40 * 6780839 * 2
def baseEnd_6780839 : Nat := 386869960861411185547555

theorem tailTrace_6780839 : CollatzResearch.WordTrace tailWord_6780839 prefixEnd_6780839 386869960861411185547555 := by
  unfold tailWord_6780839
  simp only [CollatzResearch.WordTrace]
  refine ⟨247317516281185852947241571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164878344187457235298161047 247317516281185852947241571)
  ·
    refine ⟨370976274421778779420862357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247317516281185852947241571 370976274421778779420862357)
    ·
      refine ⟨17389512863520880285352923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 370976274421778779420862357 17389512863520880285352923)
      ·
        refine ⟨26084269295281320428029385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17389512863520880285352923 26084269295281320428029385)
        ·
          refine ⟨19563201971460990321022039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26084269295281320428029385 19563201971460990321022039)
          ·
            refine ⟨29344802957191485481533059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19563201971460990321022039 29344802957191485481533059)
            ·
              refine ⟨44017204435787228222299589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29344802957191485481533059 44017204435787228222299589)
              ·
                refine ⟨8253225831710105291681173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44017204435787228222299589 8253225831710105291681173)
                ·
                  refine ⟨386869960861411185547555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8253225831710105291681173 386869960861411185547555)
                  ·
                    rfl

theorem cell23_6780839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 6].length) (baseStart_6780839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780839 prefixEnd_6780839 := by exact prefixLift 6780839
  have htrace : WordTrace (prefixWord ++ tailWord_6780839) baseStart_6780839 baseEnd_6780839 := by
    simpa [prefixWord, tailWord_6780839, baseEnd_6780839] using wordTrace_append hprefix tailTrace_6780839
  have hstable : (prefixWord ++ tailWord_6780839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780839).length < 2 ^ (prefixWord ++ tailWord_6780839).sum := by decide
  have hdescent : baseEnd_6780839 < baseStart_6780839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780859 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 6, 3, 2]
def baseStart_6780859 : Nat := 118140960795 + 6780859 * 2 ^ 59
def prefixEnd_6780859 : Nat := 4983230072969 + 3 ^ 40 * 6780859 * 2
def baseEnd_6780859 : Nat := 3481839917365790591677903

theorem tailTrace_6780859 : CollatzResearch.WordTrace tailWord_6780859 prefixEnd_6780859 3481839917365790591677903 := by
  unfold tailWord_6780859
  simp only [CollatzResearch.WordTrace]
  refine ⟨247318245741113396362969631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164878830494075597575313087 247318245741113396362969631)
  ·
    refine ⟨370977368611670094544454447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247318245741113396362969631 370977368611670094544454447)
    ·
      refine ⟨556466052917505141816681671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370977368611670094544454447 556466052917505141816681671)
      ·
        refine ⟨834699079376257712725022507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556466052917505141816681671 834699079376257712725022507)
        ·
          refine ⟨1252048619064386569087533761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834699079376257712725022507 1252048619064386569087533761)
          ·
            refine ⟨939036464298289926815650321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1252048619064386569087533761 939036464298289926815650321)
            ·
              refine ⟨704277348223717445111737741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939036464298289926815650321 704277348223717445111737741)
              ·
                refine ⟨264104005583894041916901653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 704277348223717445111737741 264104005583894041916901653)
                ·
                  refine ⟨12379875261745033214854765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 264104005583894041916901653 12379875261745033214854765)
                  ·
                    refine ⟨4642453223154387455570537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12379875261745033214854765 4642453223154387455570537)
                    ·
                      refine ⟨3481839917365790591677903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642453223154387455570537 3481839917365790591677903)
                      ·
                        rfl

theorem cell23_6780859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 3, 2].length) (baseStart_6780859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780859 prefixEnd_6780859 := by exact prefixLift 6780859
  have htrace : WordTrace (prefixWord ++ tailWord_6780859) baseStart_6780859 baseEnd_6780859 := by
    simpa [prefixWord, tailWord_6780859, baseEnd_6780859] using wordTrace_append hprefix tailTrace_6780859
  have hstable : (prefixWord ++ tailWord_6780859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780859).length < 2 ^ (prefixWord ++ tailWord_6780859).sum := by decide
  have hdescent : baseEnd_6780859 < baseStart_6780859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780876 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 1, 5, 2]
def baseStart_6780876 : Nat := 118140960795 + 6780876 * 2 ^ 59
def prefixEnd_6780876 : Nat := 4983230072969 + 3 ^ 40 * 6780876 * 2
def baseEnd_6780876 : Nat := 3481848646536917025165325

theorem tailTrace_6780876 : CollatzResearch.WordTrace tailWord_6780876 prefixEnd_6780876 3481848646536917025165325 := by
  unfold tailWord_6780876
  simp only [CollatzResearch.WordTrace]
  refine ⟨123659432891025904133169241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164879243854701205510892321 123659432891025904133169241)
  ·
    refine ⟨92744574668269428099876931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123659432891025904133169241 92744574668269428099876931)
    ·
      refine ⟨139116862002404142149815397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92744574668269428099876931 139116862002404142149815397)
      ·
        refine ⟨26084411625450776653090387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139116862002404142149815397 26084411625450776653090387)
        ·
          refine ⟨39126617438176164979635581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26084411625450776653090387 39126617438176164979635581)
          ·
            refine ⟨14672481539316061867363343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39126617438176164979635581 14672481539316061867363343)
            ·
              refine ⟨22008722308974092801045015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14672481539316061867363343 22008722308974092801045015)
              ·
                refine ⟨33013083463461139201567523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22008722308974092801045015 33013083463461139201567523)
                ·
                  refine ⟨49519625195191708802351285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33013083463461139201567523 49519625195191708802351285)
                  ·
                    refine ⟨4642464862049222700220433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49519625195191708802351285 4642464862049222700220433)
                    ·
                      refine ⟨3481848646536917025165325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642464862049222700220433 3481848646536917025165325)
                      ·
                        rfl

theorem cell23_6780876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_6780876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780876 prefixEnd_6780876 := by exact prefixLift 6780876
  have htrace : WordTrace (prefixWord ++ tailWord_6780876) baseStart_6780876 baseEnd_6780876 := by
    simpa [prefixWord, tailWord_6780876, baseEnd_6780876] using wordTrace_append hprefix tailTrace_6780876
  have hstable : (prefixWord ++ tailWord_6780876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780876).length < 2 ^ (prefixWord ++ tailWord_6780876).sum := by decide
  have hdescent : baseEnd_6780876 < baseStart_6780876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780939 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 3]
def baseStart_6780939 : Nat := 118140960795 + 6780939 * 2 ^ 59
def prefixEnd_6780939 : Nat := 4983230072969 + 3 ^ 40 * 6780939 * 2
def baseEnd_6780939 : Nat := 3481880995818150278677535

theorem tailTrace_6780939 : CollatzResearch.WordTrace tailWord_6780939 prefixEnd_6780939 3481880995818150278677535 := by
  unfold tailWord_6780939
  simp only [CollatzResearch.WordTrace]
  refine ⟨247321163580823570025881871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164880775720549046683921247 247321163580823570025881871)
  ·
    refine ⟨370981745371235355038822807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247321163580823570025881871 370981745371235355038822807)
    ·
      refine ⟨556472618056853032558234211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370981745371235355038822807 556472618056853032558234211)
      ·
        refine ⟨834708927085279548837351317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556472618056853032558234211 834708927085279548837351317)
        ·
          refine ⟨39126980957122478851750843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 834708927085279548837351317 39126980957122478851750843)
          ·
            refine ⟨58690471435683718277626265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39126980957122478851750843 58690471435683718277626265)
            ·
              refine ⟨44017853576762788708219699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58690471435683718277626265 44017853576762788708219699)
              ·
                refine ⟨66026780365144183062329549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44017853576762788708219699 66026780365144183062329549)
                ·
                  refine ⟨24760042636929068648373581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66026780365144183062329549 24760042636929068648373581)
                  ·
                    refine ⟨9285015988848400743140093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24760042636929068648373581 9285015988848400743140093)
                    ·
                      refine ⟨3481880995818150278677535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9285015988848400743140093 3481880995818150278677535)
                      ·
                        rfl

theorem cell23_6780939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 3].length) (baseStart_6780939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780939 prefixEnd_6780939 := by exact prefixLift 6780939
  have htrace : WordTrace (prefixWord ++ tailWord_6780939) baseStart_6780939 baseEnd_6780939 := by
    simpa [prefixWord, tailWord_6780939, baseEnd_6780939] using wordTrace_append hprefix tailTrace_6780939
  have hstable : (prefixWord ++ tailWord_6780939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780939).length < 2 ^ (prefixWord ++ tailWord_6780939).sum := by decide
  have hdescent : baseEnd_6780939 < baseStart_6780939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780967 : List Nat := [1, 1, 7, 1, 2, 2, 2, 1, 2, 4]
def baseStart_6780967 : Nat := 118140960795 + 6780967 * 2 ^ 59
def prefixEnd_6780967 : Nat := 4983230072969 + 3 ^ 40 * 6780967 * 2
def baseEnd_6780967 : Nat := 1160631791092158723042469

theorem tailTrace_6780967 : CollatzResearch.WordTrace tailWord_6780967 prefixEnd_6780967 1160631791092158723042469 := by
  unfold tailWord_6780967
  simp only [CollatzResearch.WordTrace]
  refine ⟨247322184824722130807901155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164881456549814753871934103 247322184824722130807901155)
  ·
    refine ⟨370983277237083196211851733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247322184824722130807901155 370983277237083196211851733)
    ·
      refine ⟨8694920560244137411215275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 370983277237083196211851733 8694920560244137411215275)
      ·
        refine ⟨13042380840366206116822913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8694920560244137411215275 13042380840366206116822913)
        ·
          refine ⟨9781785630274654587617185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13042380840366206116822913 9781785630274654587617185)
          ·
            refine ⟨7336339222705990940712889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9781785630274654587617185 7336339222705990940712889)
            ·
              refine ⟨5502254417029493205534667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7336339222705990940712889 5502254417029493205534667)
              ·
                refine ⟨8253381625544239808302001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5502254417029493205534667 8253381625544239808302001)
                ·
                  refine ⟨6190036219158179856226501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8253381625544239808302001 6190036219158179856226501)
                  ·
                    refine ⟨1160631791092158723042469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6190036219158179856226501 1160631791092158723042469)
                    ·
                      rfl

theorem cell23_6780967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_6780967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780967 prefixEnd_6780967 := by exact prefixLift 6780967
  have htrace : WordTrace (prefixWord ++ tailWord_6780967) baseStart_6780967 baseEnd_6780967 := by
    simpa [prefixWord, tailWord_6780967, baseEnd_6780967] using wordTrace_append hprefix tailTrace_6780967
  have hstable : (prefixWord ++ tailWord_6780967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780967).length < 2 ^ (prefixWord ++ tailWord_6780967).sum := by decide
  have hdescent : baseEnd_6780967 < baseStart_6780967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780983 : List Nat := [1, 1, 3, 1, 2, 2, 5, 2, 1, 3, 2]
def baseStart_6780983 : Nat := 118140960795 + 6780983 * 2 ^ 59
def prefixEnd_6780983 : Nat := 4983230072969 + 3 ^ 40 * 6780983 * 2
def baseEnd_6780983 : Nat := 3481903588966948106527333

theorem tailTrace_6780983 : CollatzResearch.WordTrace tailWord_6780983 prefixEnd_6780983 3481903588966948106527333 := by
  unfold tailWord_6780983
  simp only [CollatzResearch.WordTrace]
  refine ⟨247322768392664165540483603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164881845595109443693655735 247322768392664165540483603)
  ·
    refine ⟨370984152588996248310725405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247322768392664165540483603 370984152588996248310725405)
    ·
      refine ⟨139119057220873593116522027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370984152588996248310725405 139119057220873593116522027)
      ·
        refine ⟨208678585831310389674783041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139119057220873593116522027 208678585831310389674783041)
        ·
          refine ⟨156508939373482792256087281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208678585831310389674783041 156508939373482792256087281)
          ·
            refine ⟨117381704530112094192065461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156508939373482792256087281 117381704530112094192065461)
            ·
              refine ⟨11004534799698008830506137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117381704530112094192065461 11004534799698008830506137)
              ·
                refine ⟨8253401099773506622879603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11004534799698008830506137 8253401099773506622879603)
                ·
                  refine ⟨12380101649660259934319405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8253401099773506622879603 12380101649660259934319405)
                  ·
                    refine ⟨4642538118622597475369777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12380101649660259934319405 4642538118622597475369777)
                    ·
                      refine ⟨3481903588966948106527333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642538118622597475369777 3481903588966948106527333)
                      ·
                        rfl

theorem cell23_6780983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 3, 2].length) (baseStart_6780983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780983 prefixEnd_6780983 := by exact prefixLift 6780983
  have htrace : WordTrace (prefixWord ++ tailWord_6780983) baseStart_6780983 baseEnd_6780983 := by
    simpa [prefixWord, tailWord_6780983, baseEnd_6780983] using wordTrace_append hprefix tailTrace_6780983
  have hstable : (prefixWord ++ tailWord_6780983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780983).length < 2 ^ (prefixWord ++ tailWord_6780983).sum := by decide
  have hdescent : baseEnd_6780983 < baseStart_6780983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6780999 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_6780999 : Nat := 118140960795 + 6780999 * 2 ^ 59
def prefixEnd_6780999 : Nat := 4983230072969 + 3 ^ 40 * 6780999 * 2
def baseEnd_6780999 : Nat := 3481911804657420043927259

theorem tailTrace_6780999 : CollatzResearch.WordTrace tailWord_6780999 prefixEnd_6780999 3481911804657420043927259 := by
  unfold tailWord_6780999
  simp only [CollatzResearch.WordTrace]
  refine ⟨247323351960606200273066051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164882234640404133515377367 247323351960606200273066051)
  ·
    refine ⟨370985027940909300409599077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247323351960606200273066051 370985027940909300409599077)
    ·
      refine ⟨69559692738920493826799827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370985027940909300409599077 69559692738920493826799827)
      ·
        refine ⟨104339539108380740740199741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69559692738920493826799827 104339539108380740740199741)
        ·
          refine ⟨39127327165642777777574903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104339539108380740740199741 39127327165642777777574903)
          ·
            refine ⟨58690990748464166666362355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39127327165642777777574903 58690990748464166666362355)
            ·
              refine ⟨88036486122696249999543533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58690990748464166666362355 88036486122696249999543533)
              ·
                refine ⟨33013682296011093749828825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88036486122696249999543533 33013682296011093749828825)
                ·
                  refine ⟨24760261722008320312371619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33013682296011093749828825 24760261722008320312371619)
                  ·
                    refine ⟨37140392583012480468557429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24760261722008320312371619 37140392583012480468557429)
                    ·
                      refine ⟨3481911804657420043927259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37140392583012480468557429 3481911804657420043927259)
                      ·
                        rfl

theorem cell23_6780999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_6780999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6780999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6780999 prefixEnd_6780999 := by exact prefixLift 6780999
  have htrace : WordTrace (prefixWord ++ tailWord_6780999) baseStart_6780999 baseEnd_6780999 := by
    simpa [prefixWord, tailWord_6780999, baseEnd_6780999] using wordTrace_append hprefix tailTrace_6780999
  have hstable : (prefixWord ++ tailWord_6780999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6780999).length < 2 ^ (prefixWord ++ tailWord_6780999).sum := by decide
  have hdescent : baseEnd_6780999 < baseStart_6780999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6780999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781009 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_6781009 : Nat := 118140960795 + 6781009 * 2 ^ 59
def prefixEnd_6781009 : Nat := 4983230072969 + 3 ^ 40 * 6781009 * 2
def baseEnd_6781009 : Nat := 3481916939463965004802213

theorem tailTrace_6781009 : CollatzResearch.WordTrace tailWord_6781009 prefixEnd_6781009 3481916939463965004802213 := by
  unfold tailWord_6781009
  simp only [CollatzResearch.WordTrace]
  refine ⟨247323716690569971980930081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164882477793713314653953387 247323716690569971980930081)
  ·
    refine ⟨185492787517927478985697561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247323716690569971980930081 185492787517927478985697561)
    ·
      refine ⟨139119590638445609239273171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185492787517927478985697561 139119590638445609239273171)
      ·
        refine ⟨208679385957668413858909757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139119590638445609239273171 208679385957668413858909757)
        ·
          refine ⟨78254769734125655197091159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208679385957668413858909757 78254769734125655197091159)
          ·
            refine ⟨117382154601188482795636739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78254769734125655197091159 117382154601188482795636739)
            ·
              refine ⟨176073231901782724193455109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117382154601188482795636739 176073231901782724193455109)
              ·
                refine ⟨33013730981584260786272833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176073231901782724193455109 33013730981584260786272833)
                ·
                  refine ⟨24760298236188195589704625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33013730981584260786272833 24760298236188195589704625)
                  ·
                    refine ⟨18570223677141146692278469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24760298236188195589704625 18570223677141146692278469)
                    ·
                      refine ⟨3481916939463965004802213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18570223677141146692278469 3481916939463965004802213)
                      ·
                        rfl

theorem cell23_6781009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_6781009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781009 prefixEnd_6781009 := by exact prefixLift 6781009
  have htrace : WordTrace (prefixWord ++ tailWord_6781009) baseStart_6781009 baseEnd_6781009 := by
    simpa [prefixWord, tailWord_6781009, baseEnd_6781009] using wordTrace_append hprefix tailTrace_6781009
  have hstable : (prefixWord ++ tailWord_6781009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781009).length < 2 ^ (prefixWord ++ tailWord_6781009).sum := by decide
  have hdescent : baseEnd_6781009 < baseStart_6781009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781053 : List Nat := [1, 4, 1, 1, 3, 3, 2, 3, 5]
def baseStart_6781053 : Nat := 118140960795 + 6781053 * 2 ^ 59
def prefixEnd_6781053 : Nat := 4983230072969 + 3 ^ 40 * 6781053 * 2
def baseEnd_6781053 : Nat := 386882170290306981405779

theorem tailTrace_6781053 : CollatzResearch.WordTrace tailWord_6781053 prefixEnd_6781053 386882170290306981405779 := by
  unfold tailWord_6781053
  simp only [CollatzResearch.WordTrace]
  refine ⟨247325321502410567495531813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164883547668273711663687875 247325321502410567495531813)
  ·
    refine ⟨46373497781701981405412215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247325321502410567495531813 46373497781701981405412215)
    ·
      refine ⟨69560246672552972108118323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46373497781701981405412215 69560246672552972108118323)
      ·
        refine ⟨104340370008829458162177485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69560246672552972108118323 104340370008829458162177485)
        ·
          refine ⟨39127638753311046810816557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104340370008829458162177485 39127638753311046810816557)
          ·
            refine ⟨14672864532491642554056209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39127638753311046810816557 14672864532491642554056209)
            ·
              refine ⟨11004648399368731915542157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14672864532491642554056209 11004648399368731915542157)
              ·
                refine ⟨4126743149763274468328309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11004648399368731915542157 4126743149763274468328309)
                ·
                  refine ⟨386882170290306981405779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4126743149763274468328309 386882170290306981405779)
                  ·
                    rfl

theorem cell23_6781053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_6781053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781053 prefixEnd_6781053 := by exact prefixLift 6781053
  have htrace : WordTrace (prefixWord ++ tailWord_6781053) baseStart_6781053 baseEnd_6781053 := by
    simpa [prefixWord, tailWord_6781053, baseEnd_6781053] using wordTrace_append hprefix tailTrace_6781053
  have hstable : (prefixWord ++ tailWord_6781053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781053).length < 2 ^ (prefixWord ++ tailWord_6781053).sum := by decide
  have hdescent : baseEnd_6781053 < baseStart_6781053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781106 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_6781106 : Nat := 118140960795 + 6781106 * 2 ^ 59
def prefixEnd_6781106 : Nat := 4983230072969 + 3 ^ 40 * 6781106 * 2
def baseEnd_6781106 : Nat := 3481966747087451125289267

theorem tailTrace_6781106 : CollatzResearch.WordTrace tailWord_6781106 prefixEnd_6781106 3481966747087451125289267 := by
  unfold tailWord_6781106
  simp only [CollatzResearch.WordTrace]
  refine ⟨61831813642804639386802793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164884836380812371698140781 61831813642804639386802793)
  ·
    refine ⟨46373860232103479540102095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61831813642804639386802793 46373860232103479540102095)
    ·
      refine ⟨69560790348155219310153143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46373860232103479540102095 69560790348155219310153143)
      ·
        refine ⟨104341185522232828965229715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69560790348155219310153143 104341185522232828965229715)
        ·
          refine ⟨156511778283349243447844573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104341185522232828965229715 156511778283349243447844573)
          ·
            refine ⟨58691916856255966292941715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156511778283349243447844573 58691916856255966292941715)
            ·
              refine ⟨88037875284383949439412573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58691916856255966292941715 88037875284383949439412573)
              ·
                refine ⟨33014203231643981039779715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88037875284383949439412573 33014203231643981039779715)
                ·
                  refine ⟨49521304847465971559669573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33014203231643981039779715 49521304847465971559669573)
                  ·
                    refine ⟨9285244658899869667438045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49521304847465971559669573 9285244658899869667438045)
                    ·
                      refine ⟨3481966747087451125289267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9285244658899869667438045 3481966747087451125289267)
                      ·
                        rfl

theorem cell23_6781106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_6781106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781106 prefixEnd_6781106 := by exact prefixLift 6781106
  have htrace : WordTrace (prefixWord ++ tailWord_6781106) baseStart_6781106 baseEnd_6781106 := by
    simpa [prefixWord, tailWord_6781106, baseEnd_6781106] using wordTrace_append hprefix tailTrace_6781106
  have hstable : (prefixWord ++ tailWord_6781106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781106).length < 2 ^ (prefixWord ++ tailWord_6781106).sum := by decide
  have hdescent : baseEnd_6781106 < baseStart_6781106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781129 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 6]
def baseStart_6781129 : Nat := 118140960795 + 6781129 * 2 ^ 59
def prefixEnd_6781129 : Nat := 4983230072969 + 3 ^ 40 * 6781129 * 2
def baseEnd_6781129 : Nat := 3481978557142504535301661

theorem tailTrace_6781129 : CollatzResearch.WordTrace tailWord_6781129 prefixEnd_6781129 3481978557142504535301661 := by
  unfold tailWord_6781129
  simp only [CollatzResearch.WordTrace]
  refine ⟨247328093450135232475298441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164885395633423488316865627 247328093450135232475298441)
  ·
    refine ⟨185496070087601424356473831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247328093450135232475298441 185496070087601424356473831)
    ·
      refine ⟨278244105131402136534710747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185496070087601424356473831 278244105131402136534710747)
      ·
        refine ⟨417366157697103204802066121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278244105131402136534710747 417366157697103204802066121)
        ·
          refine ⟨313024618272827403601549591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417366157697103204802066121 313024618272827403601549591)
          ·
            refine ⟨469536927409241105402324387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313024618272827403601549591 469536927409241105402324387)
            ·
              refine ⟨704305391113861658103486581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469536927409241105402324387 704305391113861658103486581)
              ·
                refine ⟨66028630416924530447201867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 704305391113861658103486581 66028630416924530447201867)
                ·
                  refine ⟨99042945625386795670802801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66028630416924530447201867 99042945625386795670802801)
                  ·
                    refine ⟨74282209219040096753102101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99042945625386795670802801 74282209219040096753102101)
                    ·
                      refine ⟨3481978557142504535301661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74282209219040096753102101 3481978557142504535301661)
                      ·
                        rfl

theorem cell23_6781129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_6781129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781129 prefixEnd_6781129 := by exact prefixLift 6781129
  have htrace : WordTrace (prefixWord ++ tailWord_6781129) baseStart_6781129 baseEnd_6781129 := by
    simpa [prefixWord, tailWord_6781129, baseEnd_6781129] using wordTrace_append hprefix tailTrace_6781129
  have hstable : (prefixWord ++ tailWord_6781129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781129).length < 2 ^ (prefixWord ++ tailWord_6781129).sum := by decide
  have hdescent : baseEnd_6781129 < baseStart_6781129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781153 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_6781153 : Nat := 118140960795 + 6781153 * 2 ^ 59
def prefixEnd_6781153 : Nat := 4983230072969 + 3 ^ 40 * 6781153 * 2
def baseEnd_6781153 : Nat := 3481990880678212441401551

theorem tailTrace_6781153 : CollatzResearch.WordTrace tailWord_6781153 prefixEnd_6781153 3481990880678212441401551 := by
  unfold tailWord_6781153
  simp only [CollatzResearch.WordTrace]
  refine ⟨247328968802048284574172113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164885979201365523049448075 247328968802048284574172113)
  ·
    refine ⟨185496726601536213430629085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247328968802048284574172113 185496726601536213430629085)
    ·
      refine ⟨69561272475576080036485907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185496726601536213430629085 69561272475576080036485907)
      ·
        refine ⟨104341908713364120054728861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69561272475576080036485907 104341908713364120054728861)
        ·
          refine ⟨39128215767511545020523323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104341908713364120054728861 39128215767511545020523323)
          ·
            refine ⟨58692323651267317530784985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39128215767511545020523323 58692323651267317530784985)
            ·
              refine ⟨44019242738450488148088739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58692323651267317530784985 44019242738450488148088739)
              ·
                refine ⟨66028864107675732222133109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44019242738450488148088739 66028864107675732222133109)
                ·
                  refine ⟨6190206010094599895824979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66028864107675732222133109 6190206010094599895824979)
                  ·
                    refine ⟨9285309015141899843737469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6190206010094599895824979 9285309015141899843737469)
                    ·
                      refine ⟨3481990880678212441401551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9285309015141899843737469 3481990880678212441401551)
                      ·
                        rfl

theorem cell23_6781153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_6781153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781153 prefixEnd_6781153 := by exact prefixLift 6781153
  have htrace : WordTrace (prefixWord ++ tailWord_6781153) baseStart_6781153 baseEnd_6781153 := by
    simpa [prefixWord, tailWord_6781153, baseEnd_6781153] using wordTrace_append hprefix tailTrace_6781153
  have hstable : (prefixWord ++ tailWord_6781153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781153).length < 2 ^ (prefixWord ++ tailWord_6781153).sum := by decide
  have hdescent : baseEnd_6781153 < baseStart_6781153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781154 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6781154 : Nat := 118140960795 + 6781154 * 2 ^ 59
def prefixEnd_6781154 : Nat := 4983230072969 + 3 ^ 40 * 6781154 * 2
def baseEnd_6781154 : Nat := 3481991394158866937489047

theorem tailTrace_6781154 : CollatzResearch.WordTrace tailWord_6781154 prefixEnd_6781154 3481991394158866937489047 := by
  unfold tailWord_6781154
  simp only [CollatzResearch.WordTrace]
  refine ⟨61832251318761165436239629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164886003516696441163305677 61832251318761165436239629)
  ·
    refine ⟨23187094244535437038589861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61832251318761165436239629 23187094244535437038589861)
    ·
      refine ⟨4347580170850394444735599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23187094244535437038589861 4347580170850394444735599)
      ·
        refine ⟨6521370256275591667103399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4347580170850394444735599 6521370256275591667103399)
        ·
          refine ⟨9782055384413387500655099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6521370256275591667103399 9782055384413387500655099)
          ·
            refine ⟨14673083076620081250982649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9782055384413387500655099 14673083076620081250982649)
            ·
              refine ⟨11004812307465060938236987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14673083076620081250982649 11004812307465060938236987)
              ·
                refine ⟨16507218461197591407355481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11004812307465060938236987 16507218461197591407355481)
                ·
                  refine ⟨12380413845898193555516611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16507218461197591407355481 12380413845898193555516611)
                  ·
                    refine ⟨18570620768847290333274917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12380413845898193555516611 18570620768847290333274917)
                    ·
                      refine ⟨3481991394158866937489047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18570620768847290333274917 3481991394158866937489047)
                      ·
                        rfl

theorem cell23_6781154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6781154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781154 prefixEnd_6781154 := by exact prefixLift 6781154
  have htrace : WordTrace (prefixWord ++ tailWord_6781154) baseStart_6781154 baseEnd_6781154 := by
    simpa [prefixWord, tailWord_6781154, baseEnd_6781154] using wordTrace_append hprefix tailTrace_6781154
  have hstable : (prefixWord ++ tailWord_6781154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781154).length < 2 ^ (prefixWord ++ tailWord_6781154).sum := by decide
  have hdescent : baseEnd_6781154 < baseStart_6781154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781180 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 2, 3, 2]
def baseStart_6781180 : Nat := 118140960795 + 6781180 * 2 ^ 59
def prefixEnd_6781180 : Nat := 4983230072969 + 3 ^ 40 * 6781180 * 2
def baseEnd_6781180 : Nat := 3482004744655883835763927

theorem tailTrace_6781180 : CollatzResearch.WordTrace tailWord_6781180 prefixEnd_6781180 3482004744655883835763927 := by
  unfold tailWord_6781180
  simp only [CollatzResearch.WordTrace]
  refine ⟨123664976786475234092702497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164886635715300312123603329 123664976786475234092702497)
  ·
    refine ⟨92748732589856425569526873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123664976786475234092702497 92748732589856425569526873)
    ·
      refine ⟨69561549442392319177145155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92748732589856425569526873 69561549442392319177145155)
      ·
        refine ⟨104342324163588478765717733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69561549442392319177145155 104342324163588478765717733)
        ·
          refine ⟨19564185780672839768572075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104342324163588478765717733 19564185780672839768572075)
          ·
            refine ⟨29346278671009259652858113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19564185780672839768572075 29346278671009259652858113)
            ·
              refine ⟨22009709003256944739643585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29346278671009259652858113 22009709003256944739643585)
              ·
                refine ⟨16507281752442708554732689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22009709003256944739643585 16507281752442708554732689)
                ·
                  refine ⟨12380461314332031416049517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16507281752442708554732689 12380461314332031416049517)
                  ·
                    refine ⟨4642672992874511781018569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12380461314332031416049517 4642672992874511781018569)
                    ·
                      refine ⟨3482004744655883835763927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642672992874511781018569 3482004744655883835763927)
                      ·
                        rfl

theorem cell23_6781180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_6781180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781180 prefixEnd_6781180 := by exact prefixLift 6781180
  have htrace : WordTrace (prefixWord ++ tailWord_6781180) baseStart_6781180 baseEnd_6781180 := by
    simpa [prefixWord, tailWord_6781180, baseEnd_6781180] using wordTrace_append hprefix tailTrace_6781180
  have hstable : (prefixWord ++ tailWord_6781180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781180).length < 2 ^ (prefixWord ++ tailWord_6781180).sum := by decide
  have hdescent : baseEnd_6781180 < baseStart_6781180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781196 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_6781196 : Nat := 118140960795 + 6781196 * 2 ^ 59
def prefixEnd_6781196 : Nat := 4983230072969 + 3 ^ 40 * 6781196 * 2
def baseEnd_6781196 : Nat := 3482012960346355773163853

theorem tailTrace_6781196 : CollatzResearch.WordTrace tailWord_6781196 prefixEnd_6781196 3482012960346355773163853 := by
  unfold tailWord_6781196
  simp only [CollatzResearch.WordTrace]
  refine ⟨123665268570446251458993721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164887024760595001945324961 123665268570446251458993721)
  ·
    refine ⟨92748951427834688594245291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123665268570446251458993721 92748951427834688594245291)
    ·
      refine ⟨139123427141752032891367937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92748951427834688594245291 139123427141752032891367937)
      ·
        refine ⟨104342570356314024668525953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139123427141752032891367937 104342570356314024668525953)
        ·
          refine ⟨78256927767235518501394465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104342570356314024668525953 78256927767235518501394465)
          ·
            refine ⟨58692695825426638876045849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78256927767235518501394465 58692695825426638876045849)
            ·
              refine ⟨44019521869069979157034387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58692695825426638876045849 44019521869069979157034387)
              ·
                refine ⟨66029282803604968735551581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44019521869069979157034387 66029282803604968735551581)
                ·
                  refine ⟨24760981051351863275831843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66029282803604968735551581 24760981051351863275831843)
                  ·
                    refine ⟨37141471577027794913747765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24760981051351863275831843 37141471577027794913747765)
                    ·
                      refine ⟨3482012960346355773163853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37141471577027794913747765 3482012960346355773163853)
                      ·
                        rfl

theorem cell23_6781196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_6781196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781196 prefixEnd_6781196 := by exact prefixLift 6781196
  have htrace : WordTrace (prefixWord ++ tailWord_6781196) baseStart_6781196 baseEnd_6781196 := by
    simpa [prefixWord, tailWord_6781196, baseEnd_6781196] using wordTrace_append hprefix tailTrace_6781196
  have hstable : (prefixWord ++ tailWord_6781196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781196).length < 2 ^ (prefixWord ++ tailWord_6781196).sum := by decide
  have hdescent : baseEnd_6781196 < baseStart_6781196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781214 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_6781214 : Nat := 118140960795 + 6781214 * 2 ^ 59
def prefixEnd_6781214 : Nat := 4983230072969 + 3 ^ 40 * 6781214 * 2
def baseEnd_6781214 : Nat := 3482022202998136702738771

theorem tailTrace_6781214 : CollatzResearch.WordTrace tailWord_6781214 prefixEnd_6781214 3482022202998136702738771 := by
  unfold tailWord_6781214
  simp only [CollatzResearch.WordTrace]
  refine ⟨30916399206853411499017837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164887462436551527994761797 30916399206853411499017837)
  ·
    refine ⟨11593649702570029312131689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30916399206853411499017837 11593649702570029312131689)
    ·
      refine ⟨8695237276927521984098767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11593649702570029312131689 8695237276927521984098767)
      ·
        refine ⟨13042855915391282976148151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8695237276927521984098767 13042855915391282976148151)
        ·
          refine ⟨19564283873086924464222227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13042855915391282976148151 19564283873086924464222227)
          ·
            refine ⟨29346425809630386696333341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19564283873086924464222227 29346425809630386696333341)
            ·
              refine ⟨11004909678611395011125003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29346425809630386696333341 11004909678611395011125003)
              ·
                refine ⟨16507364517917092516687505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11004909678611395011125003 16507364517917092516687505)
                ·
                  refine ⟨12380523388437819387515629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16507364517917092516687505 12380523388437819387515629)
                  ·
                    refine ⟨4642696270664182270318361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12380523388437819387515629 4642696270664182270318361)
                    ·
                      refine ⟨3482022202998136702738771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642696270664182270318361 3482022202998136702738771)
                      ·
                        rfl

theorem cell23_6781214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_6781214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781214 prefixEnd_6781214 := by exact prefixLift 6781214
  have htrace : WordTrace (prefixWord ++ tailWord_6781214) baseStart_6781214 baseEnd_6781214 := by
    simpa [prefixWord, tailWord_6781214, baseEnd_6781214] using wordTrace_append hprefix tailTrace_6781214
  have hstable : (prefixWord ++ tailWord_6781214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781214).length < 2 ^ (prefixWord ++ tailWord_6781214).sum := by decide
  have hdescent : baseEnd_6781214 < baseStart_6781214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781224 : List Nat := [2, 1, 5, 1, 4, 1, 2, 1, 1, 5]
def baseStart_6781224 : Nat := 118140960795 + 6781224 * 2 ^ 59
def prefixEnd_6781224 : Nat := 4983230072969 + 3 ^ 40 * 6781224 * 2
def baseEnd_6781224 : Nat := 1160675779268227221204575

theorem tailTrace_6781224 : CollatzResearch.WordTrace tailWord_6781224 prefixEnd_6781224 1160675779268227221204575 := by
  unfold tailWord_6781224
  simp only [CollatzResearch.WordTrace]
  refine ⟨123665779192395531850003363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164887705589860709133337817 123665779192395531850003363)
  ·
    refine ⟨185498668788593297775005045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123665779192395531850003363 185498668788593297775005045)
    ·
      refine ⟨17390500198930621666406723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185498668788593297775005045 17390500198930621666406723)
      ·
        refine ⟨26085750298395932499610085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17390500198930621666406723 26085750298395932499610085)
        ·
          refine ⟨4891078180949237343676891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26085750298395932499610085 4891078180949237343676891)
          ·
            refine ⟨7336617271423856015515337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4891078180949237343676891 7336617271423856015515337)
            ·
              refine ⟨5502462953567892011636503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7336617271423856015515337 5502462953567892011636503)
              ·
                refine ⟨8253694430351838017454755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5502462953567892011636503 8253694430351838017454755)
                ·
                  refine ⟨12380541645527757026182133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8253694430351838017454755 12380541645527757026182133)
                  ·
                    refine ⟨1160675779268227221204575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12380541645527757026182133 1160675779268227221204575)
                    ·
                      rfl

theorem cell23_6781224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_6781224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781224 prefixEnd_6781224 := by exact prefixLift 6781224
  have htrace : WordTrace (prefixWord ++ tailWord_6781224) baseStart_6781224 baseEnd_6781224 := by
    simpa [prefixWord, tailWord_6781224, baseEnd_6781224] using wordTrace_append hprefix tailTrace_6781224
  have hstable : (prefixWord ++ tailWord_6781224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781224).length < 2 ^ (prefixWord ++ tailWord_6781224).sum := by decide
  have hdescent : baseEnd_6781224 < baseStart_6781224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781287 : List Nat := [1, 1, 5, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_6781287 : Nat := 118140960795 + 6781287 * 2 ^ 59
def prefixEnd_6781287 : Nat := 4983230072969 + 3 ^ 40 * 6781287 * 2
def baseEnd_6781287 : Nat := 3482059687085914917125935

theorem tailTrace_6781287 : CollatzResearch.WordTrace tailWord_6781287 prefixEnd_6781287 3482059687085914917125935 := by
  unfold tailWord_6781287
  simp only [CollatzResearch.WordTrace]
  refine ⟨247333856183562825459550115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164889237455708550306366743 247333856183562825459550115)
  ·
    refine ⟨371000784275344238189325173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247333856183562825459550115 371000784275344238189325173)
    ·
      refine ⟨34781323525813522330249235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 371000784275344238189325173 34781323525813522330249235)
      ·
        refine ⟨52171985288720283495373853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34781323525813522330249235 52171985288720283495373853)
        ·
          refine ⟨19564494483270106310765195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52171985288720283495373853 19564494483270106310765195)
          ·
            refine ⟨29346741724905159466147793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19564494483270106310765195 29346741724905159466147793)
            ·
              refine ⟨22010056293678869599610845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29346741724905159466147793 22010056293678869599610845)
              ·
                refine ⟨8253771110129576099854067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22010056293678869599610845 8253771110129576099854067)
                ·
                  refine ⟨12380656665194364149781101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8253771110129576099854067 12380656665194364149781101)
                  ·
                    refine ⟨4642746249447886556167913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12380656665194364149781101 4642746249447886556167913)
                    ·
                      refine ⟨3482059687085914917125935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642746249447886556167913 3482059687085914917125935)
                      ·
                        rfl

theorem cell23_6781287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_6781287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781287 prefixEnd_6781287 := by exact prefixLift 6781287
  have htrace : WordTrace (prefixWord ++ tailWord_6781287) baseStart_6781287 baseEnd_6781287 := by
    simpa [prefixWord, tailWord_6781287, baseEnd_6781287] using wordTrace_append hprefix tailTrace_6781287
  have hstable : (prefixWord ++ tailWord_6781287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781287).length < 2 ^ (prefixWord ++ tailWord_6781287).sum := by decide
  have hdescent : baseEnd_6781287 < baseStart_6781287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781333 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_6781333 : Nat := 118140960795 + 6781333 * 2 ^ 59
def prefixEnd_6781333 : Nat := 4983230072969 + 3 ^ 40 * 6781333 * 2
def baseEnd_6781333 : Nat := 3482083307196021737150723

theorem tailTrace_6781333 : CollatzResearch.WordTrace tailWord_6781333 prefixEnd_6781333 3482083307196021737150723 := by
  unfold tailWord_6781333
  simp only [CollatzResearch.WordTrace]
  refine ⟨247335533941396175315724653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164890355960930783543816435 247335533941396175315724653)
  ·
    refine ⟨92750825228023565743396745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247335533941396175315724653 92750825228023565743396745)
    ·
      refine ⟨69563118921017674307547559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92750825228023565743396745 69563118921017674307547559)
      ·
        refine ⟨104344678381526511461321339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69563118921017674307547559 104344678381526511461321339)
        ·
          refine ⟨156517017572289767191982009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104344678381526511461321339 156517017572289767191982009)
          ·
            refine ⟨117387763179217325393986507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156517017572289767191982009 117387763179217325393986507)
            ·
              refine ⟨176081644768825988090979761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117387763179217325393986507 176081644768825988090979761)
              ·
                refine ⟨132061233576619491068234821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176081644768825988090979761 132061233576619491068234821)
                ·
                  refine ⟨24761481295616154575294029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132061233576619491068234821 24761481295616154575294029)
                  ·
                    refine ⟨9285555485856057965735261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24761481295616154575294029 9285555485856057965735261)
                    ·
                      refine ⟨3482083307196021737150723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9285555485856057965735261 3482083307196021737150723)
                      ·
                        rfl

theorem cell23_6781333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_6781333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781333 prefixEnd_6781333 := by exact prefixLift 6781333
  have htrace : WordTrace (prefixWord ++ tailWord_6781333) baseStart_6781333 baseEnd_6781333 := by
    simpa [prefixWord, tailWord_6781333, baseEnd_6781333] using wordTrace_append hprefix tailTrace_6781333
  have hstable : (prefixWord ++ tailWord_6781333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781333).length < 2 ^ (prefixWord ++ tailWord_6781333).sum := by decide
  have hdescent : baseEnd_6781333 < baseStart_6781333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781364 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_6781364 : Nat := 118140960795 + 6781364 * 2 ^ 59
def prefixEnd_6781364 : Nat := 4983230072969 + 3 ^ 40 * 6781364 * 2
def baseEnd_6781364 : Nat := 3482099225096311115863081

theorem tailTrace_6781364 : CollatzResearch.WordTrace tailWord_6781364 prefixEnd_6781364 3482099225096311115863081 := by
  unfold tailWord_6781364
  simp only [CollatzResearch.WordTrace]
  refine ⟨123668332302141933805051573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164891109736189245073402097 123668332302141933805051573)
  ·
    refine ⟨11593906153325806294223585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123668332302141933805051573 11593906153325806294223585)
    ·
      refine ⟨8695429614994354720667689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11593906153325806294223585 8695429614994354720667689)
      ·
        refine ⟨6521572211245766040500767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8695429614994354720667689 6521572211245766040500767)
        ·
          refine ⟨9782358316868649060751151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6521572211245766040500767 9782358316868649060751151)
          ·
            refine ⟨14673537475302973591126727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9782358316868649060751151 14673537475302973591126727)
            ·
              refine ⟨22010306212954460386690091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14673537475302973591126727 22010306212954460386690091)
              ·
                refine ⟨33015459319431690580035137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22010306212954460386690091 33015459319431690580035137)
                ·
                  refine ⟨24761594489573767935026353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33015459319431690580035137 24761594489573767935026353)
                  ·
                    refine ⟨18571195867180325951269765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24761594489573767935026353 18571195867180325951269765)
                    ·
                      refine ⟨3482099225096311115863081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18571195867180325951269765 3482099225096311115863081)
                      ·
                        rfl

theorem cell23_6781364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_6781364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781364 prefixEnd_6781364 := by exact prefixLift 6781364
  have htrace : WordTrace (prefixWord ++ tailWord_6781364) baseStart_6781364 baseEnd_6781364 := by
    simpa [prefixWord, tailWord_6781364, baseEnd_6781364] using wordTrace_append hprefix tailTrace_6781364
  have hstable : (prefixWord ++ tailWord_6781364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781364).length < 2 ^ (prefixWord ++ tailWord_6781364).sum := by decide
  have hdescent : baseEnd_6781364 < baseStart_6781364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781390 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2]
def baseStart_6781390 : Nat := 118140960795 + 6781390 * 2 ^ 59
def prefixEnd_6781390 : Nat := 4983230072969 + 3 ^ 40 * 6781390 * 2
def baseEnd_6781390 : Nat := 3482112575593328014137961

theorem tailTrace_6781390 : CollatzResearch.WordTrace tailWord_6781390 prefixEnd_6781390 3482112575593328014137961 := by
  unfold tailWord_6781390
  simp only [CollatzResearch.WordTrace]
  refine ⟨30917201612773709256318703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164891741934793116033699749 30917201612773709256318703)
  ·
    refine ⟨46375802419160563884478055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30917201612773709256318703 46375802419160563884478055)
    ·
      refine ⟨69563703628740845826717083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46375802419160563884478055 69563703628740845826717083)
      ·
        refine ⟨104345555443111268740075625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69563703628740845826717083 104345555443111268740075625)
        ·
          refine ⟨78259166582333451555056719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104345555443111268740075625 78259166582333451555056719)
          ·
            refine ⟨117388749873500177332585079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78259166582333451555056719 117388749873500177332585079)
            ·
              refine ⟨176083124810250265998877619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117388749873500177332585079 176083124810250265998877619)
              ·
                refine ⟨264124687215375398998316429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176083124810250265998877619 264124687215375398998316429)
                ·
                  refine ⟨99046757705765774624368661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264124687215375398998316429 99046757705765774624368661)
                  ·
                    refine ⟨4642816767457770685517281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99046757705765774624368661 4642816767457770685517281)
                    ·
                      refine ⟨3482112575593328014137961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642816767457770685517281 3482112575593328014137961)
                      ·
                        rfl

theorem cell23_6781390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_6781390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781390 prefixEnd_6781390 := by exact prefixLift 6781390
  have htrace : WordTrace (prefixWord ++ tailWord_6781390) baseStart_6781390 baseEnd_6781390 := by
    simpa [prefixWord, tailWord_6781390, baseEnd_6781390] using wordTrace_append hprefix tailTrace_6781390
  have hstable : (prefixWord ++ tailWord_6781390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781390).length < 2 ^ (prefixWord ++ tailWord_6781390).sum := by decide
  have hdescent : baseEnd_6781390 < baseStart_6781390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781494 : List Nat := [5, 1, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_6781494 : Nat := 118140960795 + 6781494 * 2 ^ 59
def prefixEnd_6781494 : Nat := 4983230072969 + 3 ^ 40 * 6781494 * 2
def baseEnd_6781494 : Nat := 1160721992527131869079161

theorem tailTrace_6781494 : CollatzResearch.WordTrace tailWord_6781494 prefixEnd_6781494 1160721992527131869079161 := by
  unfold tailWord_6781494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15458837880863306238270971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164894270729208599874890357 15458837880863306238270971)
  ·
    refine ⟨23188256821294959357406457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15458837880863306238270971 23188256821294959357406457)
    ·
      refine ⟨17391192615971219518054843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23188256821294959357406457 17391192615971219518054843)
      ·
        refine ⟨26086788923956829277082265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17391192615971219518054843 26086788923956829277082265)
        ·
          refine ⟨19565091692967621957811699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26086788923956829277082265 19565091692967621957811699)
          ·
            refine ⟨29347637539451432936717549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19565091692967621957811699 29347637539451432936717549)
            ·
              refine ⟨11005364077294287351269081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29347637539451432936717549 11005364077294287351269081)
              ·
                refine ⟨8254023057970715513451811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11005364077294287351269081 8254023057970715513451811)
                ·
                  refine ⟨12381034586956073270177717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8254023057970715513451811 12381034586956073270177717)
                  ·
                    refine ⟨1160721992527131869079161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12381034586956073270177717 1160721992527131869079161)
                    ·
                      rfl

theorem cell23_6781494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_6781494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781494 prefixEnd_6781494 := by exact prefixLift 6781494
  have htrace : WordTrace (prefixWord ++ tailWord_6781494) baseStart_6781494 baseEnd_6781494 := by
    simpa [prefixWord, tailWord_6781494, baseEnd_6781494] using wordTrace_append hprefix tailTrace_6781494
  have hstable : (prefixWord ++ tailWord_6781494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781494).length < 2 ^ (prefixWord ++ tailWord_6781494).sum := by decide
  have hdescent : baseEnd_6781494 < baseStart_6781494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781503 : List Nat := [1, 1, 2, 2, 3, 2, 1, 11]
def baseStart_6781503 : Nat := 118140960795 + 6781503 * 2 ^ 59
def prefixEnd_6781503 : Nat := 4983230072969 + 3 ^ 40 * 6781503 * 2
def baseEnd_6781503 : Nat := 128969281441010595260183

theorem tailTrace_6781503 : CollatzResearch.WordTrace tailWord_6781503 prefixEnd_6781503 128969281441010595260183 := by
  unfold tailWord_6781503
  simp only [CollatzResearch.WordTrace]
  refine ⟨247341734350780294349413163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164894489567186862899608775 247341734350780294349413163)
  ·
    refine ⟨371012601526170441524119745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247341734350780294349413163 371012601526170441524119745)
    ·
      refine ⟨278259451144627831143089809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371012601526170441524119745 278259451144627831143089809)
      ·
        refine ⟨208694588358470873357317357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278259451144627831143089809 208694588358470873357317357)
        ·
          refine ⟨78260470634426577508994009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208694588358470873357317357 78260470634426577508994009)
          ·
            refine ⟨58695352975819933131745507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78260470634426577508994009 58695352975819933131745507)
            ·
              refine ⟨88043029463729899697618261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58695352975819933131745507 88043029463729899697618261)
              ·
                refine ⟨128969281441010595260183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 88043029463729899697618261 128969281441010595260183)
                ·
                  rfl

theorem cell23_6781503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 11].length) (baseStart_6781503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781503 prefixEnd_6781503 := by exact prefixLift 6781503
  have htrace : WordTrace (prefixWord ++ tailWord_6781503) baseStart_6781503 baseEnd_6781503 := by
    simpa [prefixWord, tailWord_6781503, baseEnd_6781503] using wordTrace_append hprefix tailTrace_6781503
  have hstable : (prefixWord ++ tailWord_6781503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781503).length < 2 ^ (prefixWord ++ tailWord_6781503).sum := by decide
  have hdescent : baseEnd_6781503 < baseStart_6781503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781514 : List Nat := [3, 1, 2, 1, 1, 5, 3, 1, 1, 1, 4]
def baseStart_6781514 : Nat := 118140960795 + 6781514 * 2 ^ 59
def prefixEnd_6781514 : Nat := 4983230072969 + 3 ^ 40 * 6781514 * 2
def baseEnd_6781514 : Nat := 3482176247194485528987391

theorem tailTrace_6781514 : CollatzResearch.WordTrace tailWord_6781514 prefixEnd_6781514 3482176247194485528987391 := by
  unfold tailWord_6781514
  simp only [CollatzResearch.WordTrace]
  refine ⟨61835533888435110807015899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164894757035826962152042397 61835533888435110807015899)
  ·
    refine ⟨92753300832652666210523849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61835533888435110807015899 92753300832652666210523849)
    ·
      refine ⟨69564975624489499657892887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92753300832652666210523849 69564975624489499657892887)
      ·
        refine ⟨104347463436734249486839331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69564975624489499657892887 104347463436734249486839331)
        ·
          refine ⟨156521195155101374230258997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104347463436734249486839331 156521195155101374230258997)
          ·
            refine ⟨14673862045790753834086781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156521195155101374230258997 14673862045790753834086781)
            ·
              refine ⟨5502698267171532687782543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14673862045790753834086781 5502698267171532687782543)
              ·
                refine ⟨8254047400757299031673815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5502698267171532687782543 8254047400757299031673815)
                ·
                  refine ⟨12381071101135948547510723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8254047400757299031673815 12381071101135948547510723)
                  ·
                    refine ⟨18571606651703922821266085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12381071101135948547510723 18571606651703922821266085)
                    ·
                      refine ⟨3482176247194485528987391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18571606651703922821266085 3482176247194485528987391)
                      ·
                        rfl

theorem cell23_6781514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_6781514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781514 prefixEnd_6781514 := by exact prefixLift 6781514
  have htrace : WordTrace (prefixWord ++ tailWord_6781514) baseStart_6781514 baseEnd_6781514 := by
    simpa [prefixWord, tailWord_6781514, baseEnd_6781514] using wordTrace_append hprefix tailTrace_6781514
  have hstable : (prefixWord ++ tailWord_6781514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781514).length < 2 ^ (prefixWord ++ tailWord_6781514).sum := by decide
  have hdescent : baseEnd_6781514 < baseStart_6781514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781524 : List Nat := [2, 4, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_6781524 : Nat := 118140960795 + 6781524 * 2 ^ 59
def prefixEnd_6781524 : Nat := 4983230072969 + 3 ^ 40 * 6781524 * 2
def baseEnd_6781524 : Nat := 1160727127333676829954115

theorem tailTrace_6781524 : CollatzResearch.WordTrace tailWord_6781524 prefixEnd_6781524 1160727127333676829954115 := by
  unfold tailWord_6781524
  simp only [CollatzResearch.WordTrace]
  refine ⟨123671250141852107467963813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164895000189136143290618417 123671250141852107467963813)
  ·
    refine ⟨23188359401597270150243215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123671250141852107467963813 23188359401597270150243215)
    ·
      refine ⟨34782539102395905225364823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23188359401597270150243215 34782539102395905225364823)
      ·
        refine ⟨52173808653593857838047235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34782539102395905225364823 52173808653593857838047235)
        ·
          refine ⟨78260712980390786757070853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52173808653593857838047235 78260712980390786757070853)
          ·
            refine ⟨14673883683823272516950785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78260712980390786757070853 14673883683823272516950785)
            ·
              refine ⟨11005412762867454387713089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14673883683823272516950785 11005412762867454387713089)
              ·
                refine ⟨8254059572150590790784817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11005412762867454387713089 8254059572150590790784817)
                ·
                  refine ⟨6190544679112943093088613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8254059572150590790784817 6190544679112943093088613)
                  ·
                    refine ⟨1160727127333676829954115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6190544679112943093088613 1160727127333676829954115)
                    ·
                      rfl

theorem cell23_6781524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_6781524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781524 prefixEnd_6781524 := by exact prefixLift 6781524
  have htrace : WordTrace (prefixWord ++ tailWord_6781524) baseStart_6781524 baseEnd_6781524 := by
    simpa [prefixWord, tailWord_6781524, baseEnd_6781524] using wordTrace_append hprefix tailTrace_6781524
  have hstable : (prefixWord ++ tailWord_6781524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781524).length < 2 ^ (prefixWord ++ tailWord_6781524).sum := by decide
  have hdescent : baseEnd_6781524 < baseStart_6781524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781544 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_6781544 : Nat := 118140960795 + 6781544 * 2 ^ 59
def prefixEnd_6781544 : Nat := 4983230072969 + 3 ^ 40 * 6781544 * 2
def baseEnd_6781544 : Nat := 3482191651614120411612253

theorem tailTrace_6781544 : CollatzResearch.WordTrace tailWord_6781544 prefixEnd_6781544 3482191651614120411612253 := by
  unfold tailWord_6781544
  simp only [CollatzResearch.WordTrace]
  refine ⟨123671614871815879175827843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164895486495754505567770457 123671614871815879175827843)
  ·
    refine ⟨185507422307723818763741765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123671614871815879175827843 185507422307723818763741765)
    ·
      refine ⟨34782641682698216018201581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185507422307723818763741765 34782641682698216018201581)
      ·
        refine ⟨13043490631011831006825593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34782641682698216018201581 13043490631011831006825593)
        ·
          refine ⟨9782617973258873255119195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13043490631011831006825593 9782617973258873255119195)
          ·
            refine ⟨14673926959888309882678793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9782617973258873255119195 14673926959888309882678793)
            ·
              refine ⟨11005445219916232412009095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14673926959888309882678793 11005445219916232412009095)
              ·
                refine ⟨16508167829874348618013643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11005445219916232412009095 16508167829874348618013643)
                ·
                  refine ⟨24762251744811522927020465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16508167829874348618013643 24762251744811522927020465)
                  ·
                    refine ⟨18571688808608642195265349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24762251744811522927020465 18571688808608642195265349)
                    ·
                      refine ⟨3482191651614120411612253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18571688808608642195265349 3482191651614120411612253)
                      ·
                        rfl

theorem cell23_6781544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_6781544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781544 prefixEnd_6781544 := by exact prefixLift 6781544
  have htrace : WordTrace (prefixWord ++ tailWord_6781544) baseStart_6781544 baseEnd_6781544 := by
    simpa [prefixWord, tailWord_6781544, baseEnd_6781544] using wordTrace_append hprefix tailTrace_6781544
  have hstable : (prefixWord ++ tailWord_6781544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781544).length < 2 ^ (prefixWord ++ tailWord_6781544).sum := by decide
  have hdescent : baseEnd_6781544 < baseStart_6781544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781598 : List Nat := [4, 3, 1, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_6781598 : Nat := 118140960795 + 6781598 * 2 ^ 59
def prefixEnd_6781598 : Nat := 4983230072969 + 3 ^ 40 * 6781598 * 2
def baseEnd_6781598 : Nat := 3482219379569463200337005

theorem tailTrace_6781598 : CollatzResearch.WordTrace tailWord_6781598 prefixEnd_6781598 3482219379569463200337005 := by
  unfold tailWord_6781598
  simp only [CollatzResearch.WordTrace]
  refine ⟨30918149910679515696765181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164896799523624083716080965 30918149910679515696765181)
  ·
    refine ⟨11594306216504818386286943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30918149910679515696765181 11594306216504818386286943)
    ·
      refine ⟨17391459324757227579430415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11594306216504818386286943 17391459324757227579430415)
      ·
        refine ⟨26087188987135841369145623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17391459324757227579430415 26087188987135841369145623)
        ·
          refine ⟨39130783480703762053718435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26087188987135841369145623 39130783480703762053718435)
          ·
            refine ⟨58696175221055643080577653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39130783480703762053718435 58696175221055643080577653)
            ·
              refine ⟨5502766426973966538804155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58696175221055643080577653 5502766426973966538804155)
              ·
                refine ⟨8254149640460949808206233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5502766426973966538804155 8254149640460949808206233)
                ·
                  refine ⟨6190612230345712356154675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8254149640460949808206233 6190612230345712356154675)
                  ·
                    refine ⟨9285918345518568534232013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6190612230345712356154675 9285918345518568534232013)
                    ·
                      refine ⟨3482219379569463200337005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9285918345518568534232013 3482219379569463200337005)
                      ·
                        rfl

theorem cell23_6781598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_6781598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781598 prefixEnd_6781598 := by exact prefixLift 6781598
  have htrace : WordTrace (prefixWord ++ tailWord_6781598) baseStart_6781598 baseEnd_6781598 := by
    simpa [prefixWord, tailWord_6781598, baseEnd_6781598] using wordTrace_append hprefix tailTrace_6781598
  have hstable : (prefixWord ++ tailWord_6781598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781598).length < 2 ^ (prefixWord ++ tailWord_6781598).sum := by decide
  have hdescent : baseEnd_6781598 < baseStart_6781598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781621 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_6781621 : Nat := 118140960795 + 6781621 * 2 ^ 59
def prefixEnd_6781621 : Nat := 4983230072969 + 3 ^ 40 * 6781621 * 2
def baseEnd_6781621 : Nat := 3482231189624516610349399

theorem tailTrace_6781621 : CollatzResearch.WordTrace tailWord_6781621 prefixEnd_6781621 3482231189624516610349399 := by
  unfold tailWord_6781621
  simp only [CollatzResearch.WordTrace]
  refine ⟨247346038164352800502208717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164897358776235200334805811 247346038164352800502208717)
  ·
    refine ⟨92754764311632300188328269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247346038164352800502208717 92754764311632300188328269)
    ·
      refine ⟨34783036616862112570623101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92754764311632300188328269 34783036616862112570623101)
      ·
        refine ⟨13043638731323292213983663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34783036616862112570623101 13043638731323292213983663)
        ·
          refine ⟨19565458096984938320975495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13043638731323292213983663 19565458096984938320975495)
          ·
            refine ⟨29348187145477407481463243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19565458096984938320975495 29348187145477407481463243)
            ·
              refine ⟨44022280718216111222194865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29348187145477407481463243 44022280718216111222194865)
              ·
                refine ⟨33016710538662083416646149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44022280718216111222194865 33016710538662083416646149)
                ·
                  refine ⟨6190633225999140640621153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33016710538662083416646149 6190633225999140640621153)
                  ·
                    refine ⟨4642974919499355480465865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6190633225999140640621153 4642974919499355480465865)
                    ·
                      refine ⟨3482231189624516610349399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4642974919499355480465865 3482231189624516610349399)
                      ·
                        rfl

theorem cell23_6781621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_6781621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781621 prefixEnd_6781621 := by exact prefixLift 6781621
  have htrace : WordTrace (prefixWord ++ tailWord_6781621) baseStart_6781621 baseEnd_6781621 := by
    simpa [prefixWord, tailWord_6781621, baseEnd_6781621] using wordTrace_append hprefix tailTrace_6781621
  have hstable : (prefixWord ++ tailWord_6781621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781621).length < 2 ^ (prefixWord ++ tailWord_6781621).sum := by decide
  have hdescent : baseEnd_6781621 < baseStart_6781621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781644 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 7]
def baseStart_6781644 : Nat := 118140960795 + 6781644 * 2 ^ 59
def prefixEnd_6781644 : Nat := 4983230072969 + 3 ^ 40 * 6781644 * 2
def baseEnd_6781644 : Nat := 386915888853285557817977

theorem tailTrace_6781644 : CollatzResearch.WordTrace tailWord_6781644 prefixEnd_6781644 386915888853285557817977 := by
  unfold tailWord_6781644
  simp only [CollatzResearch.WordTrace]
  refine ⟨123673438521634737715147993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164897918028846316953530657 123673438521634737715147993)
  ·
    refine ⟨92755078891226053286360995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123673438521634737715147993 92755078891226053286360995)
    ·
      refine ⟨139132618336839079929541493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92755078891226053286360995 139132618336839079929541493)
      ·
        refine ⟨13043682969078663743394515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139132618336839079929541493 13043682969078663743394515)
        ·
          refine ⟨19565524453617995615091773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13043682969078663743394515 19565524453617995615091773)
          ·
            refine ⟨7337071670106748355659415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19565524453617995615091773 7337071670106748355659415)
            ·
              refine ⟨11005607505160122533489123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7337071670106748355659415 11005607505160122533489123)
              ·
                refine ⟨16508411257740183800233685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11005607505160122533489123 16508411257740183800233685)
                ·
                  refine ⟨386915888853285557817977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16508411257740183800233685 386915888853285557817977)
                  ·
                    rfl

theorem cell23_6781644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_6781644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781644 prefixEnd_6781644 := by exact prefixLift 6781644
  have htrace : WordTrace (prefixWord ++ tailWord_6781644) baseStart_6781644 baseEnd_6781644 := by
    simpa [prefixWord, tailWord_6781644, baseEnd_6781644] using wordTrace_append hprefix tailTrace_6781644
  have hstable : (prefixWord ++ tailWord_6781644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781644).length < 2 ^ (prefixWord ++ tailWord_6781644).sum := by decide
  have hdescent : baseEnd_6781644 < baseStart_6781644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781697 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_6781697 : Nat := 118140960795 + 6781697 * 2 ^ 59
def prefixEnd_6781697 : Nat := 4983230072969 + 3 ^ 40 * 6781697 * 2
def baseEnd_6781697 : Nat := 3482270214154258312999049

theorem tailTrace_6781697 : CollatzResearch.WordTrace tailWord_6781697 prefixEnd_6781697 3482270214154258312999049 := by
  unfold tailWord_6781697
  simp only [CollatzResearch.WordTrace]
  refine ⟨247348810112077465481975345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164899206741384976987983563 247348810112077465481975345)
  ·
    refine ⟨185511607584058099111481509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247348810112077465481975345 185511607584058099111481509)
    ·
      refine ⟨34783426422010893583402783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185511607584058099111481509 34783426422010893583402783)
      ·
        refine ⟨52175139633016340375104175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34783426422010893583402783 52175139633016340375104175)
        ·
          refine ⟨78262709449524510562656263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52175139633016340375104175 78262709449524510562656263)
          ·
            refine ⟨117394064174286765843984395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78262709449524510562656263 117394064174286765843984395)
            ·
              refine ⟨176091096261430148765976593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117394064174286765843984395 176091096261430148765976593)
              ·
                refine ⟨132068322196072611574482445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176091096261430148765976593 132068322196072611574482445)
                ·
                  refine ⟨49525620823527229340430917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132068322196072611574482445 49525620823527229340430917)
                  ·
                    refine ⟨9286053904411355501330797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49525620823527229340430917 9286053904411355501330797)
                    ·
                      refine ⟨3482270214154258312999049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9286053904411355501330797 3482270214154258312999049)
                      ·
                        rfl

theorem cell23_6781697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_6781697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781697 prefixEnd_6781697 := by exact prefixLift 6781697
  have htrace : WordTrace (prefixWord ++ tailWord_6781697) baseStart_6781697 baseEnd_6781697 := by
    simpa [prefixWord, tailWord_6781697, baseEnd_6781697] using wordTrace_append hprefix tailTrace_6781697
  have hstable : (prefixWord ++ tailWord_6781697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781697).length < 2 ^ (prefixWord ++ tailWord_6781697).sum := by decide
  have hdescent : baseEnd_6781697 < baseStart_6781697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781717 : List Nat := [1, 3, 2, 1, 2, 2, 1, 5, 6]
def baseStart_6781717 : Nat := 118140960795 + 6781717 * 2 ^ 59
def prefixEnd_6781717 : Nat := 4983230072969 + 3 ^ 40 * 6781717 * 2
def baseEnd_6781717 : Nat := 386920053751927581638773

theorem tailTrace_6781717 : CollatzResearch.WordTrace tailWord_6781717 prefixEnd_6781717 386920053751927581638773 := by
  unfold tailWord_6781717
  simp only [CollatzResearch.WordTrace]
  refine ⟨247349539572005008897703405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164899693048003339265135603 247349539572005008897703405)
  ·
    refine ⟨92756077339501878336638777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247349539572005008897703405 92756077339501878336638777)
    ·
      refine ⟨69567058004626408752479083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92756077339501878336638777 69567058004626408752479083)
      ·
        refine ⟨104350587006939613128718625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69567058004626408752479083 104350587006939613128718625)
        ·
          refine ⟨78262940255204709846538969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104350587006939613128718625 78262940255204709846538969)
          ·
            refine ⟨58697205191403532384904227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78262940255204709846538969 58697205191403532384904227)
            ·
              refine ⟨88045807787105298577356341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58697205191403532384904227 88045807787105298577356341)
              ·
                refine ⟨8254294480041121741627157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88045807787105298577356341 8254294480041121741627157)
                ·
                  refine ⟨386920053751927581638773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8254294480041121741627157 386920053751927581638773)
                  ·
                    rfl

theorem cell23_6781717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_6781717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781717 prefixEnd_6781717 := by exact prefixLift 6781717
  have htrace : WordTrace (prefixWord ++ tailWord_6781717) baseStart_6781717 baseEnd_6781717 := by
    simpa [prefixWord, tailWord_6781717, baseEnd_6781717] using wordTrace_append hprefix tailTrace_6781717
  have hstable : (prefixWord ++ tailWord_6781717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781717).length < 2 ^ (prefixWord ++ tailWord_6781717).sum := by decide
  have hdescent : baseEnd_6781717 < baseStart_6781717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781795 : List Nat := [1, 1, 1, 5, 3, 3, 1, 3, 1, 1, 3]
def baseStart_6781795 : Nat := 118140960795 + 6781795 * 2 ^ 59
def prefixEnd_6781795 : Nat := 4983230072969 + 3 ^ 40 * 6781795 * 2
def baseEnd_6781795 : Nat := 3482320535258398929573599

theorem tailTrace_6781795 : CollatzResearch.WordTrace tailWord_6781795 prefixEnd_6781795 3482320535258398929573599 := by
  unfold tailWord_6781795
  simp only [CollatzResearch.WordTrace]
  refine ⟨247352384465722428219042839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164901589643814952146028559 247352384465722428219042839)
  ·
    refine ⟨371028576698583642328564259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247352384465722428219042839 371028576698583642328564259)
    ·
      refine ⟨556542865047875463492846389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371028576698583642328564259 556542865047875463492846389)
      ·
        refine ⟨52175893598238324702454349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 556542865047875463492846389 52175893598238324702454349)
        ·
          refine ⟨19565960099339371763420381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52175893598238324702454349 19565960099339371763420381)
          ·
            refine ⟨7337235037252264411282643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19565960099339371763420381 7337235037252264411282643)
            ·
              refine ⟨11005852555878396616923965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7337235037252264411282643 11005852555878396616923965)
              ·
                refine ⟨4127194708454398731346487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11005852555878396616923965 4127194708454398731346487)
                ·
                  refine ⟨6190792062681598097019731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127194708454398731346487 6190792062681598097019731)
                  ·
                    refine ⟨9286188094022397145529597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6190792062681598097019731 9286188094022397145529597)
                    ·
                      refine ⟨3482320535258398929573599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9286188094022397145529597 3482320535258398929573599)
                      ·
                        rfl

theorem cell23_6781795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_6781795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781795 prefixEnd_6781795 := by exact prefixLift 6781795
  have htrace : WordTrace (prefixWord ++ tailWord_6781795) baseStart_6781795 baseEnd_6781795 := by
    simpa [prefixWord, tailWord_6781795, baseEnd_6781795] using wordTrace_append hprefix tailTrace_6781795
  have hstable : (prefixWord ++ tailWord_6781795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781795).length < 2 ^ (prefixWord ++ tailWord_6781795).sum := by decide
  have hdescent : baseEnd_6781795 < baseStart_6781795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781804 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 5]
def baseStart_6781804 : Nat := 118140960795 + 6781804 * 2 ^ 59
def prefixEnd_6781804 : Nat := 4983230072969 + 3 ^ 40 * 6781804 * 2
def baseEnd_6781804 : Nat := 3482325156584289394361057

theorem tailTrace_6781804 : CollatzResearch.WordTrace tailWord_6781804 prefixEnd_6781804 3482325156584289394361057 := by
  unfold tailWord_6781804
  simp only [CollatzResearch.WordTrace]
  refine ⟨123676356361344911378060233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164901808481793215170746977 123676356361344911378060233)
  ·
    refine ⟨92757267271008683533545175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123676356361344911378060233 92757267271008683533545175)
    ·
      refine ⟨139135900906513025300317763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92757267271008683533545175 139135900906513025300317763)
      ·
        refine ⟨208703851359769537950476645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139135900906513025300317763 208703851359769537950476645)
        ·
          refine ⟨39131972129956788365714371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208703851359769537950476645 39131972129956788365714371)
          ·
            refine ⟨58697958194935182548571557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39131972129956788365714371 58697958194935182548571557)
            ·
              refine ⟨11005867161550346727857167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58697958194935182548571557 11005867161550346727857167)
              ·
                refine ⟨16508800742325520091785751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11005867161550346727857167 16508800742325520091785751)
                ·
                  refine ⟨24763201113488280137678627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16508800742325520091785751 24763201113488280137678627)
                  ·
                    refine ⟨37144801670232420206517941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24763201113488280137678627 37144801670232420206517941)
                    ·
                      refine ⟨3482325156584289394361057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37144801670232420206517941 3482325156584289394361057)
                      ·
                        rfl

theorem cell23_6781804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_6781804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781804 prefixEnd_6781804 := by exact prefixLift 6781804
  have htrace : WordTrace (prefixWord ++ tailWord_6781804) baseStart_6781804 baseEnd_6781804 := by
    simpa [prefixWord, tailWord_6781804, baseEnd_6781804] using wordTrace_append hprefix tailTrace_6781804
  have hstable : (prefixWord ++ tailWord_6781804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781804).length < 2 ^ (prefixWord ++ tailWord_6781804).sum := by decide
  have hdescent : baseEnd_6781804 < baseStart_6781804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781827 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 6]
def baseStart_6781827 : Nat := 118140960795 + 6781827 * 2 ^ 59
def prefixEnd_6781827 : Nat := 4983230072969 + 3 ^ 40 * 6781827 * 2
def baseEnd_6781827 : Nat := 3482336966639342804373451

theorem tailTrace_6781827 : CollatzResearch.WordTrace tailWord_6781827 prefixEnd_6781827 3482336966639342804373451 := by
  unfold tailWord_6781827
  simp only [CollatzResearch.WordTrace]
  refine ⟨247353551601606497684207735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164902367734404331789471823 247353551601606497684207735)
  ·
    refine ⟨371030327402409746526311603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247353551601606497684207735 371030327402409746526311603)
    ·
      refine ⟨556545491103614619789467405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371030327402409746526311603 556545491103614619789467405)
      ·
        refine ⟨208704559163855482421050277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 556545491103614619789467405 208704559163855482421050277)
        ·
          refine ⟨39132104843222902953946927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208704559163855482421050277 39132104843222902953946927)
          ·
            refine ⟨58698157264834354430920391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39132104843222902953946927 58698157264834354430920391)
            ·
              refine ⟨88047235897251531646380587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58698157264834354430920391 88047235897251531646380587)
              ·
                refine ⟨132070853845877297469570881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88047235897251531646380587 132070853845877297469570881)
                ·
                  refine ⟨99053140384407973102178161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132070853845877297469570881 99053140384407973102178161)
                  ·
                    refine ⟨74289855288305979826633621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99053140384407973102178161 74289855288305979826633621)
                    ·
                      refine ⟨3482336966639342804373451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74289855288305979826633621 3482336966639342804373451)
                      ·
                        rfl

theorem cell23_6781827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_6781827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781827 prefixEnd_6781827 := by exact prefixLift 6781827
  have htrace : WordTrace (prefixWord ++ tailWord_6781827) baseStart_6781827 baseEnd_6781827 := by
    simpa [prefixWord, tailWord_6781827, baseEnd_6781827] using wordTrace_append hprefix tailTrace_6781827
  have hstable : (prefixWord ++ tailWord_6781827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781827).length < 2 ^ (prefixWord ++ tailWord_6781827).sum := by decide
  have hdescent : baseEnd_6781827 < baseStart_6781827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781867 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 4, 6]
def baseStart_6781867 : Nat := 118140960795 + 6781867 * 2 ^ 59
def prefixEnd_6781867 : Nat := 4983230072969 + 3 ^ 40 * 6781867 * 2
def baseEnd_6781867 : Nat := 1160785835288507549291089

theorem tailTrace_6781867 : CollatzResearch.WordTrace tailWord_6781867 prefixEnd_6781867 1160785835288507549291089 := by
  unfold tailWord_6781867
  simp only [CollatzResearch.WordTrace]
  refine ⟨247355010521461584515663855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164903340347641056343775903 247355010521461584515663855)
  ·
    refine ⟨371032515782192376773495783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247355010521461584515663855 371032515782192376773495783)
    ·
      refine ⟨556548773673288565160243675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371032515782192376773495783 556548773673288565160243675)
      ·
        refine ⟨834823160509932847740365513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556548773673288565160243675 834823160509932847740365513)
        ·
          refine ⟨626117370382449635805274135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 834823160509932847740365513 626117370382449635805274135)
          ·
            refine ⟨939176055573674453707911203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626117370382449635805274135 939176055573674453707911203)
            ·
              refine ⟨1408764083360511680561866805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939176055573674453707911203 1408764083360511680561866805)
              ·
                refine ⟨132071632815047970052675013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1408764083360511680561866805 132071632815047970052675013)
                ·
                  refine ⟨24763431152821494384876565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132071632815047970052675013 24763431152821494384876565)
                  ·
                    refine ⟨1160785835288507549291089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24763431152821494384876565 1160785835288507549291089)
                    ·
                      rfl

theorem cell23_6781867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 6].length) (baseStart_6781867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781867 prefixEnd_6781867 := by exact prefixLift 6781867
  have htrace : WordTrace (prefixWord ++ tailWord_6781867) baseStart_6781867 baseEnd_6781867 := by
    simpa [prefixWord, tailWord_6781867, baseEnd_6781867] using wordTrace_append hprefix tailTrace_6781867
  have hstable : (prefixWord ++ tailWord_6781867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781867).length < 2 ^ (prefixWord ++ tailWord_6781867).sum := by decide
  have hdescent : baseEnd_6781867 < baseStart_6781867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781869 : List Nat := [1, 5, 2, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_6781869 : Nat := 118140960795 + 6781869 * 2 ^ 59
def prefixEnd_6781869 : Nat := 4983230072969 + 3 ^ 40 * 6781869 * 2
def baseEnd_6781869 : Nat := 3482358532826831640048259

theorem tailTrace_6781869 : CollatzResearch.WordTrace tailWord_6781869 prefixEnd_6781869 3482358532826831640048259 := by
  unfold tailWord_6781869
  simp only [CollatzResearch.WordTrace]
  refine ⟨247355083467454338857236661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164903388978302892571491107 247355083467454338857236661)
  ·
    refine ⟨23189539075073844267865937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247355083467454338857236661 23189539075073844267865937)
    ·
      refine ⟨17392154306305383200899453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23189539075073844267865937 17392154306305383200899453)
      ·
        refine ⟨6522057864864518700337295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17392154306305383200899453 6522057864864518700337295)
        ·
          refine ⟨9783086797296778050505943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6522057864864518700337295 9783086797296778050505943)
          ·
            refine ⟨14674630195945167075758915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9783086797296778050505943 14674630195945167075758915)
            ·
              refine ⟨22011945293917750613638373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14674630195945167075758915 22011945293917750613638373)
              ·
                refine ⟨4127239742609578240057195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22011945293917750613638373 4127239742609578240057195)
                ·
                  refine ⟨6190859613914367360085793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127239742609578240057195 6190859613914367360085793)
                  ·
                    refine ⟨4643144710435775520064345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6190859613914367360085793 4643144710435775520064345)
                    ·
                      refine ⟨3482358532826831640048259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4643144710435775520064345 3482358532826831640048259)
                      ·
                        rfl

theorem cell23_6781869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_6781869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781869 prefixEnd_6781869 := by exact prefixLift 6781869
  have htrace : WordTrace (prefixWord ++ tailWord_6781869) baseStart_6781869 baseEnd_6781869 := by
    simpa [prefixWord, tailWord_6781869, baseEnd_6781869] using wordTrace_append hprefix tailTrace_6781869
  have hstable : (prefixWord ++ tailWord_6781869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781869).length < 2 ^ (prefixWord ++ tailWord_6781869).sum := by decide
  have hdescent : baseEnd_6781869 < baseStart_6781869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781908 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_6781908 : Nat := 118140960795 + 6781908 * 2 ^ 59
def prefixEnd_6781908 : Nat := 4983230072969 + 3 ^ 40 * 6781908 * 2
def baseEnd_6781908 : Nat := 3482378558572356987460579

theorem tailTrace_6781908 : CollatzResearch.WordTrace tailWord_6781908 prefixEnd_6781908 3482378558572356987460579 := by
  unfold tailWord_6781908
  simp only [CollatzResearch.WordTrace]
  refine ⟨123678252957156524258953189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164904337276208699011937585 123678252957156524258953189)
  ·
    refine ⟨23189672429466848298553723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123678252957156524258953189 23189672429466848298553723)
    ·
      refine ⟨34784508644200272447830585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23189672429466848298553723 34784508644200272447830585)
      ·
        refine ⟨26088381483150204335872939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34784508644200272447830585 26088381483150204335872939)
        ·
          refine ⟨39132572224725306503809409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26088381483150204335872939 39132572224725306503809409)
          ·
            refine ⟨29349429168543979877857057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39132572224725306503809409 29349429168543979877857057)
            ·
              refine ⟨22012071876407984908392793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29349429168543979877857057 22012071876407984908392793)
              ·
                refine ⟨16509053907305988681294595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22012071876407984908392793 16509053907305988681294595)
                ·
                  refine ⟨24763580860958983021941893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16509053907305988681294595 24763580860958983021941893)
                  ·
                    refine ⟨4643171411429809316614105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24763580860958983021941893 4643171411429809316614105)
                    ·
                      refine ⟨3482378558572356987460579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4643171411429809316614105 3482378558572356987460579)
                      ·
                        rfl

theorem cell23_6781908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_6781908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781908 prefixEnd_6781908 := by exact prefixLift 6781908
  have htrace : WordTrace (prefixWord ++ tailWord_6781908) baseStart_6781908 baseEnd_6781908 := by
    simpa [prefixWord, tailWord_6781908, baseEnd_6781908] using wordTrace_append hprefix tailTrace_6781908
  have hstable : (prefixWord ++ tailWord_6781908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781908).length < 2 ^ (prefixWord ++ tailWord_6781908).sum := by decide
  have hdescent : baseEnd_6781908 < baseStart_6781908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6781998 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_6781998 : Nat := 118140960795 + 6781998 * 2 ^ 59
def prefixEnd_6781998 : Nat := 4983230072969 + 3 ^ 40 * 6781998 * 2
def baseEnd_6781998 : Nat := 3482424771831261635335165

theorem tailTrace_6781998 : CollatzResearch.WordTrace tailWord_6781998 prefixEnd_6781998 3482424771831261635335165 := by
  unfold tailWord_6781998
  simp only [CollatzResearch.WordTrace]
  refine ⟨30919973560498374236085331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164906525655991329259121765 30919973560498374236085331)
  ·
    refine ⟨46379960340747561354127997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30919973560498374236085331 46379960340747561354127997)
    ·
      refine ⟨17392485127780335507797999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46379960340747561354127997 17392485127780335507797999)
      ·
        refine ⟨26088727691670503261696999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17392485127780335507797999 26088727691670503261696999)
        ·
          refine ⟨39133091537505754892545499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26088727691670503261696999 39133091537505754892545499)
          ·
            refine ⟨58699637306258632338818249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39133091537505754892545499 58699637306258632338818249)
            ·
              refine ⟨44024727979693974254113687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58699637306258632338818249 44024727979693974254113687)
              ·
                refine ⟨66037091969540961381170531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44024727979693974254113687 66037091969540961381170531)
                ·
                  refine ⟨99055637954311442071755797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66037091969540961381170531 99055637954311442071755797)
                  ·
                    refine ⟨4643233029108348847113553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99055637954311442071755797 4643233029108348847113553)
                    ·
                      refine ⟨3482424771831261635335165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4643233029108348847113553 3482424771831261635335165)
                      ·
                        rfl

theorem cell23_6781998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_6781998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6781998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6781998 prefixEnd_6781998 := by exact prefixLift 6781998
  have htrace : WordTrace (prefixWord ++ tailWord_6781998) baseStart_6781998 baseEnd_6781998 := by
    simpa [prefixWord, tailWord_6781998, baseEnd_6781998] using wordTrace_append hprefix tailTrace_6781998
  have hstable : (prefixWord ++ tailWord_6781998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6781998).length < 2 ^ (prefixWord ++ tailWord_6781998).sum := by decide
  have hdescent : baseEnd_6781998 < baseStart_6781998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6781998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782001 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 4, 2, 3]
def baseStart_6782001 : Nat := 118140960795 + 6782001 * 2 ^ 59
def prefixEnd_6782001 : Nat := 4983230072969 + 3 ^ 40 * 6782001 * 2
def baseEnd_6782001 : Nat := 3482426312273225123597651

theorem tailTrace_6782001 : CollatzResearch.WordTrace tailWord_6782001 prefixEnd_6782001 3482426312273225123597651 := by
  unfold tailWord_6782001
  simp only [CollatzResearch.WordTrace]
  refine ⟨247359897902976125401041857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164906598601984083600694571 247359897902976125401041857)
  ·
    refine ⟨185519923427232094050781393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247359897902976125401041857 185519923427232094050781393)
    ·
      refine ⟨139139942570424070538086045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185519923427232094050781393 139139942570424070538086045)
      ·
        refine ⟨52177478463909026451782267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139139942570424070538086045 52177478463909026451782267)
        ·
          refine ⟨78266217695863539677673401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52177478463909026451782267 78266217695863539677673401)
          ·
            refine ⟨58699663271897654758255051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78266217695863539677673401 58699663271897654758255051)
            ·
              refine ⟨88049494907846482137382577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58699663271897654758255051 88049494907846482137382577)
              ·
                refine ⟨66037121180884861603036933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88049494907846482137382577 66037121180884861603036933)
                ·
                  refine ⟨12381960221415911550569425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66037121180884861603036933 12381960221415911550569425)
                  ·
                    refine ⟨9286470166061933662927069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12381960221415911550569425 9286470166061933662927069)
                    ·
                      refine ⟨3482426312273225123597651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9286470166061933662927069 3482426312273225123597651)
                      ·
                        rfl

theorem cell23_6782001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_6782001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782001 prefixEnd_6782001 := by exact prefixLift 6782001
  have htrace : WordTrace (prefixWord ++ tailWord_6782001) baseStart_6782001 baseEnd_6782001 := by
    simpa [prefixWord, tailWord_6782001, baseEnd_6782001] using wordTrace_append hprefix tailTrace_6782001
  have hstable : (prefixWord ++ tailWord_6782001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782001).length < 2 ^ (prefixWord ++ tailWord_6782001).sum := by decide
  have hdescent : baseEnd_6782001 < baseStart_6782001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782048 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 3, 1, 3]
def baseStart_6782048 : Nat := 118140960795 + 6782048 * 2 ^ 59
def prefixEnd_6782048 : Nat := 4983230072969 + 3 ^ 40 * 6782048 * 2
def baseEnd_6782048 : Nat := 3482450445863986439709935

theorem tailTrace_6782048 : CollatzResearch.WordTrace tailWord_6782048 prefixEnd_6782048 3482450445863986439709935 := by
  unfold tailWord_6782048
  simp only [CollatzResearch.WordTrace]
  refine ⟨123680806066902926214001399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164907741422537234952001865 123680806066902926214001399)
  ·
    refine ⟨185521209100354389321002099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123680806066902926214001399 185521209100354389321002099)
    ·
      refine ⟨278281813650531583981503149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185521209100354389321002099 278281813650531583981503149)
      ·
        refine ⟨104355680118949343993063681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278281813650531583981503149 104355680118949343993063681)
        ·
          refine ⟨78266760089212007994797761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104355680118949343993063681 78266760089212007994797761)
          ·
            refine ⟨58700070066909005996098321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78266760089212007994797761 58700070066909005996098321)
            ·
              refine ⟨44025052550181754497073741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58700070066909005996098321 44025052550181754497073741)
              ·
                refine ⟨16509394706318157936402653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44025052550181754497073741 16509394706318157936402653)
                ·
                  refine ⟨6191023014869309226150995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16509394706318157936402653 6191023014869309226150995)
                  ·
                    refine ⟨9286534522303963839226493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6191023014869309226150995 9286534522303963839226493)
                    ·
                      refine ⟨3482450445863986439709935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9286534522303963839226493 3482450445863986439709935)
                      ·
                        rfl

theorem cell23_6782048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_6782048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782048 prefixEnd_6782048 := by exact prefixLift 6782048
  have htrace : WordTrace (prefixWord ++ tailWord_6782048) baseStart_6782048 baseEnd_6782048 := by
    simpa [prefixWord, tailWord_6782048, baseEnd_6782048] using wordTrace_append hprefix tailTrace_6782048
  have hstable : (prefixWord ++ tailWord_6782048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782048).length < 2 ^ (prefixWord ++ tailWord_6782048).sum := by decide
  have hdescent : baseEnd_6782048 < baseStart_6782048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782069 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6782069 : Nat := 118140960795 + 6782069 * 2 ^ 59
def prefixEnd_6782069 : Nat := 4983230072969 + 3 ^ 40 * 6782069 * 2
def baseEnd_6782069 : Nat := 3482461228957730857547339

theorem tailTrace_6782069 : CollatzResearch.WordTrace tailWord_6782069 prefixEnd_6782069 3482461228957730857547339 := by
  unfold tailWord_6782069
  simp only [CollatzResearch.WordTrace]
  refine ⟨247362378066729773014517261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164908252044486515343011507 247362378066729773014517261)
  ·
    refine ⟨92760891775023664880443973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247362378066729773014517261 92760891775023664880443973)
    ·
      refine ⟨17392667207816937165083245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92760891775023664880443973 17392667207816937165083245)
      ·
        refine ⟨6522250202931351436906217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17392667207816937165083245 6522250202931351436906217)
        ·
          refine ⟨4891687652198513577679663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6522250202931351436906217 4891687652198513577679663)
          ·
            refine ⟨7337531478297770366519495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4891687652198513577679663 7337531478297770366519495)
            ·
              refine ⟨11006297217446655549779243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7337531478297770366519495 11006297217446655549779243)
              ·
                refine ⟨16509445826169983324668865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11006297217446655549779243 16509445826169983324668865)
                ·
                  refine ⟨12382084369627487493501649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16509445826169983324668865 12382084369627487493501649)
                  ·
                    refine ⟨9286563277220615620126237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12382084369627487493501649 9286563277220615620126237)
                    ·
                      refine ⟨3482461228957730857547339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9286563277220615620126237 3482461228957730857547339)
                      ·
                        rfl

theorem cell23_6782069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6782069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782069 prefixEnd_6782069 := by exact prefixLift 6782069
  have htrace : WordTrace (prefixWord ++ tailWord_6782069) baseStart_6782069 baseEnd_6782069 := by
    simpa [prefixWord, tailWord_6782069, baseEnd_6782069] using wordTrace_append hprefix tailTrace_6782069
  have hstable : (prefixWord ++ tailWord_6782069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782069).length < 2 ^ (prefixWord ++ tailWord_6782069).sum := by decide
  have hdescent : baseEnd_6782069 < baseStart_6782069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782071 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_6782071 : Nat := 118140960795 + 6782071 * 2 ^ 59
def prefixEnd_6782071 : Nat := 4983230072969 + 3 ^ 40 * 6782071 * 2
def baseEnd_6782071 : Nat := 3482462255919039849722329

theorem tailTrace_6782071 : CollatzResearch.WordTrace tailWord_6782071 prefixEnd_6782071 3482462255919039849722329 := by
  unfold tailWord_6782071
  simp only [CollatzResearch.WordTrace]
  refine ⟨247362451012722527356090067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164908300675148351570726711 247362451012722527356090067)
  ·
    refine ⟨371043676519083791034135101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247362451012722527356090067 371043676519083791034135101)
    ·
      refine ⟨139141378694656421637800663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371043676519083791034135101 139141378694656421637800663)
      ·
        refine ⟨208712068041984632456700995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139141378694656421637800663 208712068041984632456700995)
        ·
          refine ⟨313068102062976948685051493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208712068041984632456700995 313068102062976948685051493)
          ·
            refine ⟨58700269136808177878447155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313068102062976948685051493 58700269136808177878447155)
            ·
              refine ⟨88050403705212266817670733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58700269136808177878447155 88050403705212266817670733)
              ·
                refine ⟨33018901389454600056626525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88050403705212266817670733 33018901389454600056626525)
                ·
                  refine ⟨12382088021045475021234947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33018901389454600056626525 12382088021045475021234947)
                  ·
                    refine ⟨18573132031568212531852421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12382088021045475021234947 18573132031568212531852421)
                    ·
                      refine ⟨3482462255919039849722329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18573132031568212531852421 3482462255919039849722329)
                      ·
                        rfl

theorem cell23_6782071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_6782071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782071 prefixEnd_6782071 := by exact prefixLift 6782071
  have htrace : WordTrace (prefixWord ++ tailWord_6782071) baseStart_6782071 baseEnd_6782071 := by
    simpa [prefixWord, tailWord_6782071, baseEnd_6782071] using wordTrace_append hprefix tailTrace_6782071
  have hstable : (prefixWord ++ tailWord_6782071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782071).length < 2 ^ (prefixWord ++ tailWord_6782071).sum := by decide
  have hdescent : baseEnd_6782071 < baseStart_6782071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782108 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_6782108 : Nat := 118140960795 + 6782108 * 2 ^ 59
def prefixEnd_6782108 : Nat := 4983230072969 + 3 ^ 40 * 6782108 * 2
def baseEnd_6782108 : Nat := 3482481254703256204959659

theorem tailTrace_6782108 : CollatzResearch.WordTrace tailWord_6782108 prefixEnd_6782108 3482481254703256204959659 := by
  unfold tailWord_6782108
  simp only [CollatzResearch.WordTrace]
  refine ⟨123681900256794241337593489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164909200342392321783457985 123681900256794241337593489)
  ·
    refine ⟨92761425192595681003195117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123681900256794241337593489 92761425192595681003195117)
    ·
      refine ⟨34785534447223380376198169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92761425192595681003195117 34785534447223380376198169)
      ·
        refine ⟨26089150835417535282148627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34785534447223380376198169 26089150835417535282148627)
        ·
          refine ⟨39133726253126302923222941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26089150835417535282148627 39133726253126302923222941)
          ·
            refine ⟨14675147344922363596208603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39133726253126302923222941 14675147344922363596208603)
            ·
              refine ⟨22012721017383545394312905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14675147344922363596208603 22012721017383545394312905)
              ·
                refine ⟨16509540763037659045734679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22012721017383545394312905 16509540763037659045734679)
                ·
                  refine ⟨24764311144556488568602019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16509540763037659045734679 24764311144556488568602019)
                  ·
                    refine ⟨37146466716834732852903029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24764311144556488568602019 37146466716834732852903029)
                    ·
                      refine ⟨3482481254703256204959659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37146466716834732852903029 3482481254703256204959659)
                      ·
                        rfl

theorem cell23_6782108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_6782108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782108 prefixEnd_6782108 := by exact prefixLift 6782108
  have htrace : WordTrace (prefixWord ++ tailWord_6782108) baseStart_6782108 baseEnd_6782108 := by
    simpa [prefixWord, tailWord_6782108, baseEnd_6782108] using wordTrace_append hprefix tailTrace_6782108
  have hstable : (prefixWord ++ tailWord_6782108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782108).length < 2 ^ (prefixWord ++ tailWord_6782108).sum := by decide
  have hdescent : baseEnd_6782108 < baseStart_6782108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782121 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 7, 3, 3]
def baseStart_6782121 : Nat := 118140960795 + 6782121 * 2 ^ 59
def prefixEnd_6782121 : Nat := 4983230072969 + 3 ^ 40 * 6782121 * 2
def baseEnd_6782121 : Nat := 3482487929951764654097099

theorem tailTrace_6782121 : CollatzResearch.WordTrace tailWord_6782121 prefixEnd_6782121 3482487929951764654097099 := by
  unfold tailWord_6782121
  simp only [CollatzResearch.WordTrace]
  refine ⟨247364274662541385895410217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164909516441694257263606811 247364274662541385895410217)
  ·
    refine ⟨185523205996906039421557663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247364274662541385895410217 185523205996906039421557663)
    ·
      refine ⟨278284808995359059132336495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185523205996906039421557663 278284808995359059132336495)
      ·
        refine ⟨417427213493038588698504743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278284808995359059132336495 417427213493038588698504743)
        ·
          refine ⟨626140820239557883047757115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417427213493038588698504743 626140820239557883047757115)
          ·
            refine ⟨939211230359336824571635673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626140820239557883047757115 939211230359336824571635673)
            ·
              refine ⟨704408422769502618428726755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939211230359336824571635673 704408422769502618428726755)
              ·
                refine ⟨1056612634154253927643090133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704408422769502618428726755 1056612634154253927643090133)
                ·
                  refine ⟨24764358612990326429134925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1056612634154253927643090133 24764358612990326429134925)
                  ·
                    refine ⟨9286634479871372410925597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24764358612990326429134925 9286634479871372410925597)
                    ·
                      refine ⟨3482487929951764654097099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9286634479871372410925597 3482487929951764654097099)
                      ·
                        rfl

theorem cell23_6782121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 3, 3].length) (baseStart_6782121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782121 prefixEnd_6782121 := by exact prefixLift 6782121
  have htrace : WordTrace (prefixWord ++ tailWord_6782121) baseStart_6782121 baseEnd_6782121 := by
    simpa [prefixWord, tailWord_6782121, baseEnd_6782121] using wordTrace_append hprefix tailTrace_6782121
  have hstable : (prefixWord ++ tailWord_6782121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782121).length < 2 ^ (prefixWord ++ tailWord_6782121).sum := by decide
  have hdescent : baseEnd_6782121 < baseStart_6782121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782122 : List Nat := [3, 1, 5, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_6782122 : Nat := 118140960795 + 6782122 * 2 ^ 59
def prefixEnd_6782122 : Nat := 4983230072969 + 3 ^ 40 * 6782122 * 2
def baseEnd_6782122 : Nat := 3482488443432419150184595

theorem tailTrace_6782122 : CollatzResearch.WordTrace tailWord_6782122 prefixEnd_6782122 3482488443432419150184595 := by
  unfold tailWord_6782122
  simp only [CollatzResearch.WordTrace]
  refine ⟨61841077783884440766549155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164909540757025175377464413 61841077783884440766549155)
  ·
    refine ⟨92761616675826661149823733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61841077783884440766549155 92761616675826661149823733)
    ·
      refine ⟨8696401563358749482795975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92761616675826661149823733 8696401563358749482795975)
      ·
        refine ⟨13044602345038124224193963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8696401563358749482795975 13044602345038124224193963)
        ·
          refine ⟨19566903517557186336290945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13044602345038124224193963 19566903517557186336290945)
          ·
            refine ⟨14675177638167889752218209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19566903517557186336290945 14675177638167889752218209)
            ·
              refine ⟨11006383228625917314163657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14675177638167889752218209 11006383228625917314163657)
              ·
                refine ⟨8254787421469437985622743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11006383228625917314163657 8254787421469437985622743)
                ·
                  refine ⟨12382181132204156978434115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8254787421469437985622743 12382181132204156978434115)
                  ·
                    refine ⟨18573271698306235467651173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12382181132204156978434115 18573271698306235467651173)
                    ·
                      refine ⟨3482488443432419150184595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18573271698306235467651173 3482488443432419150184595)
                      ·
                        rfl

theorem cell23_6782122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_6782122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782122 prefixEnd_6782122 := by exact prefixLift 6782122
  have htrace : WordTrace (prefixWord ++ tailWord_6782122) baseStart_6782122 baseEnd_6782122 := by
    simpa [prefixWord, tailWord_6782122, baseEnd_6782122] using wordTrace_append hprefix tailTrace_6782122
  have hstable : (prefixWord ++ tailWord_6782122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782122).length < 2 ^ (prefixWord ++ tailWord_6782122).sum := by decide
  have hdescent : baseEnd_6782122 < baseStart_6782122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782150 : List Nat := [6, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_6782150 : Nat := 118140960795 + 6782150 * 2 ^ 59
def prefixEnd_6782150 : Nat := 4983230072969 + 3 ^ 40 * 6782150 * 2
def baseEnd_6782150 : Nat := 3482502820890745040634467

theorem tailTrace_6782150 : CollatzResearch.WordTrace tailWord_6782150 prefixEnd_6782150 3482502820890745040634467 := by
  unfold tailWord_6782150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7730166636857385120256747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 164910221586290882565477269 7730166636857385120256747)
  ·
    refine ⟨11595249955286077680385121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7730166636857385120256747 11595249955286077680385121)
    ·
      refine ⟨8696437466464558260288841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11595249955286077680385121 8696437466464558260288841)
      ·
        refine ⟨6522328099848418695216631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8696437466464558260288841 6522328099848418695216631)
        ·
          refine ⟨9783492149772628042824947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6522328099848418695216631 9783492149772628042824947)
          ·
            refine ⟨14675238224658942064237421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9783492149772628042824947 14675238224658942064237421)
            ·
              refine ⟨5503214334247103274089033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14675238224658942064237421 5503214334247103274089033)
              ·
                refine ⟨4127410750685327455566775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5503214334247103274089033 4127410750685327455566775)
                ·
                  refine ⟨6191116126027991183350163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127410750685327455566775 6191116126027991183350163)
                  ·
                    refine ⟨9286674189041986775025245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6191116126027991183350163 9286674189041986775025245)
                    ·
                      refine ⟨3482502820890745040634467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9286674189041986775025245 3482502820890745040634467)
                      ·
                        rfl

theorem cell23_6782150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_6782150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782150 prefixEnd_6782150 := by exact prefixLift 6782150
  have htrace : WordTrace (prefixWord ++ tailWord_6782150) baseStart_6782150 baseEnd_6782150 := by
    simpa [prefixWord, tailWord_6782150, baseEnd_6782150] using wordTrace_append hprefix tailTrace_6782150
  have hstable : (prefixWord ++ tailWord_6782150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782150).length < 2 ^ (prefixWord ++ tailWord_6782150).sum := by decide
  have hdescent : baseEnd_6782150 < baseStart_6782150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782161 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_6782161 : Nat := 118140960795 + 6782161 * 2 ^ 59
def prefixEnd_6782161 : Nat := 4983230072969 + 3 ^ 40 * 6782161 * 2
def baseEnd_6782161 : Nat := 3482508469177944497596915

theorem tailTrace_6782161 : CollatzResearch.WordTrace tailWord_6782161 prefixEnd_6782161 3482508469177944497596915 := by
  unfold tailWord_6782161
  simp only [CollatzResearch.WordTrace]
  refine ⟨247365733582396472726866337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164910489054930981817910891 247365733582396472726866337)
  ·
    refine ⟨185524300186797354545149753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247365733582396472726866337 185524300186797354545149753)
    ·
      refine ⟨139143225140098015908862315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185524300186797354545149753 139143225140098015908862315)
      ·
        refine ⟨208714837710147023863293473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139143225140098015908862315 208714837710147023863293473)
        ·
          refine ⟨156536128282610267897470105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208714837710147023863293473 156536128282610267897470105)
          ·
            refine ⟨117402096211957700923102579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156536128282610267897470105 117402096211957700923102579)
            ·
              refine ⟨176103144317936551384653869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117402096211957700923102579 176103144317936551384653869)
              ·
                refine ⟨66038679119226206769245201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176103144317936551384653869 66038679119226206769245201)
                ·
                  refine ⟨49529009339419655076933901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66038679119226206769245201 49529009339419655076933901)
                  ·
                    refine ⟨18573378502282370653850213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49529009339419655076933901 18573378502282370653850213)
                    ·
                      refine ⟨3482508469177944497596915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18573378502282370653850213 3482508469177944497596915)
                      ·
                        rfl

theorem cell23_6782161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_6782161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782161 prefixEnd_6782161 := by exact prefixLift 6782161
  have htrace : WordTrace (prefixWord ++ tailWord_6782161) baseStart_6782161 baseEnd_6782161 := by
    simpa [prefixWord, tailWord_6782161, baseEnd_6782161] using wordTrace_append hprefix tailTrace_6782161
  have hstable : (prefixWord ++ tailWord_6782161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782161).length < 2 ^ (prefixWord ++ tailWord_6782161).sum := by decide
  have hdescent : baseEnd_6782161 < baseStart_6782161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782166 : List Nat := [5, 2, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_6782166 : Nat := 118140960795 + 6782166 * 2 ^ 59
def prefixEnd_6782166 : Nat := 4983230072969 + 3 ^ 40 * 6782166 * 2
def baseEnd_6782166 : Nat := 1160837012193738992678131

theorem tailTrace_6782166 : CollatzResearch.WordTrace tailWord_6782166 prefixEnd_6782166 1160837012193738992678131 := by
  unfold tailWord_6782166
  simp only [CollatzResearch.WordTrace]
  refine ⟨15460369746711147411299897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164910610631585572387198901 15460369746711147411299897)
  ·
    refine ⟨11595277310033360558474923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15460369746711147411299897 11595277310033360558474923)
    ·
      refine ⟨17392915965050040837712385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11595277310033360558474923 17392915965050040837712385)
      ·
        refine ⟨13044686973787530628284289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17392915965050040837712385 13044686973787530628284289)
        ·
          refine ⟨9783515230340647971213217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13044686973787530628284289 9783515230340647971213217)
          ·
            refine ⟨7337636422755485978409913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9783515230340647971213217 7337636422755485978409913)
            ·
              refine ⟨5503227317066614483807435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7337636422755485978409913 5503227317066614483807435)
              ·
                refine ⟨8254840975599921725711153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5503227317066614483807435 8254840975599921725711153)
                ·
                  refine ⟨6191130731699941294283365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8254840975599921725711153 6191130731699941294283365)
                  ·
                    refine ⟨1160837012193738992678131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6191130731699941294283365 1160837012193738992678131)
                    ·
                      rfl

theorem cell23_6782166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_6782166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782166 prefixEnd_6782166 := by exact prefixLift 6782166
  have htrace : WordTrace (prefixWord ++ tailWord_6782166) baseStart_6782166 baseEnd_6782166 := by
    simpa [prefixWord, tailWord_6782166, baseEnd_6782166] using wordTrace_append hprefix tailTrace_6782166
  have hstable : (prefixWord ++ tailWord_6782166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782166).length < 2 ^ (prefixWord ++ tailWord_6782166).sum := by decide
  have hdescent : baseEnd_6782166 < baseStart_6782166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782195 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 1, 4, 2]
def baseStart_6782195 : Nat := 118140960795 + 6782195 * 2 ^ 59
def prefixEnd_6782195 : Nat := 4983230072969 + 3 ^ 40 * 6782195 * 2
def baseEnd_6782195 : Nat := 3482525927520197364571759

theorem tailTrace_6782195 : CollatzResearch.WordTrace tailWord_6782195 prefixEnd_6782195 3482525927520197364571759 := by
  unfold tailWord_6782195
  simp only [CollatzResearch.WordTrace]
  refine ⟨247366973664273296533604039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164911315776182197689069359 247366973664273296533604039)
  ·
    refine ⟨371050460496409944800406059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247366973664273296533604039 371050460496409944800406059)
    ·
      refine ⟨556575690744614917200609089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371050460496409944800406059 556575690744614917200609089)
      ·
        refine ⟨417431768058461187900456817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556575690744614917200609089 417431768058461187900456817)
        ·
          refine ⟨313073826043845890925342613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417431768058461187900456817 313073826043845890925342613)
          ·
            refine ⟨14675335595805276137125435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 313073826043845890925342613 14675335595805276137125435)
            ·
              refine ⟨22013003393707914205688153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14675335595805276137125435 22013003393707914205688153)
              ·
                refine ⟨16509752545280935654266115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22013003393707914205688153 16509752545280935654266115)
                ·
                  refine ⟨24764628817921403481399173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16509752545280935654266115 24764628817921403481399173)
                  ·
                    refine ⟨4643367903360263152762345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24764628817921403481399173 4643367903360263152762345)
                    ·
                      refine ⟨3482525927520197364571759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4643367903360263152762345 3482525927520197364571759)
                      ·
                        rfl

theorem cell23_6782195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 4, 2].length) (baseStart_6782195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782195 prefixEnd_6782195 := by exact prefixLift 6782195
  have htrace : WordTrace (prefixWord ++ tailWord_6782195) baseStart_6782195 baseEnd_6782195 := by
    simpa [prefixWord, tailWord_6782195, baseEnd_6782195] using wordTrace_append hprefix tailTrace_6782195
  have hstable : (prefixWord ++ tailWord_6782195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782195).length < 2 ^ (prefixWord ++ tailWord_6782195).sum := by decide
  have hdescent : baseEnd_6782195 < baseStart_6782195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782288 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 3]
def baseStart_6782288 : Nat := 118140960795 + 6782288 * 2 ^ 59
def prefixEnd_6782288 : Nat := 4983230072969 + 3 ^ 40 * 6782288 * 2
def baseEnd_6782288 : Nat := 3482573681221065500708831

theorem tailTrace_6782288 : CollatzResearch.WordTrace tailWord_6782288 prefixEnd_6782288 3482573681221065500708831 := by
  unfold tailWord_6782288
  simp only [CollatzResearch.WordTrace]
  refine ⟨123685182826468186708369759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164913577101957582277826345 123685182826468186708369759)
  ·
    refine ⟨185527774239702280062554639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123685182826468186708369759 185527774239702280062554639)
    ·
      refine ⟨278291661359553420093831959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185527774239702280062554639 278291661359553420093831959)
      ·
        refine ⟨417437492039330130140747939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278291661359553420093831959 417437492039330130140747939)
        ·
          refine ⟨626156238058995195211121909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417437492039330130140747939 626156238058995195211121909)
          ·
            refine ⟨58702147318030799551042679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 626156238058995195211121909 58702147318030799551042679)
            ·
              refine ⟨88053220977046199326564019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58702147318030799551042679 88053220977046199326564019)
              ·
                refine ⟨132079831465569298989846029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88053220977046199326564019 132079831465569298989846029)
                ·
                  refine ⟨49529936799588487121192261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132079831465569298989846029 49529936799588487121192261)
                  ·
                    refine ⟨9286863149922841335223549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49529936799588487121192261 9286863149922841335223549)
                    ·
                      refine ⟨3482573681221065500708831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9286863149922841335223549 3482573681221065500708831)
                      ·
                        rfl

theorem cell23_6782288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 3].length) (baseStart_6782288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782288 prefixEnd_6782288 := by exact prefixLift 6782288
  have htrace : WordTrace (prefixWord ++ tailWord_6782288) baseStart_6782288 baseEnd_6782288 := by
    simpa [prefixWord, tailWord_6782288, baseEnd_6782288] using wordTrace_append hprefix tailTrace_6782288
  have hstable : (prefixWord ++ tailWord_6782288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782288).length < 2 ^ (prefixWord ++ tailWord_6782288).sum := by decide
  have hdescent : baseEnd_6782288 < baseStart_6782288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782295 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 3, 4]
def baseStart_6782295 : Nat := 118140960795 + 6782295 * 2 ^ 59
def prefixEnd_6782295 : Nat := 4983230072969 + 3 ^ 40 * 6782295 * 2
def baseEnd_6782295 : Nat := 1160859091861882324440433

theorem tailTrace_6782295 : CollatzResearch.WordTrace tailWord_6782295 prefixEnd_6782295 1160859091861882324440433 := by
  unfold tailWord_6782295
  simp only [CollatzResearch.WordTrace]
  refine ⟨247370620963911013612244339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164913747309274009074829559 247370620963911013612244339)
  ·
    refine ⟨371055931445866520418366509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247370620963911013612244339 371055931445866520418366509)
    ·
      refine ⟨139145974292199945156887441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371055931445866520418366509 139145974292199945156887441)
      ·
        refine ⟨104359480719149958867665581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139145974292199945156887441 104359480719149958867665581)
        ·
          refine ⟨39134805269681234575374593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104359480719149958867665581 39134805269681234575374593)
          ·
            refine ⟨29351103952260925931530945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39134805269681234575374593 29351103952260925931530945)
            ·
              refine ⟨22013327964195694448648209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29351103952260925931530945 22013327964195694448648209)
              ·
                refine ⟨16509995973146770836486157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22013327964195694448648209 16509995973146770836486157)
                ·
                  refine ⟨6191248489930039063682309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16509995973146770836486157 6191248489930039063682309)
                  ·
                    refine ⟨1160859091861882324440433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6191248489930039063682309 1160859091861882324440433)
                    ·
                      rfl

theorem cell23_6782295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_6782295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782295 prefixEnd_6782295 := by exact prefixLift 6782295
  have htrace : WordTrace (prefixWord ++ tailWord_6782295) baseStart_6782295 baseEnd_6782295 := by
    simpa [prefixWord, tailWord_6782295, baseEnd_6782295] using wordTrace_append hprefix tailTrace_6782295
  have hstable : (prefixWord ++ tailWord_6782295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782295).length < 2 ^ (prefixWord ++ tailWord_6782295).sum := by decide
  have hdescent : baseEnd_6782295 < baseStart_6782295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782308 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 8]
def baseStart_6782308 : Nat := 118140960795 + 6782308 * 2 ^ 59
def prefixEnd_6782308 : Nat := 4983230072969 + 3 ^ 40 * 6782308 * 2
def baseEnd_6782308 : Nat := 386953772314906158050971

theorem tailTrace_6782308 : CollatzResearch.WordTrace tailWord_6782308 prefixEnd_6782308 386953772314906158050971 := by
  unfold tailWord_6782308
  simp only [CollatzResearch.WordTrace]
  refine ⟨123685547556431958416233789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164914063408575944554978385 123685547556431958416233789)
  ·
    refine ⟨46382080333661984406087671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123685547556431958416233789 46382080333661984406087671)
    ·
      refine ⟨69573120500492976609131507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46382080333661984406087671 69573120500492976609131507)
      ·
        refine ⟨104359680750739464913697261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69573120500492976609131507 104359680750739464913697261)
        ·
          refine ⟨39134880281527299342636473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104359680750739464913697261 39134880281527299342636473)
          ·
            refine ⟨29351160211145474506977355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39134880281527299342636473 29351160211145474506977355)
            ·
              refine ⟨44026740316718211760466033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29351160211145474506977355 44026740316718211760466033)
              ·
                refine ⟨33020055237538658820349525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44026740316718211760466033 33020055237538658820349525)
                ·
                  refine ⟨386953772314906158050971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33020055237538658820349525 386953772314906158050971)
                  ·
                    rfl

theorem cell23_6782308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_6782308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782308 prefixEnd_6782308 := by exact prefixLift 6782308
  have htrace : WordTrace (prefixWord ++ tailWord_6782308) baseStart_6782308 baseEnd_6782308 := by
    simpa [prefixWord, tailWord_6782308, baseEnd_6782308] using wordTrace_append hprefix tailTrace_6782308
  have hstable : (prefixWord ++ tailWord_6782308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782308).length < 2 ^ (prefixWord ++ tailWord_6782308).sum := by decide
  have hdescent : baseEnd_6782308 < baseStart_6782308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782412 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 3, 2, 3]
def baseStart_6782412 : Nat := 118140960795 + 6782412 * 2 ^ 59
def prefixEnd_6782412 : Nat := 4983230072969 + 3 ^ 40 * 6782412 * 2
def baseEnd_6782412 : Nat := 3482637352822223015558261

theorem tailTrace_6782412 : CollatzResearch.WordTrace tailWord_6782412 prefixEnd_6782412 3482637352822223015558261 := by
  unfold tailWord_6782412
  simp only [CollatzResearch.WordTrace]
  refine ⟨123687444152243571297126745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164916592202991428396168993 123687444152243571297126745)
  ·
    refine ⟨92765583114182678472845059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123687444152243571297126745 92765583114182678472845059)
    ·
      refine ⟨139148374671274017709267589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92765583114182678472845059 139148374671274017709267589)
      ·
        refine ⟨26090320250863878320487673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139148374671274017709267589 26090320250863878320487673)
        ·
          refine ⟨19567740188147908740365755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26090320250863878320487673 19567740188147908740365755)
          ·
            refine ⟨29351610282221863110548633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19567740188147908740365755 29351610282221863110548633)
            ·
              refine ⟨22013707711666397332911475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29351610282221863110548633 22013707711666397332911475)
              ·
                refine ⟨33020561567499595999367213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22013707711666397332911475 33020561567499595999367213)
                ·
                  refine ⟨12382710587812348499762705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33020561567499595999367213 12382710587812348499762705)
                  ·
                    refine ⟨9287032940859261374822029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12382710587812348499762705 9287032940859261374822029)
                    ·
                      refine ⟨3482637352822223015558261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9287032940859261374822029 3482637352822223015558261)
                      ·
                        rfl

theorem cell23_6782412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_6782412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782412 prefixEnd_6782412 := by exact prefixLift 6782412
  have htrace : WordTrace (prefixWord ++ tailWord_6782412) baseStart_6782412 baseEnd_6782412 := by
    simpa [prefixWord, tailWord_6782412, baseEnd_6782412] using wordTrace_append hprefix tailTrace_6782412
  have hstable : (prefixWord ++ tailWord_6782412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782412).length < 2 ^ (prefixWord ++ tailWord_6782412).sum := by decide
  have hdescent : baseEnd_6782412 < baseStart_6782412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782426 : List Nat := [3, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2]
def baseStart_6782426 : Nat := 118140960795 + 6782426 * 2 ^ 59
def prefixEnd_6782426 : Nat := 4983230072969 + 3 ^ 40 * 6782426 * 2
def baseEnd_6782426 : Nat := 3482644541551385960783197

theorem tailTrace_6782426 : CollatzResearch.WordTrace tailWord_6782426 prefixEnd_6782426 3482644541551385960783197 := by
  unfold tailWord_6782426
  simp only [CollatzResearch.WordTrace]
  refine ⟨61843849731609105746315783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164916932617624281990175421 61843849731609105746315783)
  ·
    refine ⟨92765774597413658619473675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61843849731609105746315783 92765774597413658619473675)
    ·
      refine ⟨139148661896120487929210513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92765774597413658619473675 139148661896120487929210513)
      ·
        refine ⟨104361496422090365946907885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139148661896120487929210513 104361496422090365946907885)
        ·
          refine ⟨39135561158283887230090457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104361496422090365946907885 39135561158283887230090457)
          ·
            refine ⟨29351670868712915422567843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39135561158283887230090457 29351670868712915422567843)
            ·
              refine ⟨44027506303069373133851765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29351670868712915422567843 44027506303069373133851765)
              ·
                refine ⟨4127578715912753731298603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44027506303069373133851765 4127578715912753731298603)
                ·
                  refine ⟨6191368073869130596947905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127578715912753731298603 6191368073869130596947905)
                  ·
                    refine ⟨4643526055401847947710929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6191368073869130596947905 4643526055401847947710929)
                    ·
                      refine ⟨3482644541551385960783197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4643526055401847947710929 3482644541551385960783197)
                      ·
                        rfl

theorem cell23_6782426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_6782426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782426 prefixEnd_6782426 := by exact prefixLift 6782426
  have htrace : WordTrace (prefixWord ++ tailWord_6782426) baseStart_6782426 baseEnd_6782426 := by
    simpa [prefixWord, tailWord_6782426, baseEnd_6782426] using wordTrace_append hprefix tailTrace_6782426
  have hstable : (prefixWord ++ tailWord_6782426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782426).length < 2 ^ (prefixWord ++ tailWord_6782426).sum := by decide
  have hdescent : baseEnd_6782426 < baseStart_6782426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782429 : List Nat := [1, 4, 3, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_6782429 : Nat := 118140960795 + 6782429 * 2 ^ 59
def prefixEnd_6782429 : Nat := 4983230072969 + 3 ^ 40 * 6782429 * 2
def baseEnd_6782429 : Nat := 3482646081993349449045683

theorem tailTrace_6782429 : CollatzResearch.WordTrace tailWord_6782429 prefixEnd_6782429 3482646081993349449045683 := by
  unfold tailWord_6782429
  simp only [CollatzResearch.WordTrace]
  refine ⟨247375508345425554497622341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164917005563617036331748227 247375508345425554497622341)
  ·
    refine ⟨46382907814767291468304189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247375508345425554497622341 46382907814767291468304189)
    ·
      refine ⟨17393590430537734300614071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46382907814767291468304189 17393590430537734300614071)
      ·
        refine ⟨26090385645806601450921107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17393590430537734300614071 26090385645806601450921107)
        ·
          refine ⟨39135578468709902176381661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26090385645806601450921107 39135578468709902176381661)
          ·
            refine ⟨14675841925766213316143123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39135578468709902176381661 14675841925766213316143123)
            ·
              refine ⟨22013762888649319974214685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14675841925766213316143123 22013762888649319974214685)
              ·
                refine ⟨8255161083243494990330507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22013762888649319974214685 8255161083243494990330507)
                ·
                  refine ⟨12382741624865242485495761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8255161083243494990330507 12382741624865242485495761)
                  ·
                    refine ⟨9287056218648931864121821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12382741624865242485495761 9287056218648931864121821)
                    ·
                      refine ⟨3482646081993349449045683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9287056218648931864121821 3482646081993349449045683)
                      ·
                        rfl

theorem cell23_6782429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_6782429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782429 prefixEnd_6782429 := by exact prefixLift 6782429
  have htrace : WordTrace (prefixWord ++ tailWord_6782429) baseStart_6782429 baseEnd_6782429 := by
    simpa [prefixWord, tailWord_6782429, baseEnd_6782429] using wordTrace_append hprefix tailTrace_6782429
  have hstable : (prefixWord ++ tailWord_6782429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782429).length < 2 ^ (prefixWord ++ tailWord_6782429).sum := by decide
  have hdescent : baseEnd_6782429 < baseStart_6782429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782485 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_6782485 : Nat := 118140960795 + 6782485 * 2 ^ 59
def prefixEnd_6782485 : Nat := 4983230072969 + 3 ^ 40 * 6782485 * 2
def baseEnd_6782485 : Nat := 3482674836910001229945425

theorem tailTrace_6782485 : CollatzResearch.WordTrace tailWord_6782485 prefixEnd_6782485 3482674836910001229945425 := by
  unfold tailWord_6782485
  simp only [CollatzResearch.WordTrace]
  refine ⟨247377550833222676061660909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164918367222148450707773939 247377550833222676061660909)
  ·
    refine ⟨92766581562458503523122841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247377550833222676061660909 92766581562458503523122841)
    ·
      refine ⟨69574936171843877642342131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92766581562458503523122841 69574936171843877642342131)
      ·
        refine ⟨104362404257765816463513197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69574936171843877642342131 104362404257765816463513197)
        ·
          refine ⟨39135901596662181173817449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104362404257765816463513197 39135901596662181173817449)
          ·
            refine ⟨29351926197496635880363087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39135901596662181173817449 29351926197496635880363087)
            ·
              refine ⟨44027889296244953820544631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29351926197496635880363087 44027889296244953820544631)
              ·
                refine ⟨66041833944367430730816947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44027889296244953820544631 66041833944367430730816947)
                ·
                  refine ⟨99062750916551146096225421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66041833944367430730816947 99062750916551146096225421)
                  ·
                    refine ⟨37148531593706679786084533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99062750916551146096225421 37148531593706679786084533)
                    ·
                      refine ⟨3482674836910001229945425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37148531593706679786084533 3482674836910001229945425)
                      ·
                        rfl

theorem cell23_6782485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_6782485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782485 prefixEnd_6782485 := by exact prefixLift 6782485
  have htrace : WordTrace (prefixWord ++ tailWord_6782485) baseStart_6782485 baseEnd_6782485 := by
    simpa [prefixWord, tailWord_6782485, baseEnd_6782485] using wordTrace_append hprefix tailTrace_6782485
  have hstable : (prefixWord ++ tailWord_6782485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782485).length < 2 ^ (prefixWord ++ tailWord_6782485).sum := by decide
  have hdescent : baseEnd_6782485 < baseStart_6782485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782494 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6782494 : Nat := 118140960795 + 6782494 * 2 ^ 59
def prefixEnd_6782494 : Nat := 4983230072969 + 3 ^ 40 * 6782494 * 2
def baseEnd_6782494 : Nat := 3482679458235891694732885

theorem tailTrace_6782494 : CollatzResearch.WordTrace tailWord_6782494 prefixEnd_6782494 3482679458235891694732885 := by
  unfold tailWord_6782494
  simp only [CollatzResearch.WordTrace]
  refine ⟨30922234886273758824842317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164918586060126713732492357 30922234886273758824842317)
  ·
    refine ⟨11595838082352659559315869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30922234886273758824842317 11595838082352659559315869)
    ·
      refine ⟨4348439280882247334743451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11595838082352659559315869 4348439280882247334743451)
      ·
        refine ⟨6522658921323371002115177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4348439280882247334743451 6522658921323371002115177)
        ·
          refine ⟨4891994190992528251586383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6522658921323371002115177 4891994190992528251586383)
          ·
            refine ⟨7337991286488792377379575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4891994190992528251586383 7337991286488792377379575)
            ·
              refine ⟨11006986929733188566069363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7337991286488792377379575 11006986929733188566069363)
              ·
                refine ⟨16510480394599782849104045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11006986929733188566069363 16510480394599782849104045)
                ·
                  refine ⟨6191430147974918568414017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16510480394599782849104045 6191430147974918568414017)
                  ·
                    refine ⟨4643572610981188926310513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6191430147974918568414017 4643572610981188926310513)
                    ·
                      refine ⟨3482679458235891694732885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4643572610981188926310513 3482679458235891694732885)
                      ·
                        rfl

theorem cell23_6782494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6782494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782494 prefixEnd_6782494 := by exact prefixLift 6782494
  have htrace : WordTrace (prefixWord ++ tailWord_6782494) baseStart_6782494 baseEnd_6782494 := by
    simpa [prefixWord, tailWord_6782494, baseEnd_6782494] using wordTrace_append hprefix tailTrace_6782494
  have hstable : (prefixWord ++ tailWord_6782494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782494).length < 2 ^ (prefixWord ++ tailWord_6782494).sum := by decide
  have hdescent : baseEnd_6782494 < baseStart_6782494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782495 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 4]
def baseStart_6782495 : Nat := 118140960795 + 6782495 * 2 ^ 59
def prefixEnd_6782495 : Nat := 4983230072969 + 3 ^ 40 * 6782495 * 2
def baseEnd_6782495 : Nat := 3482679971716546190820379

theorem tailTrace_6782495 : CollatzResearch.WordTrace tailWord_6782495 prefixEnd_6782495 3482679971716546190820379 := by
  unfold tailWord_6782495
  simp only [CollatzResearch.WordTrace]
  refine ⟨247377915563186447769524939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164918610375457631846349959 247377915563186447769524939)
  ·
    refine ⟨371066873344779671654287409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247377915563186447769524939 371066873344779671654287409)
    ·
      refine ⟨278300155008584753740715557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371066873344779671654287409 278300155008584753740715557)
      ·
        refine ⟨52181279064109641326384167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278300155008584753740715557 52181279064109641326384167)
        ·
          refine ⟨78271918596164461989576251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52181279064109641326384167 78271918596164461989576251)
          ·
            refine ⟨117407877894246692984364377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78271918596164461989576251 117407877894246692984364377)
            ·
              refine ⟨88055908420685019738273283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117407877894246692984364377 88055908420685019738273283)
              ·
                refine ⟨132083862631027529607409925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88055908420685019738273283 132083862631027529607409925)
                ·
                  refine ⟨24765724243317661801389361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132083862631027529607409925 24765724243317661801389361)
                  ·
                    refine ⟨18574293182488246351042021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24765724243317661801389361 18574293182488246351042021)
                    ·
                      refine ⟨3482679971716546190820379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18574293182488246351042021 3482679971716546190820379)
                      ·
                        rfl

theorem cell23_6782495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_6782495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782495 prefixEnd_6782495 := by exact prefixLift 6782495
  have htrace : WordTrace (prefixWord ++ tailWord_6782495) baseStart_6782495 baseEnd_6782495 := by
    simpa [prefixWord, tailWord_6782495, baseEnd_6782495] using wordTrace_append hprefix tailTrace_6782495
  have hstable : (prefixWord ++ tailWord_6782495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782495).length < 2 ^ (prefixWord ++ tailWord_6782495).sum := by decide
  have hdescent : baseEnd_6782495 < baseStart_6782495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782545 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_6782545 : Nat := 118140960795 + 6782545 * 2 ^ 59
def prefixEnd_6782545 : Nat := 4983230072969 + 3 ^ 40 * 6782545 * 2
def baseEnd_6782545 : Nat := 3482705645749270995195149

theorem tailTrace_6782545 : CollatzResearch.WordTrace tailWord_6782545 prefixEnd_6782545 3482705645749270995195149 := by
  unfold tailWord_6782545
  simp only [CollatzResearch.WordTrace]
  refine ⟨247379739213005306308845089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164919826142003537539230059 247379739213005306308845089)
  ·
    refine ⟨185534804409753979731633817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247379739213005306308845089 185534804409753979731633817)
    ·
      refine ⟨139151103307315484798725363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185534804409753979731633817 139151103307315484798725363)
      ·
        refine ⟨208726654960973227198088045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139151103307315484798725363 208726654960973227198088045)
        ·
          refine ⟨78272495610364960199283017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208726654960973227198088045 78272495610364960199283017)
          ·
            refine ⟨58704371707773720149462263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78272495610364960199283017 58704371707773720149462263)
            ·
              refine ⟨88056557561660580224193395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58704371707773720149462263 88056557561660580224193395)
              ·
                refine ⟨132084836342490870336290093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88056557561660580224193395 132084836342490870336290093)
                ·
                  refine ⟨49531813628434076376108785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132084836342490870336290093 49531813628434076376108785)
                  ·
                    refine ⟨37148860221325557282081589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49531813628434076376108785 37148860221325557282081589)
                    ·
                      refine ⟨3482705645749270995195149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37148860221325557282081589 3482705645749270995195149)
                      ·
                        rfl

theorem cell23_6782545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_6782545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782545 prefixEnd_6782545 := by exact prefixLift 6782545
  have htrace : WordTrace (prefixWord ++ tailWord_6782545) baseStart_6782545 baseEnd_6782545 := by
    simpa [prefixWord, tailWord_6782545, baseEnd_6782545] using wordTrace_append hprefix tailTrace_6782545
  have hstable : (prefixWord ++ tailWord_6782545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782545).length < 2 ^ (prefixWord ++ tailWord_6782545).sum := by decide
  have hdescent : baseEnd_6782545 < baseStart_6782545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
