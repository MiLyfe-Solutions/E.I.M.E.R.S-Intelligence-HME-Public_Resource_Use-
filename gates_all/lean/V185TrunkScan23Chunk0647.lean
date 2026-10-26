import V185TrunkScan23Chunk0646

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3824947 : List Nat := [1, 1, 1, 2, 5, 3, 2, 3, 5]
def baseStart_3824947 : Nat := 118140960795 + 3824947 * 2 ^ 59
def prefixEnd_3824947 : Nat := 4983230072969 + 3 ^ 40 * 3824947 * 2
def baseEnd_3824947 : Nat := 218226254330327956774655

theorem tailTrace_3824947 : CollatzResearch.WordTrace tailWord_3824947 prefixEnd_3824947 218226254330327956774655 := by
  unfold tailWord_3824947
  simp only [CollatzResearch.WordTrace]
  refine ⟨139507278073877742784905095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93004852049251828523270063 139507278073877742784905095)
  ·
    refine ⟨209260917110816614177357643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139507278073877742784905095 209260917110816614177357643)
    ·
      refine ⟨313891375666224921266036465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209260917110816614177357643 313891375666224921266036465)
      ·
        refine ⟨235418531749668690949527349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313891375666224921266036465 235418531749668690949527349)
        ·
          refine ⟨22070487351531439776518189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235418531749668690949527349 22070487351531439776518189)
          ·
            refine ⟨8276432756824289916194321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22070487351531439776518189 8276432756824289916194321)
            ·
              refine ⟨6207324567618217437145741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8276432756824289916194321 6207324567618217437145741)
              ·
                refine ⟨2327746712856831538929653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6207324567618217437145741 2327746712856831538929653)
                ·
                  refine ⟨218226254330327956774655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2327746712856831538929653 218226254330327956774655)
                  ·
                    rfl

theorem cell23_3824947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 5].length) (baseStart_3824947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824947 prefixEnd_3824947 := by exact prefixLift 3824947
  have htrace : WordTrace (prefixWord ++ tailWord_3824947) baseStart_3824947 baseEnd_3824947 := by
    simpa [prefixWord, tailWord_3824947, baseEnd_3824947] using wordTrace_append hprefix tailTrace_3824947
  have hstable : (prefixWord ++ tailWord_3824947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824947).length < 2 ^ (prefixWord ++ tailWord_3824947).sum := by decide
  have hdescent : baseEnd_3824947 < baseStart_3824947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824964 : List Nat := [2, 3, 4, 1, 1, 1, 2, 4, 5]
def baseStart_3824964 : Nat := 118140960795 + 3824964 * 2 ^ 59
def prefixEnd_3824964 : Nat := 4983230072969 + 3 ^ 40 * 3824964 * 2
def baseEnd_3824964 : Nat := 218227224238230893828813

theorem tailTrace_3824964 : CollatzResearch.WordTrace tailWord_3824964 prefixEnd_3824964 218227224238230893828813 := by
  unfold tailWord_3824964
  simp only [CollatzResearch.WordTrace]
  refine ⟨69753949057408077344136973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93005265409877436458849297 69753949057408077344136973)
  ·
    refine ⟨26157730896528029004051365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69753949057408077344136973 26157730896528029004051365)
    ·
      refine ⟨4904574543099005438259631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26157730896528029004051365 4904574543099005438259631)
      ·
        refine ⟨7356861814648508157389447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4904574543099005438259631 7356861814648508157389447)
        ·
          refine ⟨11035292721972762236084171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7356861814648508157389447 11035292721972762236084171)
          ·
            refine ⟨16552939082959143354126257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11035292721972762236084171 16552939082959143354126257)
            ·
              refine ⟨12414704312219357515594693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16552939082959143354126257 12414704312219357515594693)
              ·
                refine ⟨2327757058541129534174005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12414704312219357515594693 2327757058541129534174005)
                ·
                  refine ⟨218227224238230893828813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2327757058541129534174005 218227224238230893828813)
                  ·
                    rfl

theorem cell23_3824964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_3824964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824964 prefixEnd_3824964 := by exact prefixLift 3824964
  have htrace : WordTrace (prefixWord ++ tailWord_3824964) baseStart_3824964 baseEnd_3824964 := by
    simpa [prefixWord, tailWord_3824964, baseEnd_3824964] using wordTrace_append hprefix tailTrace_3824964
  have hstable : (prefixWord ++ tailWord_3824964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824964).length < 2 ^ (prefixWord ++ tailWord_3824964).sum := by decide
  have hdescent : baseEnd_3824964 < baseStart_3824964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824980 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_3824980 : Nat := 118140960795 + 3824980 * 2 ^ 59
def prefixEnd_3824980 : Nat := 4983230072969 + 3 ^ 40 * 3824980 * 2
def baseEnd_3824980 : Nat := 1964053233834549981859243

theorem tailTrace_3824980 : CollatzResearch.WordTrace tailWord_3824980 prefixEnd_3824980 1964053233834549981859243 := by
  unfold tailWord_3824980
  simp only [CollatzResearch.WordTrace]
  refine ⟨69754240841379094710428197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93005654455172126280570929 69754240841379094710428197)
  ·
    refine ⟨13078920157758580258205287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69754240841379094710428197 13078920157758580258205287)
    ·
      refine ⟨19618380236637870387307931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13078920157758580258205287 19618380236637870387307931)
      ·
        refine ⟨29427570354956805580961897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19618380236637870387307931 29427570354956805580961897)
        ·
          refine ⟨22070677766217604185721423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29427570354956805580961897 22070677766217604185721423)
          ·
            refine ⟨33106016649326406278582135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22070677766217604185721423 33106016649326406278582135)
            ·
              refine ⟨49659024973989609417873203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33106016649326406278582135 49659024973989609417873203)
              ·
                refine ⟨74488537460984414126809805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49659024973989609417873203 74488537460984414126809805)
                ·
                  refine ⟨27933201547869155297553677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74488537460984414126809805 27933201547869155297553677)
                  ·
                    refine ⟨10474950580450933236582629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27933201547869155297553677 10474950580450933236582629)
                    ·
                      refine ⟨1964053233834549981859243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10474950580450933236582629 1964053233834549981859243)
                      ·
                        rfl

theorem cell23_3824980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_3824980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824980 prefixEnd_3824980 := by exact prefixLift 3824980
  have htrace : WordTrace (prefixWord ++ tailWord_3824980) baseStart_3824980 baseEnd_3824980 := by
    simpa [prefixWord, tailWord_3824980, baseEnd_3824980] using wordTrace_append hprefix tailTrace_3824980
  have hstable : (prefixWord ++ tailWord_3824980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824980).length < 2 ^ (prefixWord ++ tailWord_3824980).sum := by decide
  have hdescent : baseEnd_3824980 < baseStart_3824980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825020 : List Nat := [2, 2, 2, 1, 1, 1, 4, 4, 6]
def baseStart_3825020 : Nat := 118140960795 + 3825020 * 2 ^ 59
def prefixEnd_3825020 : Nat := 4983230072969 + 3 ^ 40 * 3825020 * 2
def baseEnd_3825020 : Nat := 218230419228969980595451

theorem tailTrace_3825020 : CollatzResearch.WordTrace tailWord_3825020 prefixEnd_3825020 218230419228969980595451 := by
  unfold tailWord_3825020
  simp only [CollatzResearch.WordTrace]
  refine ⟨69754970301306638126156257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93006627068408850834875009 69754970301306638126156257)
  ·
    refine ⟨52316227725979978594617193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69754970301306638126156257 52316227725979978594617193)
    ·
      refine ⟨39237170794484983945962895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52316227725979978594617193 39237170794484983945962895)
      ·
        refine ⟨58855756191727475918944343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39237170794484983945962895 58855756191727475918944343)
        ·
          refine ⟨88283634287591213878416515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58855756191727475918944343 88283634287591213878416515)
          ·
            refine ⟨132425451431386820817624773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88283634287591213878416515 132425451431386820817624773)
            ·
              refine ⟨24829772143385028903304645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132425451431386820817624773 24829772143385028903304645)
              ·
                refine ⟨4655582276884692919369621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24829772143385028903304645 4655582276884692919369621)
                ·
                  refine ⟨218230419228969980595451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4655582276884692919369621 218230419228969980595451)
                  ·
                    rfl

theorem cell23_3825020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_3825020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825020 prefixEnd_3825020 := by exact prefixLift 3825020
  have htrace : WordTrace (prefixWord ++ tailWord_3825020) baseStart_3825020 baseEnd_3825020 := by
    simpa [prefixWord, tailWord_3825020, baseEnd_3825020] using wordTrace_append hprefix tailTrace_3825020
  have hstable : (prefixWord ++ tailWord_3825020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825020).length < 2 ^ (prefixWord ++ tailWord_3825020).sum := by decide
  have hdescent : baseEnd_3825020 < baseStart_3825020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825047 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 5, 1, 3]
def baseStart_3825047 : Nat := 118140960795 + 3825047 * 2 ^ 59
def prefixEnd_3825047 : Nat := 4983230072969 + 3 ^ 40 * 3825047 * 2
def baseEnd_3825047 : Nat := 1964087637038401219721435

theorem tailTrace_3825047 : CollatzResearch.WordTrace tailWord_3825047 prefixEnd_3825047 1964087637038401219721435 := by
  unfold tailWord_3825047
  simp only [CollatzResearch.WordTrace]
  refine ⟨139510925373515459863545395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93007283582343639909030263 139510925373515459863545395)
  ·
    refine ⟨209266388060273189795318093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139510925373515459863545395 209266388060273189795318093)
    ·
      refine ⟨78474895522602446173244285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209266388060273189795318093 78474895522602446173244285)
      ·
        refine ⟨29428085820975917314966607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78474895522602446173244285 29428085820975917314966607)
        ·
          refine ⟨44142128731463875972449911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29428085820975917314966607 44142128731463875972449911)
          ·
            refine ⟨66213193097195813958674867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44142128731463875972449911 66213193097195813958674867)
            ·
              refine ⟨99319789645793720938012301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66213193097195813958674867 99319789645793720938012301)
              ·
                refine ⟨37244921117172645351754613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99319789645793720938012301 37244921117172645351754613)
                ·
                  refine ⟨3491711354734935501726995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37244921117172645351754613 3491711354734935501726995)
                  ·
                    refine ⟨5237567032102403252590493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3491711354734935501726995 5237567032102403252590493)
                    ·
                      refine ⟨1964087637038401219721435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5237567032102403252590493 1964087637038401219721435)
                      ·
                        rfl

theorem cell23_3825047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_3825047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825047 prefixEnd_3825047 := by exact prefixLift 3825047
  have htrace : WordTrace (prefixWord ++ tailWord_3825047) baseStart_3825047 baseEnd_3825047 := by
    simpa [prefixWord, tailWord_3825047, baseEnd_3825047] using wordTrace_append hprefix tailTrace_3825047
  have hstable : (prefixWord ++ tailWord_3825047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825047).length < 2 ^ (prefixWord ++ tailWord_3825047).sum := by decide
  have hdescent : baseEnd_3825047 < baseStart_3825047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825104 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 3, 2, 2]
def baseStart_3825104 : Nat := 118140960795 + 3825104 * 2 ^ 59
def prefixEnd_3825104 : Nat := 4983230072969 + 3 ^ 40 * 3825104 * 2
def baseEnd_3825104 : Nat := 1964116905435707496708673

theorem tailTrace_3825104 : CollatzResearch.WordTrace tailWord_3825104 prefixEnd_3825104 1964116905435707496708673 := by
  unfold tailWord_3825104
  simp only [CollatzResearch.WordTrace]
  refine ⟨69756502167154479299185183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93008669556205972398913577 69756502167154479299185183)
  ·
    refine ⟨104634753250731718948777775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69756502167154479299185183 104634753250731718948777775)
    ·
      refine ⟨156952129876097578423166663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104634753250731718948777775 156952129876097578423166663)
      ·
        refine ⟨235428194814146367634749995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156952129876097578423166663 235428194814146367634749995)
        ·
          refine ⟨353142292221219551452124993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235428194814146367634749995 353142292221219551452124993)
          ·
            refine ⟨264856719165914663589093745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353142292221219551452124993 264856719165914663589093745)
            ·
              refine ⟨198642539374435997691820309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264856719165914663589093745 198642539374435997691820309)
              ·
                refine ⟨9311369033176687391804077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 198642539374435997691820309 9311369033176687391804077)
                ·
                  refine ⟨3491763387441257771926529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9311369033176687391804077 3491763387441257771926529)
                  ·
                    refine ⟨2618822540580943328944897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3491763387441257771926529 2618822540580943328944897)
                    ·
                      refine ⟨1964116905435707496708673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618822540580943328944897 1964116905435707496708673)
                      ·
                        rfl

theorem cell23_3825104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 3, 2, 2].length) (baseStart_3825104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825104 prefixEnd_3825104 := by exact prefixLift 3825104
  have htrace : WordTrace (prefixWord ++ tailWord_3825104) baseStart_3825104 baseEnd_3825104 := by
    simpa [prefixWord, tailWord_3825104, baseEnd_3825104] using wordTrace_append hprefix tailTrace_3825104
  have hstable : (prefixWord ++ tailWord_3825104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825104).length < 2 ^ (prefixWord ++ tailWord_3825104).sum := by decide
  have hdescent : baseEnd_3825104 < baseStart_3825104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825108 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_3825108 : Nat := 118140960795 + 3825108 * 2 ^ 59
def prefixEnd_3825108 : Nat := 4983230072969 + 3 ^ 40 * 3825108 * 2
def baseEnd_3825108 : Nat := 1964118959358325481058655

theorem tailTrace_3825108 : CollatzResearch.WordTrace tailWord_3825108 prefixEnd_3825108 1964118959358325481058655 := by
  unfold tailWord_3825108
  simp only [CollatzResearch.WordTrace]
  refine ⟨69756575113147233640757989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93008766817529644854343985 69756575113147233640757989)
  ·
    refine ⟨13079357833715106307642123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69756575113147233640757989 13079357833715106307642123)
    ·
      refine ⟨19619036750572659461463185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13079357833715106307642123 19619036750572659461463185)
      ·
        refine ⟨14714277562929494596097389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19619036750572659461463185 14714277562929494596097389)
        ·
          refine ⟨5517854086098560473536521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14714277562929494596097389 5517854086098560473536521)
          ·
            refine ⟨4138390564573920355152391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5517854086098560473536521 4138390564573920355152391)
            ·
              refine ⟨6207585846860880532728587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138390564573920355152391 6207585846860880532728587)
              ·
                refine ⟨9311378770291320799092881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6207585846860880532728587 9311378770291320799092881)
                ·
                  refine ⟨6983534077718490599319661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9311378770291320799092881 6983534077718490599319661)
                  ·
                    refine ⟨2618825279144433974744873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6983534077718490599319661 2618825279144433974744873)
                    ·
                      refine ⟨1964118959358325481058655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618825279144433974744873 1964118959358325481058655)
                      ·
                        rfl

theorem cell23_3825108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_3825108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825108 prefixEnd_3825108 := by exact prefixLift 3825108
  have htrace : WordTrace (prefixWord ++ tailWord_3825108) baseStart_3825108 baseEnd_3825108 := by
    simpa [prefixWord, tailWord_3825108, baseEnd_3825108] using wordTrace_append hprefix tailTrace_3825108
  have hstable : (prefixWord ++ tailWord_3825108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825108).length < 2 ^ (prefixWord ++ tailWord_3825108).sum := by decide
  have hdescent : baseEnd_3825108 < baseStart_3825108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825121 : List Nat := [1, 2, 3, 1, 2, 5, 2, 1, 1, 1, 4]
def baseStart_3825121 : Nat := 118140960795 + 3825121 * 2 ^ 59
def prefixEnd_3825121 : Nat := 4983230072969 + 3 ^ 40 * 3825121 * 2
def baseEnd_3825121 : Nat := 1964125634606833930196095

theorem tailTrace_3825121 : CollatzResearch.WordTrace tailWord_3825121 prefixEnd_3825121 1964125634606833930196095 := by
  unfold tailWord_3825121
  simp only [CollatzResearch.WordTrace]
  refine ⟨139513624375247370501739217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93009082916831580334492811 139513624375247370501739217)
  ·
    refine ⟨104635218281435527876304413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139513624375247370501739217 104635218281435527876304413)
    ·
      refine ⟨39238206855538322953614155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104635218281435527876304413 39238206855538322953614155)
      ·
        refine ⟨58857310283307484430421233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39238206855538322953614155 58857310283307484430421233)
        ·
          refine ⟨44142982712480613322815925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58857310283307484430421233 44142982712480613322815925)
          ·
            refine ⟨4138404629295057499013993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44142982712480613322815925 4138404629295057499013993)
            ·
              refine ⟨3103803471971293124260495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4138404629295057499013993 3103803471971293124260495)
              ·
                refine ⟨4655705207956939686390743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103803471971293124260495 4655705207956939686390743)
                ·
                  refine ⟨6983557811935409529586115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655705207956939686390743 6983557811935409529586115)
                  ·
                    refine ⟨10475336717903114294379173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6983557811935409529586115 10475336717903114294379173)
                    ·
                      refine ⟨1964125634606833930196095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10475336717903114294379173 1964125634606833930196095)
                      ·
                        rfl

theorem cell23_3825121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_3825121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825121 prefixEnd_3825121 := by exact prefixLift 3825121
  have htrace : WordTrace (prefixWord ++ tailWord_3825121) baseStart_3825121 baseEnd_3825121 := by
    simpa [prefixWord, tailWord_3825121, baseEnd_3825121] using wordTrace_append hprefix tailTrace_3825121
  have hstable : (prefixWord ++ tailWord_3825121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825121).length < 2 ^ (prefixWord ++ tailWord_3825121).sum := by decide
  have hdescent : baseEnd_3825121 < baseStart_3825121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825138 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 3, 2, 2]
def baseStart_3825138 : Nat := 118140960795 + 3825138 * 2 ^ 59
def prefixEnd_3825138 : Nat := 4983230072969 + 3 ^ 40 * 3825138 * 2
def baseEnd_3825138 : Nat := 1964134363777960363683517

theorem tailTrace_3825138 : CollatzResearch.WordTrace tailWord_3825138 prefixEnd_3825138 1964134363777960363683517 := by
  unfold tailWord_3825138
  simp only [CollatzResearch.WordTrace]
  refine ⟨34878561104046445601277017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93009496277457188270072045 34878561104046445601277017)
  ·
    refine ⟨26158920828034834200957763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34878561104046445601277017 26158920828034834200957763)
    ·
      refine ⟨39238381242052251301436645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26158920828034834200957763 39238381242052251301436645)
      ·
        refine ⟨7357196482884797119019371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39238381242052251301436645 7357196482884797119019371)
        ·
          refine ⟨11035794724327195678529057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7357196482884797119019371 11035794724327195678529057)
          ·
            refine ⟨8276846043245396758896793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11035794724327195678529057 8276846043245396758896793)
            ·
              refine ⟨6207634532434047569172595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8276846043245396758896793 6207634532434047569172595)
              ·
                refine ⟨9311451798651071353758893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6207634532434047569172595 9311451798651071353758893)
                ·
                  refine ⟨3491794424494151757659585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9311451798651071353758893 3491794424494151757659585)
                  ·
                    refine ⟨2618845818370613818244689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3491794424494151757659585 2618845818370613818244689)
                    ·
                      refine ⟨1964134363777960363683517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618845818370613818244689 1964134363777960363683517)
                      ·
                        rfl

theorem cell23_3825138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_3825138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825138 prefixEnd_3825138 := by exact prefixLift 3825138
  have htrace : WordTrace (prefixWord ++ tailWord_3825138) baseStart_3825138 baseEnd_3825138 := by
    simpa [prefixWord, tailWord_3825138, baseEnd_3825138] using wordTrace_append hprefix tailTrace_3825138
  have hstable : (prefixWord ++ tailWord_3825138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825138).length < 2 ^ (prefixWord ++ tailWord_3825138).sum := by decide
  have hdescent : baseEnd_3825138 < baseStart_3825138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825181 : List Nat := [1, 4, 2, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_3825181 : Nat := 118140960795 + 3825181 * 2 ^ 59
def prefixEnd_3825181 : Nat := 4983230072969 + 3 ^ 40 * 3825181 * 2
def baseEnd_3825181 : Nat := 1964156443446103695445819

theorem tailTrace_3825181 : CollatzResearch.WordTrace tailWord_3825181 prefixEnd_3825181 1964156443446103695445819 := by
  unfold tailWord_3825181
  simp only [CollatzResearch.WordTrace]
  refine ⟨139515812755030000748923397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93010541836686667165948931 139515812755030000748923397)
  ·
    refine ⟨26159214891568125140423137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139515812755030000748923397 26159214891568125140423137)
    ·
      refine ⟨19619411168676093855317353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26159214891568125140423137 19619411168676093855317353)
      ·
        refine ⟨14714558376507070391488015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19619411168676093855317353 14714558376507070391488015)
        ·
          refine ⟨22071837564760605587232023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14714558376507070391488015 22071837564760605587232023)
          ·
            refine ⟨33107756347140908380848035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22071837564760605587232023 33107756347140908380848035)
            ·
              refine ⟨49661634520711362571272053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33107756347140908380848035 49661634520711362571272053)
              ·
                refine ⟨4655778236316690241056755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49661634520711362571272053 4655778236316690241056755)
                ·
                  refine ⟨6983667354475035361585133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655778236316690241056755 6983667354475035361585133)
                  ·
                    refine ⟨2618875257928138260594425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6983667354475035361585133 2618875257928138260594425)
                    ·
                      refine ⟨1964156443446103695445819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618875257928138260594425 1964156443446103695445819)
                      ·
                        rfl

theorem cell23_3825181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_3825181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825181 prefixEnd_3825181 := by exact prefixLift 3825181
  have htrace : WordTrace (prefixWord ++ tailWord_3825181) baseStart_3825181 baseEnd_3825181 := by
    simpa [prefixWord, tailWord_3825181, baseEnd_3825181] using wordTrace_append hprefix tailTrace_3825181
  have hstable : (prefixWord ++ tailWord_3825181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825181).length < 2 ^ (prefixWord ++ tailWord_3825181).sum := by decide
  have hdescent : baseEnd_3825181 < baseStart_3825181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825217 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 9]
def baseStart_3825217 : Nat := 118140960795 + 3825217 * 2 ^ 59
def prefixEnd_3825217 : Nat := 4983230072969 + 3 ^ 40 * 3825217 * 2
def baseEnd_3825217 : Nat := 218241658749962839399517

theorem tailTrace_3825217 : CollatzResearch.WordTrace tailWord_3825217 prefixEnd_3825217 218241658749962839399517 := by
  unfold tailWord_3825217
  simp only [CollatzResearch.WordTrace]
  refine ⟨139517125782899578897233905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93011417188599719264822603 139517125782899578897233905)
  ·
    refine ⟨104637844337174684172925429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139517125782899578897233905 104637844337174684172925429)
    ·
      refine ⟨9809797906610126641211759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104637844337174684172925429 9809797906610126641211759)
      ·
        refine ⟨14714696859915189961817639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9809797906610126641211759 14714696859915189961817639)
        ·
          refine ⟨22072045289872784942726459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14714696859915189961817639 22072045289872784942726459)
          ·
            refine ⟨33108067934809177414089689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22072045289872784942726459 33108067934809177414089689)
            ·
              refine ⟨24831050951106883060567267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33108067934809177414089689 24831050951106883060567267)
              ·
                refine ⟨37246576426660324590850901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24831050951106883060567267 37246576426660324590850901)
                ·
                  refine ⟨218241658749962839399517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37246576426660324590850901 218241658749962839399517)
                  ·
                    rfl

theorem cell23_3825217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 9].length) (baseStart_3825217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825217 prefixEnd_3825217 := by exact prefixLift 3825217
  have htrace : WordTrace (prefixWord ++ tailWord_3825217) baseStart_3825217 baseEnd_3825217 := by
    simpa [prefixWord, tailWord_3825217, baseEnd_3825217] using wordTrace_append hprefix tailTrace_3825217
  have hstable : (prefixWord ++ tailWord_3825217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825217).length < 2 ^ (prefixWord ++ tailWord_3825217).sum := by decide
  have hdescent : baseEnd_3825217 < baseStart_3825217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825227 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 3]
def baseStart_3825227 : Nat := 118140960795 + 3825227 * 2 ^ 59
def prefixEnd_3825227 : Nat := 4983230072969 + 3 ^ 40 * 3825227 * 2
def baseEnd_3825227 : Nat := 1964180063556210515470607

theorem tailTrace_3825227 : CollatzResearch.WordTrace tailWord_3825227 prefixEnd_3825227 1964180063556210515470607 := by
  unfold tailWord_3825227
  simp only [CollatzResearch.WordTrace]
  refine ⟨139517490512863350605097935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93011660341908900403398623 139517490512863350605097935)
  ·
    refine ⟨209276235769295025907646903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139517490512863350605097935 209276235769295025907646903)
    ·
      refine ⟨313914353653942538861470355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209276235769295025907646903 313914353653942538861470355)
      ·
        refine ⟨470871530480913808292205533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313914353653942538861470355 470871530480913808292205533)
        ·
          refine ⟨176576823930342678109577075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470871530480913808292205533 176576823930342678109577075)
          ·
            refine ⟨264865235895514017164365613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176576823930342678109577075 264865235895514017164365613)
            ·
              refine ⟨99324463460817756436637105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264865235895514017164365613 99324463460817756436637105)
              ·
                refine ⟨74493347595613317327477829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99324463460817756436637105 74493347595613317327477829)
                ·
                  refine ⟨13967502674177496998902093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74493347595613317327477829 13967502674177496998902093)
                  ·
                    refine ⟨5237813502816561374588285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13967502674177496998902093 5237813502816561374588285)
                    ·
                      refine ⟨1964180063556210515470607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5237813502816561374588285 1964180063556210515470607)
                      ·
                        rfl

theorem cell23_3825227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 3].length) (baseStart_3825227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825227 prefixEnd_3825227 := by exact prefixLift 3825227
  have htrace : WordTrace (prefixWord ++ tailWord_3825227) baseStart_3825227 baseEnd_3825227 := by
    simpa [prefixWord, tailWord_3825227, baseEnd_3825227] using wordTrace_append hprefix tailTrace_3825227
  have hstable : (prefixWord ++ tailWord_3825227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825227).length < 2 ^ (prefixWord ++ tailWord_3825227).sum := by decide
  have hdescent : baseEnd_3825227 < baseStart_3825227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825251 : List Nat := [1, 1, 1, 5, 1, 3, 4, 2, 5]
def baseStart_3825251 : Nat := 118140960795 + 3825251 * 2 ^ 59
def prefixEnd_3825251 : Nat := 4983230072969 + 3 ^ 40 * 3825251 * 2
def baseEnd_3825251 : Nat := 218243598565768713507833

theorem tailTrace_3825251 : CollatzResearch.WordTrace tailWord_3825251 prefixEnd_3825251 218243598565768713507833 := by
  unfold tailWord_3825251
  simp only [CollatzResearch.WordTrace]
  refine ⟨139518365864776402703971607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93012243909850935135981071 139518365864776402703971607)
  ·
    refine ⟨209277548797164604055957411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139518365864776402703971607 209277548797164604055957411)
    ·
      refine ⟨313916323195746906083936117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209277548797164604055957411 313916323195746906083936117)
      ·
        refine ⟨29429655299601272445369011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 313916323195746906083936117 29429655299601272445369011)
        ·
          refine ⟨44144482949401908668053517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29429655299601272445369011 44144482949401908668053517)
          ·
            refine ⟨16554181106025715750520069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44144482949401908668053517 16554181106025715750520069)
            ·
              refine ⟨3103908957379821703222513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16554181106025715750520069 3103908957379821703222513)
              ·
                refine ⟨2327931718034866277416885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3103908957379821703222513 2327931718034866277416885)
                ·
                  refine ⟨218243598565768713507833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2327931718034866277416885 218243598565768713507833)
                  ·
                    rfl

theorem cell23_3825251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 5].length) (baseStart_3825251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825251 prefixEnd_3825251 := by exact prefixLift 3825251
  have htrace : WordTrace (prefixWord ++ tailWord_3825251) baseStart_3825251 baseEnd_3825251 := by
    simpa [prefixWord, tailWord_3825251, baseEnd_3825251] using wordTrace_append hprefix tailTrace_3825251
  have hstable : (prefixWord ++ tailWord_3825251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825251).length < 2 ^ (prefixWord ++ tailWord_3825251).sum := by decide
  have hdescent : baseEnd_3825251 < baseStart_3825251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825257 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 5]
def baseStart_3825257 : Nat := 118140960795 + 3825257 * 2 ^ 59
def prefixEnd_3825257 : Nat := 4983230072969 + 3 ^ 40 * 3825257 * 2
def baseEnd_3825257 : Nat := 1964195467975845398095469

theorem tailTrace_3825257 : CollatzResearch.WordTrace tailWord_3825257 prefixEnd_3825257 1964195467975845398095469 := by
  unfold tailWord_3825257
  simp only [CollatzResearch.WordTrace]
  refine ⟨139518584702754665728690025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93012389801836443819126683 139518584702754665728690025)
  ·
    refine ⟨104638938527065999296517519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139518584702754665728690025 104638938527065999296517519)
    ·
      refine ⟨156958407790598998944776279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104638938527065999296517519 156958407790598998944776279)
      ·
        refine ⟨235437611685898498417164419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156958407790598998944776279 235437611685898498417164419)
        ·
          refine ⟨353156417528847747625746629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235437611685898498417164419 353156417528847747625746629)
          ·
            refine ⟨66216828286658952679827493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353156417528847747625746629 66216828286658952679827493)
            ·
              refine ⟨12415655303748553627467655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66216828286658952679827493 12415655303748553627467655)
              ·
                refine ⟨18623482955622830441201483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12415655303748553627467655 18623482955622830441201483)
                ·
                  refine ⟨27935224433434245661802225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18623482955622830441201483 27935224433434245661802225)
                  ·
                    refine ⟨20951418325075684246351669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27935224433434245661802225 20951418325075684246351669)
                    ·
                      refine ⟨1964195467975845398095469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20951418325075684246351669 1964195467975845398095469)
                      ·
                        rfl

theorem cell23_3825257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_3825257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825257 prefixEnd_3825257 := by exact prefixLift 3825257
  have htrace : WordTrace (prefixWord ++ tailWord_3825257) baseStart_3825257 baseEnd_3825257 := by
    simpa [prefixWord, tailWord_3825257, baseEnd_3825257] using wordTrace_append hprefix tailTrace_3825257
  have hstable : (prefixWord ++ tailWord_3825257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825257).length < 2 ^ (prefixWord ++ tailWord_3825257).sum := by decide
  have hdescent : baseEnd_3825257 < baseStart_3825257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825261 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_3825261 : Nat := 118140960795 + 3825261 * 2 ^ 59
def prefixEnd_3825261 : Nat := 4983230072969 + 3 ^ 40 * 3825261 * 2
def baseEnd_3825261 : Nat := 1964197521898463382445451

theorem tailTrace_3825261 : CollatzResearch.WordTrace tailWord_3825261 prefixEnd_3825261 1964197521898463382445451 := by
  unfold tailWord_3825261
  simp only [CollatzResearch.WordTrace]
  refine ⟨139518730594740174411835637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93012487063160116274557091 139518730594740174411835637)
  ·
    refine ⟨13079880993256891351109591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139518730594740174411835637 13079880993256891351109591)
    ·
      refine ⟨19619821489885337026664387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13079880993256891351109591 19619821489885337026664387)
      ·
        refine ⟨29429732234828005539996581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19619821489885337026664387 29429732234828005539996581)
        ·
          refine ⟨5518074794030251038749359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29429732234828005539996581 5518074794030251038749359)
          ·
            refine ⟨8277112191045376558124039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5518074794030251038749359 8277112191045376558124039)
            ·
              refine ⟨12415668286568064837186059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8277112191045376558124039 12415668286568064837186059)
              ·
                refine ⟨18623502429852097255779089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12415668286568064837186059 18623502429852097255779089)
                ·
                  refine ⟨13967626822389072941834317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18623502429852097255779089 13967626822389072941834317)
                  ·
                    refine ⟨5237860058395902353187869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13967626822389072941834317 5237860058395902353187869)
                    ·
                      refine ⟨1964197521898463382445451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5237860058395902353187869 1964197521898463382445451)
                      ·
                        rfl

theorem cell23_3825261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_3825261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825261 prefixEnd_3825261 := by exact prefixLift 3825261
  have htrace : WordTrace (prefixWord ++ tailWord_3825261) baseStart_3825261 baseEnd_3825261 := by
    simpa [prefixWord, tailWord_3825261, baseEnd_3825261] using wordTrace_append hprefix tailTrace_3825261
  have hstable : (prefixWord ++ tailWord_3825261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825261).length < 2 ^ (prefixWord ++ tailWord_3825261).sum := by decide
  have hdescent : baseEnd_3825261 < baseStart_3825261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825281 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3825281 : Nat := 118140960795 + 3825281 * 2 ^ 59
def prefixEnd_3825281 : Nat := 4983230072969 + 3 ^ 40 * 3825281 * 2
def baseEnd_3825281 : Nat := 654735930503851101398453

theorem tailTrace_3825281 : CollatzResearch.WordTrace tailWord_3825281 prefixEnd_3825281 654735930503851101398453 := by
  unfold tailWord_3825281
  simp only [CollatzResearch.WordTrace]
  refine ⟨139519460054667717827563697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93012973369778478551709131 139519460054667717827563697)
  ·
    refine ⟨104639595041000788370672773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139519460054667717827563697 104639595041000788370672773)
    ·
      refine ⟨19619924070187647819501145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104639595041000788370672773 19619924070187647819501145)
      ·
        refine ⟨14714943052640735864625859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19619924070187647819501145 14714943052640735864625859)
        ·
          refine ⟨22072414578961103796938789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14714943052640735864625859 22072414578961103796938789)
          ·
            refine ⟨4138577733555206961926023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22072414578961103796938789 4138577733555206961926023)
            ·
              refine ⟨6207866600332810442889035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138577733555206961926023 6207866600332810442889035)
              ·
                refine ⟨9311799900499215664333553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6207866600332810442889035 9311799900499215664333553)
                ·
                  refine ⟨6983849925374411748250165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9311799900499215664333553 6983849925374411748250165)
                  ·
                    refine ⟨654735930503851101398453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6983849925374411748250165 654735930503851101398453)
                    ·
                      rfl

theorem cell23_3825281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3825281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825281 prefixEnd_3825281 := by exact prefixLift 3825281
  have htrace : WordTrace (prefixWord ++ tailWord_3825281) baseStart_3825281 baseEnd_3825281 := by
    simpa [prefixWord, tailWord_3825281, baseEnd_3825281] using wordTrace_append hprefix tailTrace_3825281
  have hstable : (prefixWord ++ tailWord_3825281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825281).length < 2 ^ (prefixWord ++ tailWord_3825281).sum := by decide
  have hdescent : baseEnd_3825281 < baseStart_3825281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825327 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 6]
def baseStart_3825327 : Nat := 118140960795 + 3825327 * 2 ^ 59
def prefixEnd_3825327 : Nat := 4983230072969 + 3 ^ 40 * 3825327 * 2
def baseEnd_3825327 : Nat := 1964231411621660124220147

theorem tailTrace_3825327 : CollatzResearch.WordTrace tailWord_3825327 prefixEnd_3825327 1964231411621660124220147 := by
  unfold tailWord_3825327
  simp only [CollatzResearch.WordTrace]
  refine ⟨139521137812501067683738235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93014091875000711789158823 139521137812501067683738235)
  ·
    refine ⟨209281706718751601525607353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139521137812501067683738235 209281706718751601525607353)
    ·
      refine ⟨156961280039063701144205515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209281706718751601525607353 156961280039063701144205515)
      ·
        refine ⟨235441920058595551716308273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156961280039063701144205515 235441920058595551716308273)
        ·
          refine ⟨176581440043946663787231205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235441920058595551716308273 176581440043946663787231205)
          ·
            refine ⟨33109020008239999460105851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176581440043946663787231205 33109020008239999460105851)
            ·
              refine ⟨49663530012359999190158777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33109020008239999460105851 49663530012359999190158777)
              ·
                refine ⟨37247647509269999392619083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49663530012359999190158777 37247647509269999392619083)
                ·
                  refine ⟨55871471263904999088928625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37247647509269999392619083 55871471263904999088928625)
                  ·
                    refine ⟨41903603447928749316696469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55871471263904999088928625 41903603447928749316696469)
                    ·
                      refine ⟨1964231411621660124220147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41903603447928749316696469 1964231411621660124220147)
                      ·
                        rfl

theorem cell23_3825327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_3825327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825327 prefixEnd_3825327 := by exact prefixLift 3825327
  have htrace : WordTrace (prefixWord ++ tailWord_3825327) baseStart_3825327 baseEnd_3825327 := by
    simpa [prefixWord, tailWord_3825327, baseEnd_3825327] using wordTrace_append hprefix tailTrace_3825327
  have hstable : (prefixWord ++ tailWord_3825327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825327).length < 2 ^ (prefixWord ++ tailWord_3825327).sum := by decide
  have hdescent : baseEnd_3825327 < baseStart_3825327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825361 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 4, 3, 2]
def baseStart_3825361 : Nat := 118140960795 + 3825361 * 2 ^ 59
def prefixEnd_3825361 : Nat := 4983230072969 + 3 ^ 40 * 3825361 * 2
def baseEnd_3825361 : Nat := 1964248869963912991194991

theorem tailTrace_3825361 : CollatzResearch.WordTrace tailWord_3825361 prefixEnd_3825361 1964248869963912991194991 := by
  unfold tailWord_3825361
  simp only [CollatzResearch.WordTrace]
  refine ⟨139522377894377891490475937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93014918596251927660317291 139522377894377891490475937)
  ·
    refine ⟨104641783420783418617856953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139522377894377891490475937 104641783420783418617856953)
    ·
      refine ⟨78481337565587563963392715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104641783420783418617856953 78481337565587563963392715)
      ·
        refine ⟨117722006348381345945089073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78481337565587563963392715 117722006348381345945089073)
        ·
          refine ⟨88291504761286009458816805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117722006348381345945089073 88291504761286009458816805)
          ·
            refine ⟨16554657142741126773528151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88291504761286009458816805 16554657142741126773528151)
            ·
              refine ⟨24831985714111690160292227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16554657142741126773528151 24831985714111690160292227)
              ·
                refine ⟨37247978571167535240438341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24831985714111690160292227 37247978571167535240438341)
                ·
                  refine ⟨6983995982093912857582189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37247978571167535240438341 6983995982093912857582189)
                  ·
                    refine ⟨2618998493285217321593321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6983995982093912857582189 2618998493285217321593321)
                    ·
                      refine ⟨1964248869963912991194991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618998493285217321593321 1964248869963912991194991)
                      ·
                        rfl

theorem cell23_3825361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 3, 2].length) (baseStart_3825361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825361 prefixEnd_3825361 := by exact prefixLift 3825361
  have htrace : WordTrace (prefixWord ++ tailWord_3825361) baseStart_3825361 baseEnd_3825361 := by
    simpa [prefixWord, tailWord_3825361, baseEnd_3825361] using wordTrace_append hprefix tailTrace_3825361
  have hstable : (prefixWord ++ tailWord_3825361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825361).length < 2 ^ (prefixWord ++ tailWord_3825361).sum := by decide
  have hdescent : baseEnd_3825361 < baseStart_3825361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825411 : List Nat := [1, 1, 1, 3, 2, 2, 2, 5, 1, 2, 3]
def baseStart_3825411 : Nat := 118140960795 + 3825411 * 2 ^ 59
def prefixEnd_3825411 : Nat := 4983230072969 + 3 ^ 40 * 3825411 * 2
def baseEnd_3825411 : Nat := 1964274543996637795569761

theorem tailTrace_3825411 : CollatzResearch.WordTrace tailWord_3825411 prefixEnd_3825411 1964274543996637795569761 := by
  unfold tailWord_3825411
  simp only [CollatzResearch.WordTrace]
  refine ⟨139524201544196750029796087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93016134362797833353197391 139524201544196750029796087)
  ·
    refine ⟨209286302316295125044694131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139524201544196750029796087 209286302316295125044694131)
    ·
      refine ⟨313929453474442687567041197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209286302316295125044694131 313929453474442687567041197)
      ·
        refine ⟨117723545052916007837640449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313929453474442687567041197 117723545052916007837640449)
        ·
          refine ⟨88292658789687005878230337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117723545052916007837640449 88292658789687005878230337)
          ·
            refine ⟨66219494092265254408672753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88292658789687005878230337 66219494092265254408672753)
            ·
              refine ⟨49664620569198940806504565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66219494092265254408672753 49664620569198940806504565)
              ·
                refine ⟨4656058178362400700609803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49664620569198940806504565 4656058178362400700609803)
                ·
                  refine ⟨6984087267543601050914705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656058178362400700609803 6984087267543601050914705)
                  ·
                    refine ⟨5238065450657700788186029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6984087267543601050914705 5238065450657700788186029)
                    ·
                      refine ⟨1964274543996637795569761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5238065450657700788186029 1964274543996637795569761)
                      ·
                        rfl

theorem cell23_3825411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_3825411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825411 prefixEnd_3825411 := by exact prefixLift 3825411
  have htrace : WordTrace (prefixWord ++ tailWord_3825411) baseStart_3825411 baseEnd_3825411 := by
    simpa [prefixWord, tailWord_3825411, baseEnd_3825411] using wordTrace_append hprefix tailTrace_3825411
  have hstable : (prefixWord ++ tailWord_3825411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825411).length < 2 ^ (prefixWord ++ tailWord_3825411).sum := by decide
  have hdescent : baseEnd_3825411 < baseStart_3825411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825418 : List Nat := [3, 1, 2, 2, 1, 4, 2, 2, 2, 4]
def baseStart_3825418 : Nat := 118140960795 + 3825418 * 2 ^ 59
def prefixEnd_3825418 : Nat := 4983230072969 + 3 ^ 40 * 3825418 * 2
def baseEnd_3825418 : Nat := 654759379453739756060743

theorem tailTrace_3825418 : CollatzResearch.WordTrace tailWord_3825418 prefixEnd_3825418 654759379453739756060743 := by
  unfold tailWord_3825418
  simp only [CollatzResearch.WordTrace]
  refine ⟨34881114213792847556325227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93016304570114260150200605 34881114213792847556325227)
  ·
    refine ⟨52321671320689271334487841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34881114213792847556325227 52321671320689271334487841)
    ·
      refine ⟨39241253490516953500865881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52321671320689271334487841 39241253490516953500865881)
      ·
        refine ⟨29430940117887715125649411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39241253490516953500865881 29430940117887715125649411)
        ·
          refine ⟨44146410176831572688474117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29430940117887715125649411 44146410176831572688474117)
          ·
            refine ⟨8277451908155919879088897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44146410176831572688474117 8277451908155919879088897)
            ·
              refine ⟨6208088931116939909316673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8277451908155919879088897 6208088931116939909316673)
              ·
                refine ⟨4656066698337704931987505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6208088931116939909316673 4656066698337704931987505)
                ·
                  refine ⟨3492050023753278698990629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4656066698337704931987505 3492050023753278698990629)
                  ·
                    refine ⟨654759379453739756060743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3492050023753278698990629 654759379453739756060743)
                    ·
                      rfl

theorem cell23_3825418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_3825418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825418 prefixEnd_3825418 := by exact prefixLift 3825418
  have htrace : WordTrace (prefixWord ++ tailWord_3825418) baseStart_3825418 baseEnd_3825418 := by
    simpa [prefixWord, tailWord_3825418, baseEnd_3825418] using wordTrace_append hprefix tailTrace_3825418
  have hstable : (prefixWord ++ tailWord_3825418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825418).length < 2 ^ (prefixWord ++ tailWord_3825418).sum := by decide
  have hdescent : baseEnd_3825418 < baseStart_3825418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825431 : List Nat := [1, 1, 3, 4, 2, 3, 1, 8]
def baseStart_3825431 : Nat := 118140960795 + 3825431 * 2 ^ 59
def prefixEnd_3825431 : Nat := 4983230072969 + 3 ^ 40 * 3825431 * 2
def baseEnd_3825431 : Nat := 72751289392952878419247

theorem tailTrace_3825431 : CollatzResearch.WordTrace tailWord_3825431 prefixEnd_3825431 72751289392952878419247 := by
  unfold tailWord_3825431
  simp only [CollatzResearch.WordTrace]
  refine ⟨139524931004124293445524147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93016620669416195630349431 139524931004124293445524147)
  ·
    refine ⟨209287396506186440168286221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139524931004124293445524147 209287396506186440168286221)
    ·
      refine ⟨78482773689819915063107333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209287396506186440168286221 78482773689819915063107333)
      ·
        refine ⟨14715520066841234074332625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78482773689819915063107333 14715520066841234074332625)
        ·
          refine ⟨11036640050130925555749469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14715520066841234074332625 11036640050130925555749469)
          ·
            refine ⟨4138740018799097083406051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11036640050130925555749469 4138740018799097083406051)
            ·
              refine ⟨6208110028198645625109077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138740018799097083406051 6208110028198645625109077)
              ·
                refine ⟨72751289392952878419247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6208110028198645625109077 72751289392952878419247)
                ·
                  rfl

theorem cell23_3825431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 8].length) (baseStart_3825431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825431 prefixEnd_3825431 := by exact prefixLift 3825431
  have htrace : WordTrace (prefixWord ++ tailWord_3825431) baseStart_3825431 baseEnd_3825431 := by
    simpa [prefixWord, tailWord_3825431, baseEnd_3825431] using wordTrace_append hprefix tailTrace_3825431
  have hstable : (prefixWord ++ tailWord_3825431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825431).length < 2 ^ (prefixWord ++ tailWord_3825431).sum := by decide
  have hdescent : baseEnd_3825431 < baseStart_3825431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825441 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_3825441 : Nat := 118140960795 + 3825441 * 2 ^ 59
def prefixEnd_3825441 : Nat := 4983230072969 + 3 ^ 40 * 3825441 * 2
def baseEnd_3825441 : Nat := 1964289948416272678194623

theorem tailTrace_3825441 : CollatzResearch.WordTrace tailWord_3825441 prefixEnd_3825441 1964289948416272678194623 := by
  unfold tailWord_3825441
  simp only [CollatzResearch.WordTrace]
  refine ⟨139525295734088065153388177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93016863822725376768925451 139525295734088065153388177)
  ·
    refine ⟨104643971800566048865041133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139525295734088065153388177 104643971800566048865041133)
    ·
      refine ⟨39241489425212268324390425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104643971800566048865041133 39241489425212268324390425)
      ·
        refine ⟨29431117068909201243292819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39241489425212268324390425 29431117068909201243292819)
        ·
          refine ⟨44146675603363801864939229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29431117068909201243292819 44146675603363801864939229)
          ·
            refine ⟨16555003351261425699352211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44146675603363801864939229 16555003351261425699352211)
            ·
              refine ⟨24832505026892138549028317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16555003351261425699352211 24832505026892138549028317)
              ·
                refine ⟨9312189385084551955885619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24832505026892138549028317 9312189385084551955885619)
                ·
                  refine ⟨13968284077626827933828429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9312189385084551955885619 13968284077626827933828429)
                  ·
                    refine ⟨5238106529110060475185661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13968284077626827933828429 5238106529110060475185661)
                    ·
                      refine ⟨1964289948416272678194623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5238106529110060475185661 1964289948416272678194623)
                      ·
                        rfl

theorem cell23_3825441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_3825441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825441 prefixEnd_3825441 := by exact prefixLift 3825441
  have htrace : WordTrace (prefixWord ++ tailWord_3825441) baseStart_3825441 baseEnd_3825441 := by
    simpa [prefixWord, tailWord_3825441, baseEnd_3825441] using wordTrace_append hprefix tailTrace_3825441
  have hstable : (prefixWord ++ tailWord_3825441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825441).length < 2 ^ (prefixWord ++ tailWord_3825441).sum := by decide
  have hdescent : baseEnd_3825441 < baseStart_3825441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825451 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 7, 3, 2]
def baseStart_3825451 : Nat := 118140960795 + 3825451 * 2 ^ 59
def prefixEnd_3825451 : Nat := 4983230072969 + 3 ^ 40 * 3825451 * 2
def baseEnd_3825451 : Nat := 1964295083222817639069577

theorem tailTrace_3825451 : CollatzResearch.WordTrace tailWord_3825451 prefixEnd_3825451 1964295083222817639069577 := by
  unfold tailWord_3825451
  simp only [CollatzResearch.WordTrace]
  refine ⟨139525660464051836861252207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93017106976034557907501471 139525660464051836861252207)
  ·
    refine ⟨209288490696077755291878311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139525660464051836861252207 209288490696077755291878311)
    ·
      refine ⟨313932736044116632937817467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209288490696077755291878311 313932736044116632937817467)
      ·
        refine ⟨470899104066174949406726201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313932736044116632937817467 470899104066174949406726201)
        ·
          refine ⟨353174328049631212055044651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470899104066174949406726201 353174328049631212055044651)
          ·
            refine ⟨529761492074446818082566977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353174328049631212055044651 529761492074446818082566977)
            ·
              refine ⟨397321119055835113561925233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529761492074446818082566977 397321119055835113561925233)
              ·
                refine ⟨297990839291876335171443925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397321119055835113561925233 297990839291876335171443925)
                ·
                  refine ⟨6984160295903351605580717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 297990839291876335171443925 6984160295903351605580717)
                  ·
                    refine ⟨2619060110963756852092769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6984160295903351605580717 2619060110963756852092769)
                    ·
                      refine ⟨1964295083222817639069577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2619060110963756852092769 1964295083222817639069577)
                      ·
                        rfl

theorem cell23_3825451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 3, 2].length) (baseStart_3825451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825451 prefixEnd_3825451 := by exact prefixLift 3825451
  have htrace : WordTrace (prefixWord ++ tailWord_3825451) baseStart_3825451 baseEnd_3825451 := by
    simpa [prefixWord, tailWord_3825451, baseEnd_3825451] using wordTrace_append hprefix tailTrace_3825451
  have hstable : (prefixWord ++ tailWord_3825451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825451).length < 2 ^ (prefixWord ++ tailWord_3825451).sum := by decide
  have hdescent : baseEnd_3825451 < baseStart_3825451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825462 : List Nat := [5, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_3825462 : Nat := 118140960795 + 3825462 * 2 ^ 59
def prefixEnd_3825462 : Nat := 4983230072969 + 3 ^ 40 * 3825462 * 2
def baseEnd_3825462 : Nat := 1964300731510017096032027

theorem tailTrace_3825462 : CollatzResearch.WordTrace tailWord_3825462 prefixEnd_3825462 1964300731510017096032027 := by
  unfold tailWord_3825462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8720378854188249108743915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93017374444674657159935093 8720378854188249108743915)
  ·
    refine ⟨13080568281282373663115873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8720378854188249108743915 13080568281282373663115873)
    ·
      refine ⟨9810426210961780247336905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13080568281282373663115873 9810426210961780247336905)
      ·
        refine ⟨7357819658221335185502679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9810426210961780247336905 7357819658221335185502679)
        ·
          refine ⟨11036729487332002778254019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7357819658221335185502679 11036729487332002778254019)
          ·
            refine ⟨16555094230998004167381029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11036729487332002778254019 16555094230998004167381029)
            ·
              refine ⟨3104080168312125781383943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16555094230998004167381029 3104080168312125781383943)
              ·
                refine ⟨4656120252468188672075915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104080168312125781383943 4656120252468188672075915)
                ·
                  refine ⟨6984180378702283008113873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656120252468188672075915 6984180378702283008113873)
                  ·
                    refine ⟨5238135284026712256085405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6984180378702283008113873 5238135284026712256085405)
                    ·
                      refine ⟨1964300731510017096032027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5238135284026712256085405 1964300731510017096032027)
                      ·
                        rfl

theorem cell23_3825462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_3825462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825462 prefixEnd_3825462 := by exact prefixLift 3825462
  have htrace : WordTrace (prefixWord ++ tailWord_3825462) baseStart_3825462 baseEnd_3825462 := by
    simpa [prefixWord, tailWord_3825462, baseEnd_3825462] using wordTrace_append hprefix tailTrace_3825462
  have hstable : (prefixWord ++ tailWord_3825462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825462).length < 2 ^ (prefixWord ++ tailWord_3825462).sum := by decide
  have hdescent : baseEnd_3825462 < baseStart_3825462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825475 : List Nat := [1, 1, 1, 3, 1, 7, 1, 2, 2, 1, 3]
def baseStart_3825475 : Nat := 118140960795 + 3825475 * 2 ^ 59
def prefixEnd_3825475 : Nat := 4983230072969 + 3 ^ 40 * 3825475 * 2
def baseEnd_3825475 : Nat := 1964307406758525545169467

theorem tailTrace_3825475 : CollatzResearch.WordTrace tailWord_3825475 prefixEnd_3825475 1964307406758525545169467 := by
  unfold tailWord_3825475
  simp only [CollatzResearch.WordTrace]
  refine ⟨139526535815964888960125879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93017690543976592640083919 139526535815964888960125879)
  ·
    refine ⟨209289803723947333440188819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139526535815964888960125879 209289803723947333440188819)
    ·
      refine ⟨313934705585921000160283229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209289803723947333440188819 313934705585921000160283229)
      ·
        refine ⟨117725514594720375060106211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313934705585921000160283229 117725514594720375060106211)
        ·
          refine ⟨176588271892080562590159317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117725514594720375060106211 176588271892080562590159317)
          ·
            refine ⟨4138787622470638185706859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 176588271892080562590159317 4138787622470638185706859)
            ·
              refine ⟨6208181433705957278560289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138787622470638185706859 6208181433705957278560289)
              ·
                refine ⟨4656136075279467958920217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6208181433705957278560289 4656136075279467958920217)
                ·
                  refine ⟨3492102056459600969190163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4656136075279467958920217 3492102056459600969190163)
                  ·
                    refine ⟨5238153084689401453785245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3492102056459600969190163 5238153084689401453785245)
                    ·
                      refine ⟨1964307406758525545169467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5238153084689401453785245 1964307406758525545169467)
                      ·
                        rfl

theorem cell23_3825475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_3825475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825475 prefixEnd_3825475 := by exact prefixLift 3825475
  have htrace : WordTrace (prefixWord ++ tailWord_3825475) baseStart_3825475 baseEnd_3825475 := by
    simpa [prefixWord, tailWord_3825475, baseEnd_3825475] using wordTrace_append hprefix tailTrace_3825475
  have hstable : (prefixWord ++ tailWord_3825475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825475).length < 2 ^ (prefixWord ++ tailWord_3825475).sum := by decide
  have hdescent : baseEnd_3825475 < baseStart_3825475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825492 : List Nat := [2, 4, 1, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_3825492 : Nat := 118140960795 + 3825492 * 2 ^ 59
def prefixEnd_3825492 : Nat := 4983230072969 + 3 ^ 40 * 3825492 * 2
def baseEnd_3825492 : Nat := 1964316135929651978656889

theorem tailTrace_3825492 : CollatzResearch.WordTrace tailWord_3825492 prefixEnd_3825492 1964316135929651978656889 := by
  unfold tailWord_3825492
  simp only [CollatzResearch.WordTrace]
  refine ⟨69763577928451650431747365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93018103904602200575663153 69763577928451650431747365)
  ·
    refine ⟨13080670861584684455952631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69763577928451650431747365 13080670861584684455952631)
    ·
      refine ⟨19621006292377026683928947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13080670861584684455952631 19621006292377026683928947)
      ·
        refine ⟨29431509438565540025893421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19621006292377026683928947 29431509438565540025893421)
        ·
          refine ⟨11036816039462077509710033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29431509438565540025893421 11036816039462077509710033)
          ·
            refine ⟨8277612029596558132282525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11036816039462077509710033 8277612029596558132282525)
            ·
              refine ⟨3104104511098709299605947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8277612029596558132282525 3104104511098709299605947)
              ·
                refine ⟨4656156766648063949408921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104104511098709299605947 4656156766648063949408921)
                ·
                  refine ⟨3492117574986047962056691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4656156766648063949408921 3492117574986047962056691)
                  ·
                    refine ⟨5238176362479071943085037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3492117574986047962056691 5238176362479071943085037)
                    ·
                      refine ⟨1964316135929651978656889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5238176362479071943085037 1964316135929651978656889)
                      ·
                        rfl

theorem cell23_3825492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_3825492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825492 prefixEnd_3825492 := by exact prefixLift 3825492
  have htrace : WordTrace (prefixWord ++ tailWord_3825492) baseStart_3825492 baseEnd_3825492 := by
    simpa [prefixWord, tailWord_3825492, baseEnd_3825492] using wordTrace_append hprefix tailTrace_3825492
  have hstable : (prefixWord ++ tailWord_3825492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825492).length < 2 ^ (prefixWord ++ tailWord_3825492).sum := by decide
  have hdescent : baseEnd_3825492 < baseStart_3825492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825518 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3825518 : Nat := 118140960795 + 3825518 * 2 ^ 59
def prefixEnd_3825518 : Nat := 4983230072969 + 3 ^ 40 * 3825518 * 2
def baseEnd_3825518 : Nat := 1964329486426668876931769

theorem tailTrace_3825518 : CollatzResearch.WordTrace tailWord_3825518 prefixEnd_3825518 1964329486426668876931769 := by
  unfold tailWord_3825518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17441013019351138412992651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93018736103206071535960805 17441013019351138412992651)
  ·
    refine ⟨26161519529026707619488977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17441013019351138412992651 26161519529026707619488977)
    ·
      refine ⟨19621139646770030714616733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26161519529026707619488977 19621139646770030714616733)
      ·
        refine ⟨7357927367538761517981275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19621139646770030714616733 7357927367538761517981275)
        ·
          refine ⟨11036891051308142276971913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7357927367538761517981275 11036891051308142276971913)
          ·
            refine ⟨8277668288481106707728935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11036891051308142276971913 8277668288481106707728935)
            ·
              refine ⟨12416502432721660061593403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8277668288481106707728935 12416502432721660061593403)
              ·
                refine ⟨18624753649082490092390105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12416502432721660061593403 18624753649082490092390105)
                ·
                  refine ⟨13968565236811867569292579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18624753649082490092390105 13968565236811867569292579)
                  ·
                    refine ⟨20952847855217801353938869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13968565236811867569292579 20952847855217801353938869)
                    ·
                      refine ⟨1964329486426668876931769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20952847855217801353938869 1964329486426668876931769)
                      ·
                        rfl

theorem cell23_3825518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3825518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825518 prefixEnd_3825518 := by exact prefixLift 3825518
  have htrace : WordTrace (prefixWord ++ tailWord_3825518) baseStart_3825518 baseEnd_3825518 := by
    simpa [prefixWord, tailWord_3825518, baseEnd_3825518] using wordTrace_append hprefix tailTrace_3825518
  have hstable : (prefixWord ++ tailWord_3825518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825518).length < 2 ^ (prefixWord ++ tailWord_3825518).sum := by decide
  have hdescent : baseEnd_3825518 < baseStart_3825518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825591 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 3]
def baseStart_3825591 : Nat := 118140960795 + 3825591 * 2 ^ 59
def prefixEnd_3825591 : Nat := 4983230072969 + 3 ^ 40 * 3825591 * 2
def baseEnd_3825591 : Nat := 1964366970514447091318933

theorem tailTrace_3825591 : CollatzResearch.WordTrace tailWord_3825591 prefixEnd_3825591 1964366970514447091318933 := by
  unfold tailWord_3825591
  simp only [CollatzResearch.WordTrace]
  refine ⟨139530766683544640771348627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93020511122363093847565751 139530766683544640771348627)
  ·
    refine ⟨209296150025316961157022941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139530766683544640771348627 209296150025316961157022941)
    ·
      refine ⟨78486056259493860433883603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209296150025316961157022941 78486056259493860433883603)
      ·
        refine ⟨117729084389240790650825405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78486056259493860433883603 117729084389240790650825405)
        ·
          refine ⟨44148406645965296494059527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117729084389240790650825405 44148406645965296494059527)
          ·
            refine ⟨66222609968947944741089291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44148406645965296494059527 66222609968947944741089291)
            ·
              refine ⟨99333914953421917111633937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66222609968947944741089291 99333914953421917111633937)
              ·
                refine ⟨74500436215066437833725453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99333914953421917111633937 74500436215066437833725453)
                ·
                  refine ⟨27937663580649914187647045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74500436215066437833725453 27937663580649914187647045)
                  ·
                    refine ⟨5238311921371858910183821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27937663580649914187647045 5238311921371858910183821)
                    ·
                      refine ⟨1964366970514447091318933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5238311921371858910183821 1964366970514447091318933)
                      ·
                        rfl

theorem cell23_3825591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_3825591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825591 prefixEnd_3825591 := by exact prefixLift 3825591
  have htrace : WordTrace (prefixWord ++ tailWord_3825591) baseStart_3825591 baseEnd_3825591 := by
    simpa [prefixWord, tailWord_3825591, baseEnd_3825591] using wordTrace_append hprefix tailTrace_3825591
  have hstable : (prefixWord ++ tailWord_3825591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825591).length < 2 ^ (prefixWord ++ tailWord_3825591).sum := by decide
  have hdescent : baseEnd_3825591 < baseStart_3825591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825611 : List Nat := [1, 1, 1, 1, 3, 4, 1, 5, 6]
def baseStart_3825611 : Nat := 118140960795 + 3825611 * 2 ^ 59
def prefixEnd_3825611 : Nat := 4983230072969 + 3 ^ 40 * 3825611 * 2
def baseEnd_3825611 : Nat := 218264137791948557007649

theorem tailTrace_3825611 : CollatzResearch.WordTrace tailWord_3825611 prefixEnd_3825611 218264137791948557007649 := by
  unfold tailWord_3825611
  simp only [CollatzResearch.WordTrace]
  refine ⟨139531496143472184187076687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93020997428981456124717791 139531496143472184187076687)
  ·
    refine ⟨209297244215208276280615031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139531496143472184187076687 209297244215208276280615031)
    ·
      refine ⟨313945866322812414420922547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209297244215208276280615031 313945866322812414420922547)
      ·
        refine ⟨470918799484218621631383821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313945866322812414420922547 470918799484218621631383821)
        ·
          refine ⟨176594549806581983111768933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470918799484218621631383821 176594549806581983111768933)
          ·
            refine ⟨33111478088734121833456675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176594549806581983111768933 33111478088734121833456675)
            ·
              refine ⟨49667217133101182750185013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33111478088734121833456675 49667217133101182750185013)
              ·
                refine ⟨4656301606228235882829845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49667217133101182750185013 4656301606228235882829845)
                ·
                  refine ⟨218264137791948557007649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4656301606228235882829845 218264137791948557007649)
                  ·
                    rfl

theorem cell23_3825611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 6].length) (baseStart_3825611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825611 prefixEnd_3825611 := by exact prefixLift 3825611
  have htrace : WordTrace (prefixWord ++ tailWord_3825611) baseStart_3825611 baseEnd_3825611 := by
    simpa [prefixWord, tailWord_3825611, baseEnd_3825611] using wordTrace_append hprefix tailTrace_3825611
  have hstable : (prefixWord ++ tailWord_3825611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825611).length < 2 ^ (prefixWord ++ tailWord_3825611).sum := by decide
  have hdescent : baseEnd_3825611 < baseStart_3825611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825645 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 8]
def baseStart_3825645 : Nat := 118140960795 + 3825645 * 2 ^ 59
def prefixEnd_3825645 : Nat := 4983230072969 + 3 ^ 40 * 3825645 * 2
def baseEnd_3825645 : Nat := 218266077607754431115965

theorem tailTrace_3825645 : CollatzResearch.WordTrace tailWord_3825645 prefixEnd_3825645 218266077607754431115965 := by
  unfold tailWord_3825645
  simp only [CollatzResearch.WordTrace]
  refine ⟨139532736225349007993814389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93021824150232671995876259 139532736225349007993814389)
  ·
    refine ⟨13081194021126469499420099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139532736225349007993814389 13081194021126469499420099)
    ·
      refine ⟨19621791031689704249130149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13081194021126469499420099 19621791031689704249130149)
      ·
        refine ⟨3679085818441819546711903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19621791031689704249130149 3679085818441819546711903)
        ·
          refine ⟨5518628727662729320067855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679085818441819546711903 5518628727662729320067855)
          ·
            refine ⟨8277943091494093980101783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5518628727662729320067855 8277943091494093980101783)
            ·
              refine ⟨12416914637241140970152675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8277943091494093980101783 12416914637241140970152675)
              ·
                refine ⟨18625371955861711455229013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12416914637241140970152675 18625371955861711455229013)
                ·
                  refine ⟨218266077607754431115965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18625371955861711455229013 218266077607754431115965)
                  ·
                    rfl

theorem cell23_3825645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_3825645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825645 prefixEnd_3825645 := by exact prefixLift 3825645
  have htrace : WordTrace (prefixWord ++ tailWord_3825645) baseStart_3825645 baseEnd_3825645 := by
    simpa [prefixWord, tailWord_3825645, baseEnd_3825645] using wordTrace_append hprefix tailTrace_3825645
  have hstable : (prefixWord ++ tailWord_3825645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825645).length < 2 ^ (prefixWord ++ tailWord_3825645).sum := by decide
  have hdescent : baseEnd_3825645 < baseStart_3825645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825662 : List Nat := [4, 2, 2, 2, 1, 2, 3, 1, 6]
def baseStart_3825662 : Nat := 118140960795 + 3825662 * 2 ^ 59
def prefixEnd_3825662 : Nat := 4983230072969 + 3 ^ 40 * 3825662 * 2
def baseEnd_3825662 : Nat := 218267047515657368170123

theorem tailTrace_3825662 : CollatzResearch.WordTrace tailWord_3825662 prefixEnd_3825662 218267047515657368170123 := by
  unfold tailWord_3825662
  simp only [CollatzResearch.WordTrace]
  refine ⟨17441669533285927487147905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93022237510858279931455493 17441669533285927487147905)
  ·
    refine ⟨13081252149964445615360929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17441669533285927487147905 13081252149964445615360929)
    ·
      refine ⟨9810939112473334211520697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13081252149964445615360929 9810939112473334211520697)
      ·
        refine ⟨7358204334355000658640523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9810939112473334211520697 7358204334355000658640523)
        ·
          refine ⟨11037306501532500987960785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7358204334355000658640523 11037306501532500987960785)
          ·
            refine ⟨8277979876149375740970589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11037306501532500987960785 8277979876149375740970589)
            ·
              refine ⟨3104242453556015902863971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8277979876149375740970589 3104242453556015902863971)
              ·
                refine ⟨4656363680334023854295957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104242453556015902863971 4656363680334023854295957)
                ·
                  refine ⟨218267047515657368170123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4656363680334023854295957 218267047515657368170123)
                  ·
                    rfl

theorem cell23_3825662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_3825662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825662 prefixEnd_3825662 := by exact prefixLift 3825662
  have htrace : WordTrace (prefixWord ++ tailWord_3825662) baseStart_3825662 baseEnd_3825662 := by
    simpa [prefixWord, tailWord_3825662, baseEnd_3825662] using wordTrace_append hprefix tailTrace_3825662
  have hstable : (prefixWord ++ tailWord_3825662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825662).length < 2 ^ (prefixWord ++ tailWord_3825662).sum := by decide
  have hdescent : baseEnd_3825662 < baseStart_3825662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825688 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 6, 4]
def baseStart_3825688 : Nat := 118140960795 + 3825688 * 2 ^ 59
def prefixEnd_3825688 : Nat := 4983230072969 + 3 ^ 40 * 3825688 * 2
def baseEnd_3825688 : Nat := 654805592712644403935329

theorem tailTrace_3825688 : CollatzResearch.WordTrace tailWord_3825688 prefixEnd_3825688 654805592712644403935329 := by
  unfold tailWord_3825688
  simp only [CollatzResearch.WordTrace]
  refine ⟨69767152282096613168814859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93022869709462150891753145 69767152282096613168814859)
  ·
    refine ⟨104650728423144919753222289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69767152282096613168814859 104650728423144919753222289)
    ·
      refine ⟨78488046317358689814916717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104650728423144919753222289 78488046317358689814916717)
      ·
        refine ⟨29433017369009508680593769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78488046317358689814916717 29433017369009508680593769)
        ·
          refine ⟨22074763026757131510445327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29433017369009508680593769 22074763026757131510445327)
          ·
            refine ⟨33112144540135697265667991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22074763026757131510445327 33112144540135697265667991)
            ·
              refine ⟨49668216810203545898501987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33112144540135697265667991 49668216810203545898501987)
              ·
                refine ⟨74502325215305318847752981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49668216810203545898501987 74502325215305318847752981)
                ·
                  refine ⟨3492296494467436820988421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74502325215305318847752981 3492296494467436820988421)
                  ·
                    refine ⟨654805592712644403935329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3492296494467436820988421 654805592712644403935329)
                    ·
                      rfl

theorem cell23_3825688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_3825688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825688 prefixEnd_3825688 := by exact prefixLift 3825688
  have htrace : WordTrace (prefixWord ++ tailWord_3825688) baseStart_3825688 baseEnd_3825688 := by
    simpa [prefixWord, tailWord_3825688, baseEnd_3825688] using wordTrace_append hprefix tailTrace_3825688
  have hstable : (prefixWord ++ tailWord_3825688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825688).length < 2 ^ (prefixWord ++ tailWord_3825688).sum := by decide
  have hdescent : baseEnd_3825688 < baseStart_3825688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825701 : List Nat := [1, 3, 1, 2, 2, 3, 11]
def baseStart_3825701 : Nat := 118140960795 + 3825701 * 2 ^ 59
def prefixEnd_3825701 : Nat := 4983230072969 + 3 ^ 40 * 3825701 * 2
def baseEnd_3825701 : Nat := 24252141399832613098067

theorem tailTrace_3825701 : CollatzResearch.WordTrace tailWord_3825701 prefixEnd_3825701 24252141399832613098067 := by
  unfold tailWord_3825701
  simp only [CollatzResearch.WordTrace]
  refine ⟨139534778713146129557852957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93023185808764086371901971 139534778713146129557852957)
  ·
    refine ⟨52325542017429798584194859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139534778713146129557852957 52325542017429798584194859)
    ·
      refine ⟨78488313026144697876292289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52325542017429798584194859 78488313026144697876292289)
      ·
        refine ⟨58866234769608523407219217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78488313026144697876292289 58866234769608523407219217)
        ·
          refine ⟨44149676077206392555414413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58866234769608523407219217 44149676077206392555414413)
          ·
            refine ⟨16556128528952397208280405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44149676077206392555414413 16556128528952397208280405)
            ·
              refine ⟨24252141399832613098067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16556128528952397208280405 24252141399832613098067)
              ·
                rfl

theorem cell23_3825701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 11].length) (baseStart_3825701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825701 prefixEnd_3825701 := by exact prefixLift 3825701
  have htrace : WordTrace (prefixWord ++ tailWord_3825701) baseStart_3825701 baseEnd_3825701 := by
    simpa [prefixWord, tailWord_3825701, baseEnd_3825701] using wordTrace_append hprefix tailTrace_3825701
  have hstable : (prefixWord ++ tailWord_3825701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825701).length < 2 ^ (prefixWord ++ tailWord_3825701).sum := by decide
  have hdescent : baseEnd_3825701 < baseStart_3825701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825706 : List Nat := [3, 1, 4, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_3825706 : Nat := 118140960795 + 3825706 * 2 ^ 59
def prefixEnd_3825706 : Nat := 4983230072969 + 3 ^ 40 * 3825706 * 2
def baseEnd_3825706 : Nat := 1964426020789714141380905

theorem tailTrace_3825706 : CollatzResearch.WordTrace tailWord_3825706 prefixEnd_3825706 1964426020789714141380905 := by
  unfold tailWord_3825706
  simp only [CollatzResearch.WordTrace]
  refine ⟨34883740269532003852946243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93023307385418676941189981 34883740269532003852946243)
  ·
    refine ⟨52325610404298005779419365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34883740269532003852946243 52325610404298005779419365)
    ·
      refine ⟨9811051950805876083641131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52325610404298005779419365 9811051950805876083641131)
      ·
        refine ⟨14716577926208814125461697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9811051950805876083641131 14716577926208814125461697)
        ·
          refine ⟨11037433444656610594096273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14716577926208814125461697 11037433444656610594096273)
          ·
            refine ⟨8278075083492457945572205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11037433444656610594096273 8278075083492457945572205)
            ·
              refine ⟨3104278156309671729589577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8278075083492457945572205 3104278156309671729589577)
              ·
                refine ⟨2328208617232253797192183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3104278156309671729589577 2328208617232253797192183)
                ·
                  refine ⟨3492312925848380695788275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328208617232253797192183 3492312925848380695788275)
                  ·
                    refine ⟨5238469388772571043682413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3492312925848380695788275 5238469388772571043682413)
                    ·
                      refine ⟨1964426020789714141380905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5238469388772571043682413 1964426020789714141380905)
                      ·
                        rfl

theorem cell23_3825706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_3825706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825706 prefixEnd_3825706 := by exact prefixLift 3825706
  have htrace : WordTrace (prefixWord ++ tailWord_3825706) baseStart_3825706 baseEnd_3825706 := by
    simpa [prefixWord, tailWord_3825706, baseEnd_3825706] using wordTrace_append hprefix tailTrace_3825706
  have hstable : (prefixWord ++ tailWord_3825706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825706).length < 2 ^ (prefixWord ++ tailWord_3825706).sum := by decide
  have hdescent : baseEnd_3825706 < baseStart_3825706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825712 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 3, 2, 2]
def baseStart_3825712 : Nat := 118140960795 + 3825712 * 2 ^ 59
def prefixEnd_3825712 : Nat := 4983230072969 + 3 ^ 40 * 3825712 * 2
def baseEnd_3825712 : Nat := 1964429101673641117905877

theorem tailTrace_3825712 : CollatzResearch.WordTrace tailWord_3825712 prefixEnd_3825712 1964429101673641117905877 := by
  unfold tailWord_3825712
  simp only [CollatzResearch.WordTrace]
  refine ⟨69767589958053139218251695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93023453277404185624335593 69767589958053139218251695)
  ·
    refine ⟨104651384937079708827377543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69767589958053139218251695 104651384937079708827377543)
    ·
      refine ⟨156977077405619563241066315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104651384937079708827377543 156977077405619563241066315)
      ·
        refine ⟨235465616108429344861599473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156977077405619563241066315 235465616108429344861599473)
        ·
          refine ⟨176599212081322008646199605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235465616108429344861599473 176599212081322008646199605)
          ·
            refine ⟨16556176132623938310581213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176599212081322008646199605 16556176132623938310581213)
            ·
              refine ⟨6208566049733976866467955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16556176132623938310581213 6208566049733976866467955)
              ·
                refine ⟨9312849074600965299701933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6208566049733976866467955 9312849074600965299701933)
                ·
                  refine ⟨3492318402975361987388225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9312849074600965299701933 3492318402975361987388225)
                  ·
                    refine ⟨2619238802231521490541169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3492318402975361987388225 2619238802231521490541169)
                    ·
                      refine ⟨1964429101673641117905877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2619238802231521490541169 1964429101673641117905877)
                      ·
                        rfl

theorem cell23_3825712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 3, 2, 2].length) (baseStart_3825712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825712 prefixEnd_3825712 := by exact prefixLift 3825712
  have htrace : WordTrace (prefixWord ++ tailWord_3825712) baseStart_3825712 baseEnd_3825712 := by
    simpa [prefixWord, tailWord_3825712, baseEnd_3825712] using wordTrace_append hprefix tailTrace_3825712
  have hstable : (prefixWord ++ tailWord_3825712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825712).length < 2 ^ (prefixWord ++ tailWord_3825712).sum := by decide
  have hdescent : baseEnd_3825712 < baseStart_3825712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825731 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 4, 7]
def baseStart_3825731 : Nat := 118140960795 + 3825731 * 2 ^ 59
def prefixEnd_3825731 : Nat := 4983230072969 + 3 ^ 40 * 3825731 * 2
def baseEnd_3825731 : Nat := 654812952602025514522763

theorem tailTrace_3825731 : CollatzResearch.WordTrace tailWord_3825731 prefixEnd_3825731 654812952602025514522763 := by
  unfold tailWord_3825731
  simp only [CollatzResearch.WordTrace]
  refine ⟨139535872903037444681445047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93023915268691629787630031 139535872903037444681445047)
  ·
    refine ⟨209303809354556167022167571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139535872903037444681445047 209303809354556167022167571)
    ·
      refine ⟨313955714031834250533251357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209303809354556167022167571 313955714031834250533251357)
      ·
        refine ⟨117733392761937843949969259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313955714031834250533251357 117733392761937843949969259)
        ·
          refine ⟨176600089142906765924953889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117733392761937843949969259 176600089142906765924953889)
          ·
            refine ⟨132450066857180074443715417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176600089142906765924953889 132450066857180074443715417)
            ·
              refine ⟨99337550142885055832786563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132450066857180074443715417 99337550142885055832786563)
              ·
                refine ⟨149006325214327583749179845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99337550142885055832786563 149006325214327583749179845)
                ·
                  refine ⟨27938685977686421952971221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149006325214327583749179845 27938685977686421952971221)
                  ·
                    refine ⟨654812952602025514522763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27938685977686421952971221 654812952602025514522763)
                    ·
                      rfl

theorem cell23_3825731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 7].length) (baseStart_3825731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825731 prefixEnd_3825731 := by exact prefixLift 3825731
  have htrace : WordTrace (prefixWord ++ tailWord_3825731) baseStart_3825731 baseEnd_3825731 := by
    simpa [prefixWord, tailWord_3825731, baseEnd_3825731] using wordTrace_append hprefix tailTrace_3825731
  have hstable : (prefixWord ++ tailWord_3825731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825731).length < 2 ^ (prefixWord ++ tailWord_3825731).sum := by decide
  have hdescent : baseEnd_3825731 < baseStart_3825731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825778 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_3825778 : Nat := 118140960795 + 3825778 * 2 ^ 59
def prefixEnd_3825778 : Nat := 4983230072969 + 3 ^ 40 * 3825778 * 2
def baseEnd_3825778 : Nat := 654820997132279286560191

theorem tailTrace_3825778 : CollatzResearch.WordTrace tailWord_3825778 prefixEnd_3825778 654820997132279286560191 := by
  unfold tailWord_3825778
  simp only [CollatzResearch.WordTrace]
  refine ⟨34884396783466792927101497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93025058089244781138937325 34884396783466792927101497)
  ·
    refine ⟨26163297587600094695326123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34884396783466792927101497 26163297587600094695326123)
    ·
      refine ⟨39244946381400142042989185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26163297587600094695326123 39244946381400142042989185)
      ·
        refine ⟨29433709786050106532241889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39244946381400142042989185 29433709786050106532241889)
        ·
          refine ⟨22075282339537579899181417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29433709786050106532241889 22075282339537579899181417)
          ·
            refine ⟨16556461754653184924386063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22075282339537579899181417 16556461754653184924386063)
            ·
              refine ⟨24834692631979777386579095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16556461754653184924386063 24834692631979777386579095)
              ·
                refine ⟨37252038947969666079868643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24834692631979777386579095 37252038947969666079868643)
                ·
                  refine ⟨55878058421954499119802965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37252038947969666079868643 55878058421954499119802965)
                  ·
                    refine ⟨654820997132279286560191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55878058421954499119802965 654820997132279286560191)
                    ·
                      rfl

theorem cell23_3825778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_3825778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825778 prefixEnd_3825778 := by exact prefixLift 3825778
  have htrace : WordTrace (prefixWord ++ tailWord_3825778) baseStart_3825778 baseEnd_3825778 := by
    simpa [prefixWord, tailWord_3825778, baseEnd_3825778] using wordTrace_append hprefix tailTrace_3825778
  have hstable : (prefixWord ++ tailWord_3825778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825778).length < 2 ^ (prefixWord ++ tailWord_3825778).sum := by decide
  have hdescent : baseEnd_3825778 < baseStart_3825778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825802 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 1, 4, 2]
def baseStart_3825802 : Nat := 118140960795 + 3825802 * 2 ^ 59
def prefixEnd_3825802 : Nat := 4983230072969 + 3 ^ 40 * 3825802 * 2
def baseEnd_3825802 : Nat := 1964475314932545765780463

theorem tailTrace_3825802 : CollatzResearch.WordTrace tailWord_3825802 prefixEnd_3825802 1964475314932545765780463 := by
  unfold tailWord_3825802
  simp only [CollatzResearch.WordTrace]
  refine ⟨34884615621445055951819915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93025641657186815871519773 34884615621445055951819915)
  ·
    refine ⟨52326923432167583927729873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34884615621445055951819915 52326923432167583927729873)
    ·
      refine ⟨39245192574125687945797405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52326923432167583927729873 39245192574125687945797405)
      ·
        refine ⟨14716947215297132979674027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39245192574125687945797405 14716947215297132979674027)
        ·
          refine ⟨22075420822945699469511041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14716947215297132979674027 22075420822945699469511041)
          ·
            refine ⟨16556565617209274602133281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22075420822945699469511041 16556565617209274602133281)
            ·
              refine ⟨12417424212906955951599961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16556565617209274602133281 12417424212906955951599961)
              ·
                refine ⟨9313068159680216963699971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12417424212906955951599961 9313068159680216963699971)
                ·
                  refine ⟨13969602239520325445549957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9313068159680216963699971 13969602239520325445549957)
                  ·
                    refine ⟨2619300419910061021040617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13969602239520325445549957 2619300419910061021040617)
                    ·
                      refine ⟨1964475314932545765780463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2619300419910061021040617 1964475314932545765780463)
                      ·
                        rfl

theorem cell23_3825802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_3825802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825802 prefixEnd_3825802 := by exact prefixLift 3825802
  have htrace : WordTrace (prefixWord ++ tailWord_3825802) baseStart_3825802 baseEnd_3825802 := by
    simpa [prefixWord, tailWord_3825802, baseEnd_3825802] using wordTrace_append hprefix tailTrace_3825802
  have hstable : (prefixWord ++ tailWord_3825802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825802).length < 2 ^ (prefixWord ++ tailWord_3825802).sum := by decide
  have hdescent : baseEnd_3825802 < baseStart_3825802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825825 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 7]
def baseStart_3825825 : Nat := 118140960795 + 3825825 * 2 ^ 59
def prefixEnd_3825825 : Nat := 4983230072969 + 3 ^ 40 * 3825825 * 2
def baseEnd_3825825 : Nat := 218276347220844352865873

theorem tailTrace_3825825 : CollatzResearch.WordTrace tailWord_3825825 prefixEnd_3825825 218276347220844352865873 := by
  unfold tailWord_3825825
  simp only [CollatzResearch.WordTrace]
  refine ⟨139539301364696898735366929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93026200909797932490244619 139539301364696898735366929)
  ·
    refine ⟨104654476023522674051525197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139539301364696898735366929 104654476023522674051525197)
    ·
      refine ⟨39245428508821002769321949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104654476023522674051525197 39245428508821002769321949)
      ·
        refine ⟨14717035690807876038495731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39245428508821002769321949 14717035690807876038495731)
        ·
          refine ⟨22075553536211814057743597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14717035690807876038495731 22075553536211814057743597)
          ·
            refine ⟨8278332576079430271653849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22075553536211814057743597 8278332576079430271653849)
            ·
              refine ⟨6208749432059572703740387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8278332576079430271653849 6208749432059572703740387)
              ·
                refine ⟨9313124148089359055610581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6208749432059572703740387 9313124148089359055610581)
                ·
                  refine ⟨218276347220844352865873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9313124148089359055610581 218276347220844352865873)
                  ·
                    rfl

theorem cell23_3825825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 7].length) (baseStart_3825825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825825 prefixEnd_3825825 := by exact prefixLift 3825825
  have htrace : WordTrace (prefixWord ++ tailWord_3825825) baseStart_3825825 baseEnd_3825825 := by
    simpa [prefixWord, tailWord_3825825, baseEnd_3825825] using wordTrace_append hprefix tailTrace_3825825
  have hstable : (prefixWord ++ tailWord_3825825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825825).length < 2 ^ (prefixWord ++ tailWord_3825825).sum := by decide
  have hdescent : baseEnd_3825825 < baseStart_3825825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825969 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 1, 5, 2]
def baseStart_3825969 : Nat := 118140960795 + 3825969 * 2 ^ 59
def prefixEnd_3825969 : Nat := 4983230072969 + 3 ^ 40 * 3825969 * 2
def baseEnd_3825969 : Nat := 1964561066201846612392195

theorem tailTrace_3825969 : CollatzResearch.WordTrace tailWord_3825969 prefixEnd_3825969 1964561066201846612392195 := by
  unfold tailWord_3825969
  simp only [CollatzResearch.WordTrace]
  refine ⟨139544553476175211328608961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93029702317450140885739307 139544553476175211328608961)
  ·
    refine ⟨104658415107131408496456721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139544553476175211328608961 104658415107131408496456721)
    ·
      refine ⟨78493811330348556372342541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104658415107131408496456721 78493811330348556372342541)
      ·
        refine ⟨29435179248880708639628453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78493811330348556372342541 29435179248880708639628453)
        ·
          refine ⟨5519096109165132869930335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29435179248880708639628453 5519096109165132869930335)
          ·
            refine ⟨8278644163747699304895503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5519096109165132869930335 8278644163747699304895503)
            ·
              refine ⟨12417966245621548957343255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8278644163747699304895503 12417966245621548957343255)
              ·
                refine ⟨18626949368432323436014883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12417966245621548957343255 18626949368432323436014883)
                ·
                  refine ⟨27940424052648485154022325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18626949368432323436014883 27940424052648485154022325)
                  ·
                    refine ⟨2619414754935795483189593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27940424052648485154022325 2619414754935795483189593)
                    ·
                      refine ⟨1964561066201846612392195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2619414754935795483189593 1964561066201846612392195)
                      ·
                        rfl

theorem cell23_3825969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_3825969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3825969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3825969 prefixEnd_3825969 := by exact prefixLift 3825969
  have htrace : WordTrace (prefixWord ++ tailWord_3825969) baseStart_3825969 baseEnd_3825969 := by
    simpa [prefixWord, tailWord_3825969, baseEnd_3825969] using wordTrace_append hprefix tailTrace_3825969
  have hstable : (prefixWord ++ tailWord_3825969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825969).length < 2 ^ (prefixWord ++ tailWord_3825969).sum := by decide
  have hdescent : baseEnd_3825969 < baseStart_3825969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826002 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_3826002 : Nat := 118140960795 + 3826002 * 2 ^ 59
def prefixEnd_3826002 : Nat := 4983230072969 + 3 ^ 40 * 3826002 * 2
def baseEnd_3826002 : Nat := 1964578011063444983279543

theorem tailTrace_3826002 : CollatzResearch.WordTrace tailWord_3826002 prefixEnd_3826002 1964578011063444983279543 := by
  unfold tailWord_3826002
  simp only [CollatzResearch.WordTrace]
  refine ⟨34886439271263914491140065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93030504723370438643040173 34886439271263914491140065)
  ·
    refine ⟨26164829453447935868355049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34886439271263914491140065 26164829453447935868355049)
    ·
      refine ⟨19623622090085951901266287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26164829453447935868355049 19623622090085951901266287)
      ·
        refine ⟨29435433135128927851899431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19623622090085951901266287 29435433135128927851899431)
        ·
          refine ⟨44153149702693391777849147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29435433135128927851899431 44153149702693391777849147)
          ·
            refine ⟨66229724554040087666773721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44153149702693391777849147 66229724554040087666773721)
            ·
              refine ⟨49672293415530065750080291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66229724554040087666773721 49672293415530065750080291)
              ·
                refine ⟨74508440123295098625120437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49672293415530065750080291 74508440123295098625120437)
                ·
                  refine ⟨6985166261558915496105041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74508440123295098625120437 6985166261558915496105041)
                  ·
                    refine ⟨5238874696169186622078781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6985166261558915496105041 5238874696169186622078781)
                    ·
                      refine ⟨1964578011063444983279543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5238874696169186622078781 1964578011063444983279543)
                      ·
                        rfl

theorem cell23_3826002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_3826002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826002 prefixEnd_3826002 := by exact prefixLift 3826002
  have htrace : WordTrace (prefixWord ++ tailWord_3826002) baseStart_3826002 baseEnd_3826002 := by
    simpa [prefixWord, tailWord_3826002, baseEnd_3826002] using wordTrace_append hprefix tailTrace_3826002
  have hstable : (prefixWord ++ tailWord_3826002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826002).length < 2 ^ (prefixWord ++ tailWord_3826002).sum := by decide
  have hdescent : baseEnd_3826002 < baseStart_3826002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826019 : List Nat := [1, 1, 1, 5, 2, 1, 4, 2, 1, 2, 3]
def baseStart_3826019 : Nat := 118140960795 + 3826019 * 2 ^ 59
def prefixEnd_3826019 : Nat := 4983230072969 + 3 ^ 40 * 3826019 * 2
def baseEnd_3826019 : Nat := 1964586740234571416766965

theorem tailTrace_3826019 : CollatzResearch.WordTrace tailWord_3826019 prefixEnd_3826019 1964586740234571416766965 := by
  unfold tailWord_3826019
  simp only [CollatzResearch.WordTrace]
  refine ⟨139546377125994069867929111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93030918083996046578619407 139546377125994069867929111)
  ·
    refine ⟨209319565688991104801893667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139546377125994069867929111 209319565688991104801893667)
    ·
      refine ⟨313979348533486657202840501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209319565688991104801893667 313979348533486657202840501)
      ·
        refine ⟨29435563925014374112766297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 313979348533486657202840501 29435563925014374112766297)
        ·
          refine ⟨22076672943760780584574723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29435563925014374112766297 22076672943760780584574723)
          ·
            refine ⟨33115009415641170876862085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22076672943760780584574723 33115009415641170876862085)
            ·
              refine ⟨6209064265432719539411641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33115009415641170876862085 6209064265432719539411641)
              ·
                refine ⟨4656798199074539654558731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6209064265432719539411641 4656798199074539654558731)
                ·
                  refine ⟨6985197298611809481838097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656798199074539654558731 6985197298611809481838097)
                  ·
                    refine ⟨5238897973958857111378573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6985197298611809481838097 5238897973958857111378573)
                    ·
                      refine ⟨1964586740234571416766965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5238897973958857111378573 1964586740234571416766965)
                      ·
                        rfl

theorem cell23_3826019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_3826019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826019 prefixEnd_3826019 := by exact prefixLift 3826019
  have htrace : WordTrace (prefixWord ++ tailWord_3826019) baseStart_3826019 baseEnd_3826019 := by
    simpa [prefixWord, tailWord_3826019, baseEnd_3826019] using wordTrace_append hprefix tailTrace_3826019
  have hstable : (prefixWord ++ tailWord_3826019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826019).length < 2 ^ (prefixWord ++ tailWord_3826019).sum := by decide
  have hdescent : baseEnd_3826019 < baseStart_3826019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826070 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3826070 : Nat := 118140960795 + 3826070 * 2 ^ 59
def prefixEnd_3826070 : Nat := 4983230072969 + 3 ^ 40 * 3826070 * 2
def baseEnd_3826070 : Nat := 1964612927747950717229231

theorem tailTrace_3826070 : CollatzResearch.WordTrace tailWord_3826070 prefixEnd_3826070 1964612927747950717229231 := by
  unfold tailWord_3826070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721764828050581598627229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93032158165872870385357109 8721764828050581598627229)
  ·
    refine ⟨3270661810518968099485211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8721764828050581598627229 3270661810518968099485211)
    ·
      refine ⟨4905992715778452149227817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3270661810518968099485211 4905992715778452149227817)
      ·
        refine ⟨3679494536833839111920863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4905992715778452149227817 3679494536833839111920863)
        ·
          refine ⟨5519241805250758667881295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679494536833839111920863 5519241805250758667881295)
          ·
            refine ⟨8278862707876138001821943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5519241805250758667881295 8278862707876138001821943)
            ·
              refine ⟨12418294061814207002732915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8278862707876138001821943 12418294061814207002732915)
              ·
                refine ⟨18627441092721310504099373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12418294061814207002732915 18627441092721310504099373)
                ·
                  refine ⟨6985290409770491439037265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18627441092721310504099373 6985290409770491439037265)
                  ·
                    refine ⟨5238967807327868579277949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6985290409770491439037265 5238967807327868579277949)
                    ·
                      refine ⟨1964612927747950717229231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5238967807327868579277949 1964612927747950717229231)
                      ·
                        rfl

theorem cell23_3826070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3826070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826070 prefixEnd_3826070 := by exact prefixLift 3826070
  have htrace : WordTrace (prefixWord ++ tailWord_3826070) baseStart_3826070 baseEnd_3826070 := by
    simpa [prefixWord, tailWord_3826070, baseEnd_3826070] using wordTrace_append hprefix tailTrace_3826070
  have hstable : (prefixWord ++ tailWord_3826070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826070).length < 2 ^ (prefixWord ++ tailWord_3826070).sum := by decide
  have hdescent : baseEnd_3826070 < baseStart_3826070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826089 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 6, 2, 2]
def baseStart_3826089 : Nat := 118140960795 + 3826089 * 2 ^ 59
def prefixEnd_3826089 : Nat := 4983230072969 + 3 ^ 40 * 3826089 * 2
def baseEnd_3826089 : Nat := 1964622683880386142891643

theorem tailTrace_3826089 : CollatzResearch.WordTrace tailWord_3826089 prefixEnd_3826089 1964622683880386142891643 := by
  unfold tailWord_3826089
  simp only [CollatzResearch.WordTrace]
  refine ⟨139548930235740471822977321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93032620157160314548651547 139548930235740471822977321)
  ·
    refine ⟨104661697676805353867232991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139548930235740471822977321 104661697676805353867232991)
    ·
      refine ⟨156992546515208030800849487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104661697676805353867232991 156992546515208030800849487)
      ·
        refine ⟨235488819772812046201274231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156992546515208030800849487 235488819772812046201274231)
        ·
          refine ⟨353233229659218069301911347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235488819772812046201274231 353233229659218069301911347)
          ·
            refine ⟨529849844488827103952867021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353233229659218069301911347 529849844488827103952867021)
            ·
              refine ⟨198693691683310163982325133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 529849844488827103952867021 198693691683310163982325133)
              ·
                refine ⟨74510134381241311493371925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198693691683310163982325133 74510134381241311493371925)
                ·
                  refine ⟨3492662549120686476251809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74510134381241311493371925 3492662549120686476251809)
                  ·
                    refine ⟨2619496911840514857188857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3492662549120686476251809 2619496911840514857188857)
                    ·
                      refine ⟨1964622683880386142891643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2619496911840514857188857 1964622683880386142891643)
                      ·
                        rfl

theorem cell23_3826089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 2, 2].length) (baseStart_3826089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826089 prefixEnd_3826089 := by exact prefixLift 3826089
  have htrace : WordTrace (prefixWord ++ tailWord_3826089) baseStart_3826089 baseEnd_3826089 := by
    simpa [prefixWord, tailWord_3826089, baseEnd_3826089] using wordTrace_append hprefix tailTrace_3826089
  have hstable : (prefixWord ++ tailWord_3826089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826089).length < 2 ^ (prefixWord ++ tailWord_3826089).sum := by decide
  have hdescent : baseEnd_3826089 < baseStart_3826089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826115 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 8]
def baseStart_3826115 : Nat := 118140960795 + 3826115 * 2 ^ 59
def prefixEnd_3826115 : Nat := 4983230072969 + 3 ^ 40 * 3826115 * 2
def baseEnd_3826115 : Nat := 1964636034377403041166523

theorem tailTrace_3826115 : CollatzResearch.WordTrace tailWord_3826115 prefixEnd_3826115 1964636034377403041166523 := by
  unfold tailWord_3826115
  simp only [CollatzResearch.WordTrace]
  refine ⟨139549878533646278263423799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93033252355764185508949199 139549878533646278263423799)
  ·
    refine ⟨209324817800469417395135699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139549878533646278263423799 209324817800469417395135699)
    ·
      refine ⟨313987226700704126092703549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209324817800469417395135699 313987226700704126092703549)
      ·
        refine ⟨117745210012764047284763831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313987226700704126092703549 117745210012764047284763831)
        ·
          refine ⟨176617815019146070927145747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117745210012764047284763831 176617815019146070927145747)
          ·
            refine ⟨264926722528719106390718621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176617815019146070927145747 264926722528719106390718621)
            ·
              refine ⟨99347520948269664896519483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264926722528719106390718621 99347520948269664896519483)
              ·
                refine ⟨149021281422404497344779225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99347520948269664896519483 149021281422404497344779225)
                ·
                  refine ⟨111765961066803373008584419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149021281422404497344779225 111765961066803373008584419)
                  ·
                    refine ⟨167648941600205059512876629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111765961066803373008584419 167648941600205059512876629)
                    ·
                      refine ⟨1964636034377403041166523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 167648941600205059512876629 1964636034377403041166523)
                      ·
                        rfl

theorem cell23_3826115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_3826115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826115 prefixEnd_3826115 := by exact prefixLift 3826115
  have htrace : WordTrace (prefixWord ++ tailWord_3826115) baseStart_3826115 baseEnd_3826115 := by
    simpa [prefixWord, tailWord_3826115, baseEnd_3826115] using wordTrace_append hprefix tailTrace_3826115
  have hstable : (prefixWord ++ tailWord_3826115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826115).length < 2 ^ (prefixWord ++ tailWord_3826115).sum := by decide
  have hdescent : baseEnd_3826115 < baseStart_3826115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826179 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 2, 4, 2]
def baseStart_3826179 : Nat := 118140960795 + 3826179 * 2 ^ 59
def prefixEnd_3826179 : Nat := 4983230072969 + 3 ^ 40 * 3826179 * 2
def baseEnd_3826179 : Nat := 1964668897139290790766229

theorem tailTrace_3826179 : CollatzResearch.WordTrace tailWord_3826179 prefixEnd_3826179 1964668897139290790766229 := by
  unfold tailWord_3826179
  simp only [CollatzResearch.WordTrace]
  refine ⟨139552212805414417193753591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93034808536942944795835727 139552212805414417193753591)
  ·
    refine ⟨209328319208121625790630387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139552212805414417193753591 209328319208121625790630387)
    ·
      refine ⟨313992478812182438685945581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209328319208121625790630387 313992478812182438685945581)
      ·
        refine ⟨117747179554568414507229593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313992478812182438685945581 117747179554568414507229593)
        ·
          refine ⟨88310384665926310880422195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117747179554568414507229593 88310384665926310880422195)
          ·
            refine ⟨132465576998889466320633293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88310384665926310880422195 132465576998889466320633293)
            ·
              refine ⟨49674591374583549870237485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132465576998889466320633293 49674591374583549870237485)
              ·
                refine ⟨18627971765468831201339057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49674591374583549870237485 18627971765468831201339057)
                ·
                  refine ⟨13970978824101623401004293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18627971765468831201339057 13970978824101623401004293)
                  ·
                    refine ⟨2619558529519054387688305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13970978824101623401004293 2619558529519054387688305)
                    ·
                      refine ⟨1964668897139290790766229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2619558529519054387688305 1964668897139290790766229)
                      ·
                        rfl

theorem cell23_3826179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 4, 2].length) (baseStart_3826179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826179 prefixEnd_3826179 := by exact prefixLift 3826179
  have htrace : WordTrace (prefixWord ++ tailWord_3826179) baseStart_3826179 baseEnd_3826179 := by
    simpa [prefixWord, tailWord_3826179, baseEnd_3826179] using wordTrace_append hprefix tailTrace_3826179
  have hstable : (prefixWord ++ tailWord_3826179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826179).length < 2 ^ (prefixWord ++ tailWord_3826179).sum := by decide
  have hdescent : baseEnd_3826179 < baseStart_3826179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826196 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3826196 : Nat := 118140960795 + 3826196 * 2 ^ 59
def prefixEnd_3826196 : Nat := 4983230072969 + 3 ^ 40 * 3826196 * 2
def baseEnd_3826196 : Nat := 1964677626310417224253651

theorem tailTrace_3826196 : CollatzResearch.WordTrace tailWord_3826196 prefixEnd_3826196 1964677626310417224253651 := by
  unfold tailWord_3826196
  simp only [CollatzResearch.WordTrace]
  refine ⟨69776416423176414548561221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93035221897568552731414961 69776416423176414548561221)
  ·
    refine ⟨13083078079345577727855229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69776416423176414548561221 13083078079345577727855229)
    ·
      refine ⟨4906154279754591647945711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13083078079345577727855229 4906154279754591647945711)
      ·
        refine ⟨7359231419631887471918567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4906154279754591647945711 7359231419631887471918567)
        ·
          refine ⟨11038847129447831207877851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7359231419631887471918567 11038847129447831207877851)
          ·
            refine ⟨16558270694171746811816777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11038847129447831207877851 16558270694171746811816777)
            ·
              refine ⟨12418703020628810108862583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16558270694171746811816777 12418703020628810108862583)
              ·
                refine ⟨18628054530943215163293875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12418703020628810108862583 18628054530943215163293875)
                ·
                  refine ⟨27942081796414822744940813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18628054530943215163293875 27942081796414822744940813)
                  ·
                    refine ⟨10478280673655558529352805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27942081796414822744940813 10478280673655558529352805)
                    ·
                      refine ⟨1964677626310417224253651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10478280673655558529352805 1964677626310417224253651)
                      ·
                        rfl

theorem cell23_3826196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3826196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826196 prefixEnd_3826196 := by exact prefixLift 3826196
  have htrace : WordTrace (prefixWord ++ tailWord_3826196) baseStart_3826196 baseEnd_3826196 := by
    simpa [prefixWord, tailWord_3826196, baseEnd_3826196] using wordTrace_append hprefix tailTrace_3826196
  have hstable : (prefixWord ++ tailWord_3826196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826196).length < 2 ^ (prefixWord ++ tailWord_3826196).sum := by decide
  have hdescent : baseEnd_3826196 < baseStart_3826196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826202 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 8]
def baseStart_3826202 : Nat := 118140960795 + 3826202 * 2 ^ 59
def prefixEnd_3826202 : Nat := 4983230072969 + 3 ^ 40 * 3826202 * 2
def baseEnd_3826202 : Nat := 218297856354927133419847

theorem tailTrace_3826202 : CollatzResearch.WordTrace tailWord_3826202 prefixEnd_3826202 218297856354927133419847 := by
  unfold tailWord_3826202
  simp only [CollatzResearch.WordTrace]
  refine ⟨34888262921082773030460215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93035367789554061414560573 34888262921082773030460215)
  ·
    refine ⟨52332394381624159545690323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34888262921082773030460215 52332394381624159545690323)
    ·
      refine ⟨78498591572436239318535485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52332394381624159545690323 78498591572436239318535485)
      ·
        refine ⟨29436971839663589744450807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78498591572436239318535485 29436971839663589744450807)
        ·
          refine ⟨44155457759495384616676211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29436971839663589744450807 44155457759495384616676211)
          ·
            refine ⟨66233186639243076925014317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44155457759495384616676211 66233186639243076925014317)
            ·
              refine ⟨24837444989716153846880369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66233186639243076925014317 24837444989716153846880369)
              ·
                refine ⟨18628083742287115385160277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24837444989716153846880369 18628083742287115385160277)
                ·
                  refine ⟨218297856354927133419847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18628083742287115385160277 218297856354927133419847)
                  ·
                    rfl

theorem cell23_3826202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_3826202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826202 prefixEnd_3826202 := by exact prefixLift 3826202
  have htrace : WordTrace (prefixWord ++ tailWord_3826202) baseStart_3826202 baseEnd_3826202 := by
    simpa [prefixWord, tailWord_3826202, baseEnd_3826202] using wordTrace_append hprefix tailTrace_3826202
  have hstable : (prefixWord ++ tailWord_3826202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826202).length < 2 ^ (prefixWord ++ tailWord_3826202).sum := by decide
  have hdescent : baseEnd_3826202 < baseStart_3826202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826216 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3826216 : Nat := 118140960795 + 3826216 * 2 ^ 59
def prefixEnd_3826216 : Nat := 4983230072969 + 3 ^ 40 * 3826216 * 2
def baseEnd_3826216 : Nat := 1964687895923507146003559

theorem tailTrace_3826216 : CollatzResearch.WordTrace tailWord_3826216 prefixEnd_3826216 1964687895923507146003559 := by
  unfold tailWord_3826216
  simp only [CollatzResearch.WordTrace]
  refine ⟨69776781153140186256425251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93035708204186915008567001 69776781153140186256425251)
  ·
    refine ⟨104665171729710279384637877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69776781153140186256425251 104665171729710279384637877)
    ·
      refine ⟨9812359849660338692309801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104665171729710279384637877 9812359849660338692309801)
      ·
        refine ⟨7359269887245254019232351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9812359849660338692309801 7359269887245254019232351)
        ·
          refine ⟨11038904830867881028848527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7359269887245254019232351 11038904830867881028848527)
          ·
            refine ⟨16558357246301821543272791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11038904830867881028848527 16558357246301821543272791)
            ·
              refine ⟨24837535869452732314909187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16558357246301821543272791 24837535869452732314909187)
              ·
                refine ⟨37256303804179098472363781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24837535869452732314909187 37256303804179098472363781)
                ·
                  refine ⟨6985556963283580963568209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37256303804179098472363781 6985556963283580963568209)
                  ·
                    refine ⟨5239167722462685722676157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6985556963283580963568209 5239167722462685722676157)
                    ·
                      refine ⟨1964687895923507146003559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5239167722462685722676157 1964687895923507146003559)
                      ·
                        rfl

theorem cell23_3826216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3826216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826216 prefixEnd_3826216 := by exact prefixLift 3826216
  have htrace : WordTrace (prefixWord ++ tailWord_3826216) baseStart_3826216 baseEnd_3826216 := by
    simpa [prefixWord, tailWord_3826216, baseEnd_3826216] using wordTrace_append hprefix tailTrace_3826216
  have hstable : (prefixWord ++ tailWord_3826216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826216).length < 2 ^ (prefixWord ++ tailWord_3826216).sum := by decide
  have hdescent : baseEnd_3826216 < baseStart_3826216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826236 : List Nat := [2, 2, 2, 2, 3, 1, 4, 1, 6]
def baseStart_3826236 : Nat := 118140960795 + 3826236 * 2 ^ 59
def prefixEnd_3826236 : Nat := 4983230072969 + 3 ^ 40 * 3826236 * 2
def baseEnd_3826236 : Nat := 218299796170733007528163

theorem tailTrace_3826236 : CollatzResearch.WordTrace tailWord_3826236 prefixEnd_3826236 218299796170733007528163 := by
  unfold tailWord_3826236
  simp only [CollatzResearch.WordTrace]
  refine ⟨69777145883103957964289281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93036194510805277285719041 69777145883103957964289281)
  ·
    refine ⟨52332859412327968473216961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69777145883103957964289281 52332859412327968473216961)
    ·
      refine ⟨39249644559245976354912721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52332859412327968473216961 39249644559245976354912721)
      ·
        refine ⟨29437233419434482266184541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39249644559245976354912721 29437233419434482266184541)
        ·
          refine ⟨11038962532287930849819203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29437233419434482266184541 11038962532287930849819203)
          ·
            refine ⟨16558443798431896274728805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11038962532287930849819203 16558443798431896274728805)
            ·
              refine ⟨3104708212205980551511651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16558443798431896274728805 3104708212205980551511651)
              ·
                refine ⟨4657062318308970827267477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104708212205980551511651 4657062318308970827267477)
                ·
                  refine ⟨218299796170733007528163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4657062318308970827267477 218299796170733007528163)
                  ·
                    rfl

theorem cell23_3826236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_3826236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826236 prefixEnd_3826236 := by exact prefixLift 3826236
  have htrace : WordTrace (prefixWord ++ tailWord_3826236) baseStart_3826236 baseEnd_3826236 := by
    simpa [prefixWord, tailWord_3826236, baseEnd_3826236] using wordTrace_append hprefix tailTrace_3826236
  have hstable : (prefixWord ++ tailWord_3826236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826236).length < 2 ^ (prefixWord ++ tailWord_3826236).sum := by decide
  have hdescent : baseEnd_3826236 < baseStart_3826236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826263 : List Nat := [1, 1, 3, 2, 2, 2, 2, 5, 1, 1, 3]
def baseStart_3826263 : Nat := 118140960795 + 3826263 * 2 ^ 59
def prefixEnd_3826263 : Nat := 4983230072969 + 3 ^ 40 * 3826263 * 2
def baseEnd_3826263 : Nat := 1964712029514268462115843

theorem tailTrace_3826263 : CollatzResearch.WordTrace tailWord_3826263 prefixEnd_3826263 1964712029514268462115843 := by
  unfold tailWord_3826263
  simp only [CollatzResearch.WordTrace]
  refine ⟨139555276537110099539811443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93036851024740066359874295 139555276537110099539811443)
  ·
    refine ⟨209332914805665149309717165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139555276537110099539811443 209332914805665149309717165)
    ·
      refine ⟨78499843052124430991143937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209332914805665149309717165 78499843052124430991143937)
      ·
        refine ⟨58874882289093323243357953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78499843052124430991143937 58874882289093323243357953)
        ·
          refine ⟨44156161716819992432518465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58874882289093323243357953 44156161716819992432518465)
          ·
            refine ⟨33117121287614994324388849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44156161716819992432518465 33117121287614994324388849)
            ·
              refine ⟨24837840965711245743291637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33117121287614994324388849 24837840965711245743291637)
              ·
                refine ⟨2328547590535429288433591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24837840965711245743291637 2328547590535429288433591)
                ·
                  refine ⟨3492821385803143932650387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328547590535429288433591 3492821385803143932650387)
                  ·
                    refine ⟨5239232078704715898975581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3492821385803143932650387 5239232078704715898975581)
                    ·
                      refine ⟨1964712029514268462115843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5239232078704715898975581 1964712029514268462115843)
                      ·
                        rfl

theorem cell23_3826263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_3826263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826263 prefixEnd_3826263 := by exact prefixLift 3826263
  have htrace : WordTrace (prefixWord ++ tailWord_3826263) baseStart_3826263 baseEnd_3826263 := by
    simpa [prefixWord, tailWord_3826263, baseEnd_3826263] using wordTrace_append hprefix tailTrace_3826263
  have hstable : (prefixWord ++ tailWord_3826263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826263).length < 2 ^ (prefixWord ++ tailWord_3826263).sum := by decide
  have hdescent : baseEnd_3826263 < baseStart_3826263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826274 : List Nat := [3, 3, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_3826274 : Nat := 118140960795 + 3826274 * 2 ^ 59
def prefixEnd_3826274 : Nat := 4983230072969 + 3 ^ 40 * 3826274 * 2
def baseEnd_3826274 : Nat := 654905892600489306359431

theorem tailTrace_3826274 : CollatzResearch.WordTrace tailWord_3826274 prefixEnd_3826274 654905892600489306359431 := by
  unfold tailWord_3826274
  simp only [CollatzResearch.WordTrace]
  refine ⟨34888919435017562104615469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93037118493380165612307917 34888919435017562104615469)
  ·
    refine ⟨13083344788131585789230801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34888919435017562104615469 13083344788131585789230801)
    ·
      refine ⟨9812508591098689341923101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13083344788131585789230801 9812508591098689341923101)
      ·
        refine ⟨3679690721662008503221163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9812508591098689341923101 3679690721662008503221163)
        ·
          refine ⟨5519536082493012754831745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679690721662008503221163 5519536082493012754831745)
          ·
            refine ⟨4139652061869759566123809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5519536082493012754831745 4139652061869759566123809)
            ·
              refine ⟨3104739046402319674592857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4139652061869759566123809 3104739046402319674592857)
              ·
                refine ⟨2328554284801739755944643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3104739046402319674592857 2328554284801739755944643)
                ·
                  refine ⟨3492831427202609633916965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328554284801739755944643 3492831427202609633916965)
                  ·
                    refine ⟨654905892600489306359431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3492831427202609633916965 654905892600489306359431)
                    ·
                      rfl

theorem cell23_3826274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_3826274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826274 prefixEnd_3826274 := by exact prefixLift 3826274
  have htrace : WordTrace (prefixWord ++ tailWord_3826274) baseStart_3826274 baseEnd_3826274 := by
    simpa [prefixWord, tailWord_3826274, baseEnd_3826274] using wordTrace_append hprefix tailTrace_3826274
  have hstable : (prefixWord ++ tailWord_3826274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826274).length < 2 ^ (prefixWord ++ tailWord_3826274).sum := by decide
  have hdescent : baseEnd_3826274 < baseStart_3826274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826286 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3826286 : Nat := 118140960795 + 3826286 * 2 ^ 59
def prefixEnd_3826286 : Nat := 4983230072969 + 3 ^ 40 * 3826286 * 2
def baseEnd_3826286 : Nat := 1964723839569321872128237

theorem tailTrace_3826286 : CollatzResearch.WordTrace tailWord_3826286 prefixEnd_3826286 1964723839569321872128237 := by
  unfold tailWord_3826286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17444514427003346808487339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93037410277351182978599141 17444514427003346808487339)
  ·
    refine ⟨26166771640505020212731009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17444514427003346808487339 26166771640505020212731009)
    ·
      refine ⟨19625078730378765159548257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26166771640505020212731009 19625078730378765159548257)
      ·
        refine ⟨14718809047784073869661193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19625078730378765159548257 14718809047784073869661193)
        ·
          refine ⟨11039106785838055402245895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14718809047784073869661193 11039106785838055402245895)
          ·
            refine ⟨16558660178757083103368843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11039106785838055402245895 16558660178757083103368843)
            ·
              refine ⟨24837990268135624655053265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16558660178757083103368843 24837990268135624655053265)
              ·
                refine ⟨18628492701101718491289949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24837990268135624655053265 18628492701101718491289949)
                ·
                  refine ⟨6985684762913144434233731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18628492701101718491289949 6985684762913144434233731)
                  ·
                    refine ⟨10478527144369716651350597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6985684762913144434233731 10478527144369716651350597)
                    ·
                      refine ⟨1964723839569321872128237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10478527144369716651350597 1964723839569321872128237)
                      ·
                        rfl

theorem cell23_3826286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3826286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826286 prefixEnd_3826286 := by exact prefixLift 3826286
  have htrace : WordTrace (prefixWord ++ tailWord_3826286) baseStart_3826286 baseEnd_3826286 := by
    simpa [prefixWord, tailWord_3826286, baseEnd_3826286] using wordTrace_append hprefix tailTrace_3826286
  have hstable : (prefixWord ++ tailWord_3826286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826286).length < 2 ^ (prefixWord ++ tailWord_3826286).sum := by decide
  have hdescent : baseEnd_3826286 < baseStart_3826286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826350 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3826350 : Nat := 118140960795 + 3826350 * 2 ^ 59
def prefixEnd_3826350 : Nat := 4983230072969 + 3 ^ 40 * 3826350 * 2
def baseEnd_3826350 : Nat := 1964756702331209621727943

theorem tailTrace_3826350 : CollatzResearch.WordTrace tailWord_3826350 prefixEnd_3826350 1964756702331209621727943 := by
  unfold tailWord_3826350
  simp only [CollatzResearch.WordTrace]
  refine ⟨17444806210974364174778563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93038966458529942265485669 17444806210974364174778563)
  ·
    refine ⟨26167209316461546262167845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17444806210974364174778563 26167209316461546262167845)
    ·
      refine ⟨4906351746836539924156471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26167209316461546262167845 4906351746836539924156471)
      ·
        refine ⟨7359527620254809886234707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4906351746836539924156471 7359527620254809886234707)
        ·
          refine ⟨11039291430382214829352061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7359527620254809886234707 11039291430382214829352061)
          ·
            refine ⟨4139734286393330561007023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11039291430382214829352061 4139734286393330561007023)
            ·
              refine ⟨6209601429589995841510535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4139734286393330561007023 6209601429589995841510535)
              ·
                refine ⟨9314402144384993762265803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209601429589995841510535 9314402144384993762265803)
                ·
                  refine ⟨13971603216577490643398705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9314402144384993762265803 13971603216577490643398705)
                  ·
                    refine ⟨10478702412433117982549029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13971603216577490643398705 10478702412433117982549029)
                    ·
                      refine ⟨1964756702331209621727943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10478702412433117982549029 1964756702331209621727943)
                      ·
                        rfl

theorem cell23_3826350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3826350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826350 prefixEnd_3826350 := by exact prefixLift 3826350
  have htrace : WordTrace (prefixWord ++ tailWord_3826350) baseStart_3826350 baseEnd_3826350 := by
    simpa [prefixWord, tailWord_3826350, baseEnd_3826350] using wordTrace_append hprefix tailTrace_3826350
  have hstable : (prefixWord ++ tailWord_3826350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826350).length < 2 ^ (prefixWord ++ tailWord_3826350).sum := by decide
  have hdescent : baseEnd_3826350 < baseStart_3826350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826379 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 3]
def baseStart_3826379 : Nat := 118140960795 + 3826379 * 2 ^ 59
def prefixEnd_3826379 : Nat := 4983230072969 + 3 ^ 40 * 3826379 * 2
def baseEnd_3826379 : Nat := 1964771593270190008265309

theorem tailTrace_3826379 : CollatzResearch.WordTrace tailWord_3826379 prefixEnd_3826379 1964771593270190008265309 := by
  unfold tailWord_3826379
  simp only [CollatzResearch.WordTrace]
  refine ⟨139559507404689851351034191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93039671603126567567356127 139559507404689851351034191)
  ·
    refine ⟨209339261107034777026551287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139559507404689851351034191 209339261107034777026551287)
    ·
      refine ⟨314008891660552165539826931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209339261107034777026551287 314008891660552165539826931)
      ·
        refine ⟨471013337490828248309740397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314008891660552165539826931 471013337490828248309740397)
        ·
          refine ⟨176630001559060593116152649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471013337490828248309740397 176630001559060593116152649)
          ·
            refine ⟨132472501169295444837114487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176630001559060593116152649 132472501169295444837114487)
            ·
              refine ⟨198708751753943167255671731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132472501169295444837114487 198708751753943167255671731)
              ·
                refine ⟨298063127630914750883507597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198708751753943167255671731 298063127630914750883507597)
                ·
                  refine ⟨111773672861593031581315349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298063127630914750883507597 111773672861593031581315349)
                  ·
                    refine ⟨5239390915387173355374157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111773672861593031581315349 5239390915387173355374157)
                    ·
                      refine ⟨1964771593270190008265309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5239390915387173355374157 1964771593270190008265309)
                      ·
                        rfl

theorem cell23_3826379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 3].length) (baseStart_3826379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826379 prefixEnd_3826379 := by exact prefixLift 3826379
  have htrace : WordTrace (prefixWord ++ tailWord_3826379) baseStart_3826379 baseEnd_3826379 := by
    simpa [prefixWord, tailWord_3826379, baseEnd_3826379] using wordTrace_append hprefix tailTrace_3826379
  have hstable : (prefixWord ++ tailWord_3826379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826379).length < 2 ^ (prefixWord ++ tailWord_3826379).sum := by decide
  have hdescent : baseEnd_3826379 < baseStart_3826379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826380 : List Nat := [2, 2, 1, 5, 1, 1, 2, 3, 1, 3, 2]
def baseStart_3826380 : Nat := 118140960795 + 3826380 * 2 ^ 59
def prefixEnd_3826380 : Nat := 4983230072969 + 3 ^ 40 * 3826380 * 2
def baseEnd_3826380 : Nat := 1964772106750844504352805

theorem tailTrace_3826380 : CollatzResearch.WordTrace tailWord_3826380 prefixEnd_3826380 1964772106750844504352805 := by
  unfold tailWord_3826380
  simp only [CollatzResearch.WordTrace]
  refine ⟨69779771938843114260910297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93039695918457485681213729 69779771938843114260910297)
  ·
    refine ⟨52334828954132335695682723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69779771938843114260910297 52334828954132335695682723)
    ·
      refine ⟨78502243431198503543524085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52334828954132335695682723 78502243431198503543524085)
      ·
        refine ⟨7359585321674859707205383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78502243431198503543524085 7359585321674859707205383)
        ·
          refine ⟨11039377982512289560808075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7359585321674859707205383 11039377982512289560808075)
          ·
            refine ⟨16559066973768434341212113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11039377982512289560808075 16559066973768434341212113)
            ·
              refine ⟨12419300230326325755909085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16559066973768434341212113 12419300230326325755909085)
              ·
                refine ⟨4657237586372372158465907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12419300230326325755909085 4657237586372372158465907)
                ·
                  refine ⟨6985856379558558237698861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4657237586372372158465907 6985856379558558237698861)
                  ·
                    refine ⟨2619696142334459339137073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6985856379558558237698861 2619696142334459339137073)
                    ·
                      refine ⟨1964772106750844504352805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2619696142334459339137073 1964772106750844504352805)
                      ·
                        rfl

theorem cell23_3826380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_3826380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826380 prefixEnd_3826380 := by exact prefixLift 3826380
  have htrace : WordTrace (prefixWord ++ tailWord_3826380) baseStart_3826380 baseEnd_3826380 := by
    simpa [prefixWord, tailWord_3826380, baseEnd_3826380] using wordTrace_append hprefix tailTrace_3826380
  have hstable : (prefixWord ++ tailWord_3826380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826380).length < 2 ^ (prefixWord ++ tailWord_3826380).sum := by decide
  have hdescent : baseEnd_3826380 < baseStart_3826380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826393 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 4, 2, 2]
def baseStart_3826393 : Nat := 118140960795 + 3826393 * 2 ^ 59
def prefixEnd_3826393 : Nat := 4983230072969 + 3 ^ 40 * 3826393 * 2
def baseEnd_3826393 : Nat := 1964778781999352953490245

theorem tailTrace_3826393 : CollatzResearch.WordTrace tailWord_3826393 prefixEnd_3826393 1964778781999352953490245 := by
  unfold tailWord_3826393
  simp only [CollatzResearch.WordTrace]
  refine ⟨139560018026639131742043833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93040012017759421161362555 139560018026639131742043833)
  ·
    refine ⟨104670013519979348806532875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139560018026639131742043833 104670013519979348806532875)
    ·
      refine ⟨157005020279969023209799313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104670013519979348806532875 157005020279969023209799313)
      ·
        refine ⟨117753765209976767407349485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157005020279969023209799313 117753765209976767407349485)
        ·
          refine ⟨44157661953741287777756057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117753765209976767407349485 44157661953741287777756057)
          ·
            refine ⟨33118246465305965833317043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44157661953741287777756057 33118246465305965833317043)
            ·
              refine ⟨49677369697958948749975565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33118246465305965833317043 49677369697958948749975565)
              ·
                refine ⟨18629013636734605781240837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49677369697958948749975565 18629013636734605781240837)
                ·
                  refine ⟨3492940056887738583982657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18629013636734605781240837 3492940056887738583982657)
                  ·
                    refine ⟨2619705042665803937986993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3492940056887738583982657 2619705042665803937986993)
                    ·
                      refine ⟨1964778781999352953490245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2619705042665803937986993 1964778781999352953490245)
                      ·
                        rfl

theorem cell23_3826393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 2, 2].length) (baseStart_3826393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826393 prefixEnd_3826393 := by exact prefixLift 3826393
  have htrace : WordTrace (prefixWord ++ tailWord_3826393) baseStart_3826393 baseEnd_3826393 := by
    simpa [prefixWord, tailWord_3826393, baseEnd_3826393] using wordTrace_append hprefix tailTrace_3826393
  have hstable : (prefixWord ++ tailWord_3826393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826393).length < 2 ^ (prefixWord ++ tailWord_3826393).sum := by decide
  have hdescent : baseEnd_3826393 < baseStart_3826393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826479 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 6]
def baseStart_3826479 : Nat := 118140960795 + 3826479 * 2 ^ 59
def prefixEnd_3826479 : Nat := 4983230072969 + 3 ^ 40 * 3826479 * 2
def baseEnd_3826479 : Nat := 1964822941335639617014849

theorem tailTrace_3826479 : CollatzResearch.WordTrace tailWord_3826479 prefixEnd_3826479 1964822941335639617014849 := by
  unfold tailWord_3826479
  simp only [CollatzResearch.WordTrace]
  refine ⟨139563154704327568429674491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93042103136218378953116327 139563154704327568429674491)
  ·
    refine ⟨209344732056491352644511737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139563154704327568429674491 209344732056491352644511737)
    ·
      refine ⟨157008549042368514483383803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209344732056491352644511737 157008549042368514483383803)
      ·
        refine ⟨235512823563552771725075705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157008549042368514483383803 235512823563552771725075705)
        ·
          refine ⟨176634617672664578793806779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235512823563552771725075705 176634617672664578793806779)
          ·
            refine ⟨264951926508996868190710169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176634617672664578793806779 264951926508996868190710169)
            ·
              refine ⟨198713944881747651143032627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264951926508996868190710169 198713944881747651143032627)
              ·
                refine ⟨298070917322621476714548941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198713944881747651143032627 298070917322621476714548941)
                ·
                  refine ⟨111776593995983053767955853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298070917322621476714548941 111776593995983053767955853)
                  ·
                    refine ⟨41916222748493645162983445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111776593995983053767955853 41916222748493645162983445)
                    ·
                      refine ⟨1964822941335639617014849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41916222748493645162983445 1964822941335639617014849)
                      ·
                        rfl

theorem cell23_3826479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_3826479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826479 prefixEnd_3826479 := by exact prefixLift 3826479
  have htrace : WordTrace (prefixWord ++ tailWord_3826479) baseStart_3826479 baseEnd_3826479 := by
    simpa [prefixWord, tailWord_3826479, baseEnd_3826479] using wordTrace_append hprefix tailTrace_3826479
  have hstable : (prefixWord ++ tailWord_3826479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826479).length < 2 ^ (prefixWord ++ tailWord_3826479).sum := by decide
  have hdescent : baseEnd_3826479 < baseStart_3826479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826483 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 4]
def baseStart_3826483 : Nat := 118140960795 + 3826483 * 2 ^ 59
def prefixEnd_3826483 : Nat := 4983230072969 + 3 ^ 40 * 3826483 * 2
def baseEnd_3826483 : Nat := 1964824995258257601364831

theorem tailTrace_3826483 : CollatzResearch.WordTrace tailWord_3826483 prefixEnd_3826483 1964824995258257601364831 := by
  unfold tailWord_3826483
  simp only [CollatzResearch.WordTrace]
  refine ⟨139563300596313077112820103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93042200397542051408546735 139563300596313077112820103)
  ·
    refine ⟨209344950894469615669230155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139563300596313077112820103 209344950894469615669230155)
    ·
      refine ⟨314017426341704423503845233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209344950894469615669230155 314017426341704423503845233)
      ·
        refine ⟨235513069756278317627883925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314017426341704423503845233 235513069756278317627883925)
        ·
          refine ⟨11039675144825546138807059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235513069756278317627883925 11039675144825546138807059)
          ·
            refine ⟨16559512717238319208210589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11039675144825546138807059 16559512717238319208210589)
            ·
              refine ⟨6209817268964369703078971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16559512717238319208210589 6209817268964369703078971)
              ·
                refine ⟨9314725903446554554618457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209817268964369703078971 9314725903446554554618457)
                ·
                  refine ⟨6986044427584915915963843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9314725903446554554618457 6986044427584915915963843)
                  ·
                    refine ⟨10479066641377373873945765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6986044427584915915963843 10479066641377373873945765)
                    ·
                      refine ⟨1964824995258257601364831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10479066641377373873945765 1964824995258257601364831)
                      ·
                        rfl

theorem cell23_3826483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 4].length) (baseStart_3826483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826483 prefixEnd_3826483 := by exact prefixLift 3826483
  have htrace : WordTrace (prefixWord ++ tailWord_3826483) baseStart_3826483 baseEnd_3826483 := by
    simpa [prefixWord, tailWord_3826483, baseEnd_3826483] using wordTrace_append hprefix tailTrace_3826483
  have hstable : (prefixWord ++ tailWord_3826483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826483).length < 2 ^ (prefixWord ++ tailWord_3826483).sum := by decide
  have hdescent : baseEnd_3826483 < baseStart_3826483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826506 : List Nat := [3, 1, 2, 1, 1, 1, 2, 6, 6]
def baseStart_3826506 : Nat := 118140960795 + 3826506 * 2 ^ 59
def prefixEnd_3826506 : Nat := 4983230072969 + 3 ^ 40 * 3826506 * 2
def baseEnd_3826506 : Nat := 218315200590367890153025

theorem tailTrace_3826506 : CollatzResearch.WordTrace tailWord_3826506 prefixEnd_3826506 218315200590367890153025 := by
  unfold tailWord_3826506
  simp only [CollatzResearch.WordTrace]
  refine ⟨34891034868807438010226843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93042759650153168027271581 34891034868807438010226843)
  ·
    refine ⟨52336552303211157015340265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34891034868807438010226843 52336552303211157015340265)
    ·
      refine ⟨39252414227408367761505199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52336552303211157015340265 39252414227408367761505199)
      ·
        refine ⟨58878621341112551642257799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39252414227408367761505199 58878621341112551642257799)
        ·
          refine ⟨88317932011668827463386699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58878621341112551642257799 88317932011668827463386699)
          ·
            refine ⟨132476898017503241195080049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88317932011668827463386699 132476898017503241195080049)
            ·
              refine ⟨99357673513127430896310037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132476898017503241195080049 99357673513127430896310037)
              ·
                refine ⟨4657390945927848323264533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99357673513127430896310037 4657390945927848323264533)
                ·
                  refine ⟨218315200590367890153025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4657390945927848323264533 218315200590367890153025)
                  ·
                    rfl

theorem cell23_3826506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_3826506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826506 prefixEnd_3826506 := by exact prefixLift 3826506
  have htrace : WordTrace (prefixWord ++ tailWord_3826506) baseStart_3826506 baseEnd_3826506 := by
    simpa [prefixWord, tailWord_3826506, baseEnd_3826506] using wordTrace_append hprefix tailTrace_3826506
  have hstable : (prefixWord ++ tailWord_3826506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826506).length < 2 ^ (prefixWord ++ tailWord_3826506).sum := by decide
  have hdescent : baseEnd_3826506 < baseStart_3826506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826543 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 6, 3, 2]
def baseStart_3826543 : Nat := 118140960795 + 3826543 * 2 ^ 59
def prefixEnd_3826543 : Nat := 4983230072969 + 3 ^ 40 * 3826543 * 2
def baseEnd_3826543 : Nat := 1964855804097527366614555

theorem tailTrace_3826543 : CollatzResearch.WordTrace tailWord_3826543 prefixEnd_3826543 1964855804097527366614555 := by
  unfold tailWord_3826543
  simp only [CollatzResearch.WordTrace]
  refine ⟨139565488976095707360004283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93043659317397138240002855 139565488976095707360004283)
  ·
    refine ⟨209348233464143561040006425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139565488976095707360004283 209348233464143561040006425)
    ·
      refine ⟨157011175098107670780004819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209348233464143561040006425 157011175098107670780004819)
      ·
        refine ⟨235516762647161506170007229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157011175098107670780004819 235516762647161506170007229)
        ·
          refine ⟨88318785992685564813752711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235516762647161506170007229 88318785992685564813752711)
          ·
            refine ⟨132478178989028347220629067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88318785992685564813752711 132478178989028347220629067)
            ·
              refine ⟨198717268483542520830943601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132478178989028347220629067 198717268483542520830943601)
              ·
                refine ⟨149037951362656890623207701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198717268483542520830943601 149037951362656890623207701)
                ·
                  refine ⟨6986153970124541747962861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149037951362656890623207701 6986153970124541747962861)
                  ·
                    refine ⟨2619807738796703155486073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6986153970124541747962861 2619807738796703155486073)
                    ·
                      refine ⟨1964855804097527366614555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2619807738796703155486073 1964855804097527366614555)
                      ·
                        rfl

theorem cell23_3826543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 3, 2].length) (baseStart_3826543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826543 prefixEnd_3826543 := by exact prefixLift 3826543
  have htrace : WordTrace (prefixWord ++ tailWord_3826543) baseStart_3826543 baseEnd_3826543 := by
    simpa [prefixWord, tailWord_3826543, baseEnd_3826543] using wordTrace_append hprefix tailTrace_3826543
  have hstable : (prefixWord ++ tailWord_3826543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826543).length < 2 ^ (prefixWord ++ tailWord_3826543).sum := by decide
  have hdescent : baseEnd_3826543 < baseStart_3826543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826553 : List Nat := [1, 2, 1, 3, 2, 3, 2, 3, 1, 5]
def baseStart_3826553 : Nat := 118140960795 + 3826553 * 2 ^ 59
def prefixEnd_3826553 : Nat := 4983230072969 + 3 ^ 40 * 3826553 * 2
def baseEnd_3826553 : Nat := 654953646301357442496503

theorem tailTrace_3826553 : CollatzResearch.WordTrace tailWord_3826553 prefixEnd_3826553 654953646301357442496503 := by
  unfold tailWord_3826553
  simp only [CollatzResearch.WordTrace]
  refine ⟨139565853706059479067868313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93043902470706319378578875 139565853706059479067868313)
  ·
    refine ⟨104674390279544609300901235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139565853706059479067868313 104674390279544609300901235)
    ·
      refine ⟨157011585419316913951351853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104674390279544609300901235 157011585419316913951351853)
      ·
        refine ⟨58879344532243842731756945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157011585419316913951351853 58879344532243842731756945)
        ·
          refine ⟨44159508399182882048817709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58879344532243842731756945 44159508399182882048817709)
          ·
            refine ⟨16559815649693580768306641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44159508399182882048817709 16559815649693580768306641)
            ·
              refine ⟨12419861737270185576229981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16559815649693580768306641 12419861737270185576229981)
              ·
                refine ⟨4657448151476319591086243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12419861737270185576229981 4657448151476319591086243)
                ·
                  refine ⟨6986172227214479386629365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4657448151476319591086243 6986172227214479386629365)
                  ·
                    refine ⟨654953646301357442496503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6986172227214479386629365 654953646301357442496503)
                    ·
                      rfl

theorem cell23_3826553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 5].length) (baseStart_3826553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826553 prefixEnd_3826553 := by exact prefixLift 3826553
  have htrace : WordTrace (prefixWord ++ tailWord_3826553) baseStart_3826553 baseEnd_3826553 := by
    simpa [prefixWord, tailWord_3826553, baseEnd_3826553] using wordTrace_append hprefix tailTrace_3826553
  have hstable : (prefixWord ++ tailWord_3826553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826553).length < 2 ^ (prefixWord ++ tailWord_3826553).sum := by decide
  have hdescent : baseEnd_3826553 < baseStart_3826553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826567 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_3826567 : Nat := 118140960795 + 3826567 * 2 ^ 59
def prefixEnd_3826567 : Nat := 4983230072969 + 3 ^ 40 * 3826567 * 2
def baseEnd_3826567 : Nat := 1964868127633235272714445

theorem tailTrace_3826567 : CollatzResearch.WordTrace tailWord_3826567 prefixEnd_3826567 1964868127633235272714445 := by
  unfold tailWord_3826567
  simp only [CollatzResearch.WordTrace]
  refine ⟨139566364328008759458877955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93044242885339172972585303 139566364328008759458877955)
  ·
    refine ⟨209349546492013139188316933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139566364328008759458877955 209349546492013139188316933)
    ·
      refine ⟨39253039967252463597809425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209349546492013139188316933 39253039967252463597809425)
      ·
        refine ⟨29439779975439347698357069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39253039967252463597809425 29439779975439347698357069)
        ·
          refine ⟨11039917490789755386883901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29439779975439347698357069 11039917490789755386883901)
          ·
            refine ⟨4139969059046158270081463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11039917490789755386883901 4139969059046158270081463)
            ·
              refine ⟨6209953588569237405122195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4139969059046158270081463 6209953588569237405122195)
              ·
                refine ⟨9314930382853856107683293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209953588569237405122195 9314930382853856107683293)
                ·
                  refine ⟨3493098893570196040381235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9314930382853856107683293 3493098893570196040381235)
                  ·
                    refine ⟨5239648340355294060571853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3493098893570196040381235 5239648340355294060571853)
                    ·
                      refine ⟨1964868127633235272714445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5239648340355294060571853 1964868127633235272714445)
                      ·
                        rfl

theorem cell23_3826567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_3826567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826567 prefixEnd_3826567 := by exact prefixLift 3826567
  have htrace : WordTrace (prefixWord ++ tailWord_3826567) baseStart_3826567 baseEnd_3826567 := by
    simpa [prefixWord, tailWord_3826567, baseEnd_3826567] using wordTrace_append hprefix tailTrace_3826567
  have hstable : (prefixWord ++ tailWord_3826567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826567).length < 2 ^ (prefixWord ++ tailWord_3826567).sum := by decide
  have hdescent : baseEnd_3826567 < baseStart_3826567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826596 : List Nat := [2, 3, 1, 2, 1, 2, 1, 11]
def baseStart_3826596 : Nat := 118140960795 + 3826596 * 2 ^ 59
def prefixEnd_3826596 : Nat := 4983230072969 + 3 ^ 40 * 3826596 * 2
def baseEnd_3826596 : Nat := 72773445132304283675993

theorem tailTrace_3826596 : CollatzResearch.WordTrace tailWord_3826596 prefixEnd_3826596 72773445132304283675993 := by
  unfold tailWord_3826596
  simp only [CollatzResearch.WordTrace]
  refine ⟨69783711022451848705841821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93044948029935798274455761 69783711022451848705841821)
  ·
    refine ⟨26168891633419443264690683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69783711022451848705841821 26168891633419443264690683)
    ·
      refine ⟨39253337450129164897036025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26168891633419443264690683 39253337450129164897036025)
      ·
        refine ⟨29440003087596873672777019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39253337450129164897036025 29440003087596873672777019)
        ·
          refine ⟨44160004631395310509165529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29440003087596873672777019 44160004631395310509165529)
          ·
            refine ⟨33120003473546482881874147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44160004631395310509165529 33120003473546482881874147)
            ·
              refine ⟨49680005210319724322811221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33120003473546482881874147 49680005210319724322811221)
              ·
                refine ⟨72773445132304283675993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 49680005210319724322811221 72773445132304283675993)
                ·
                  rfl

theorem cell23_3826596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 11].length) (baseStart_3826596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826596 prefixEnd_3826596 := by exact prefixLift 3826596
  have htrace : WordTrace (prefixWord ++ tailWord_3826596) baseStart_3826596 baseEnd_3826596 := by
    simpa [prefixWord, tailWord_3826596, baseEnd_3826596] using wordTrace_append hprefix tailTrace_3826596
  have hstable : (prefixWord ++ tailWord_3826596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826596).length < 2 ^ (prefixWord ++ tailWord_3826596).sum := by decide
  have hdescent : baseEnd_3826596 < baseStart_3826596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826624 : List Nat := [2, 1, 1, 2, 3, 4, 1, 4, 1, 2, 2]
def baseStart_3826624 : Nat := 118140960795 + 3826624 * 2 ^ 59
def prefixEnd_3826624 : Nat := 4983230072969 + 3 ^ 40 * 3826624 * 2
def baseEnd_3826624 : Nat := 1964897396030541549701683

theorem tailTrace_3826624 : CollatzResearch.WordTrace tailWord_3826624 prefixEnd_3826624 1964897396030541549701683 := by
  unfold tailWord_3826624
  simp only [CollatzResearch.WordTrace]
  refine ⟨69784221644401129096851463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93045628859201505462468617 69784221644401129096851463)
  ·
    refine ⟨104676332466601693645277195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69784221644401129096851463 104676332466601693645277195)
    ·
      refine ⟨157014498699902540467915793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104676332466601693645277195 157014498699902540467915793)
      ·
        refine ⟨117760874024926905350936845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157014498699902540467915793 117760874024926905350936845)
        ·
          refine ⟨44160327759347589506601317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117760874024926905350936845 44160327759347589506601317)
          ·
            refine ⟨8280061454877673032487747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44160327759347589506601317 8280061454877673032487747)
            ·
              refine ⟨12420092182316509548731621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8280061454877673032487747 12420092182316509548731621)
              ·
                refine ⟨2328767284184345540387179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12420092182316509548731621 2328767284184345540387179)
                ·
                  refine ⟨3493150926276518310580769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328767284184345540387179 3493150926276518310580769)
                  ·
                    refine ⟨2619863194707388732935577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3493150926276518310580769 2619863194707388732935577)
                    ·
                      refine ⟨1964897396030541549701683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2619863194707388732935577 1964897396030541549701683)
                      ·
                        rfl

theorem cell23_3826624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 1, 2, 2].length) (baseStart_3826624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826624 prefixEnd_3826624 := by exact prefixLift 3826624
  have htrace : WordTrace (prefixWord ++ tailWord_3826624) baseStart_3826624 baseEnd_3826624 := by
    simpa [prefixWord, tailWord_3826624, baseEnd_3826624] using wordTrace_append hprefix tailTrace_3826624
  have hstable : (prefixWord ++ tailWord_3826624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826624).length < 2 ^ (prefixWord ++ tailWord_3826624).sum := by decide
  have hdescent : baseEnd_3826624 < baseStart_3826624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826633 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 1, 9, 2]
def baseStart_3826633 : Nat := 118140960795 + 3826633 * 2 ^ 59
def prefixEnd_3826633 : Nat := 4983230072969 + 3 ^ 40 * 3826633 * 2
def baseEnd_3826633 : Nat := 1964902017356432014489141

theorem tailTrace_3826633 : CollatzResearch.WordTrace tailWord_3826633 prefixEnd_3826633 1964902017356432014489141 := by
  unfold tailWord_3826633
  simp only [CollatzResearch.WordTrace]
  refine ⟨139568771545769652730780553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93045847697179768487187035 139568771545769652730780553)
  ·
    refine ⟨104676578659327239548085415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139568771545769652730780553 104676578659327239548085415)
    ·
      refine ⟨157014867988990859322128123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104676578659327239548085415 157014867988990859322128123)
      ·
        refine ⟨235522301983486288983192185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157014867988990859322128123 235522301983486288983192185)
        ·
          refine ⟨176641726487614716737394139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235522301983486288983192185 176641726487614716737394139)
          ·
            refine ⟨264962589731422075106091209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176641726487614716737394139 264962589731422075106091209)
            ·
              refine ⟨198721942298566556329568407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264962589731422075106091209 198721942298566556329568407)
              ·
                refine ⟨298082913447849834494352611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198721942298566556329568407 298082913447849834494352611)
                ·
                  refine ⟨447124370171774751741528917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298082913447849834494352611 447124370171774751741528917)
                  ·
                    refine ⟨2619869356475242685985521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 447124370171774751741528917 2619869356475242685985521)
                    ·
                      refine ⟨1964902017356432014489141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2619869356475242685985521 1964902017356432014489141)
                      ·
                        rfl

theorem cell23_3826633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 9, 2].length) (baseStart_3826633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826633 prefixEnd_3826633 := by exact prefixLift 3826633
  have htrace : WordTrace (prefixWord ++ tailWord_3826633) baseStart_3826633 baseEnd_3826633 := by
    simpa [prefixWord, tailWord_3826633, baseEnd_3826633] using wordTrace_append hprefix tailTrace_3826633
  have hstable : (prefixWord ++ tailWord_3826633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826633).length < 2 ^ (prefixWord ++ tailWord_3826633).sum := by decide
  have hdescent : baseEnd_3826633 < baseStart_3826633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826658 : List Nat := [3, 3, 3, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_3826658 : Nat := 118140960795 + 3826658 * 2 ^ 59
def prefixEnd_3826658 : Nat := 4983230072969 + 3 ^ 40 * 3826658 * 2
def baseEnd_3826658 : Nat := 1964914854372794416676527

theorem tailTrace_3826658 : CollatzResearch.WordTrace tailWord_3826658 prefixEnd_3826658 1964914854372794416676527 := by
  unfold tailWord_3826658
  simp only [CollatzResearch.WordTrace]
  refine ⟨34892420842669770500110157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93046455580452721333627085 34892420842669770500110157)
  ·
    refine ⟨13084657816001163937541309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34892420842669770500110157 13084657816001163937541309)
    ·
      refine ⟨4906746681000436476577991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13084657816001163937541309 4906746681000436476577991)
      ·
        refine ⟨7360120021500654714866987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4906746681000436476577991 7360120021500654714866987)
        ·
          refine ⟨11040180032250982072300481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7360120021500654714866987 11040180032250982072300481)
          ·
            refine ⟨8280135024188236554225361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11040180032250982072300481 8280135024188236554225361)
            ·
              refine ⟨6210101268141177415669021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8280135024188236554225361 6210101268141177415669021)
              ·
                refine ⟨2328787975552941530875883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6210101268141177415669021 2328787975552941530875883)
                ·
                  refine ⟨3493181963329412296313825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328787975552941530875883 3493181963329412296313825)
                  ·
                    refine ⟨2619886472497059222235369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3493181963329412296313825 2619886472497059222235369)
                    ·
                      refine ⟨1964914854372794416676527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2619886472497059222235369 1964914854372794416676527)
                      ·
                        rfl

theorem cell23_3826658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_3826658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826658 prefixEnd_3826658 := by exact prefixLift 3826658
  have htrace : WordTrace (prefixWord ++ tailWord_3826658) baseStart_3826658 baseEnd_3826658 := by
    simpa [prefixWord, tailWord_3826658, baseEnd_3826658] using wordTrace_append hprefix tailTrace_3826658
  have hstable : (prefixWord ++ tailWord_3826658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826658).length < 2 ^ (prefixWord ++ tailWord_3826658).sum := by decide
  have hdescent : baseEnd_3826658 < baseStart_3826658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826661 : List Nat := [1, 3, 1, 6, 1, 2, 2, 1, 1, 2, 3]
def baseStart_3826661 : Nat := 118140960795 + 3826661 * 2 ^ 59
def prefixEnd_3826661 : Nat := 4983230072969 + 3 ^ 40 * 3826661 * 2
def baseEnd_3826661 : Nat := 1964916394814757904939013

theorem tailTrace_3826661 : CollatzResearch.WordTrace tailWord_3826661 prefixEnd_3826661 1964916394814757904939013 := by
  unfold tailWord_3826661
  simp only [CollatzResearch.WordTrace]
  refine ⟨139569792789668213512799837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93046528526445475675199891 139569792789668213512799837)
  ·
    refine ⟨52338672296125580067299939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139569792789668213512799837 52338672296125580067299939)
    ·
      refine ⟨78508008444188370100949909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52338672296125580067299939 78508008444188370100949909)
      ·
        refine ⟨3680062895821329848482027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78508008444188370100949909 3680062895821329848482027)
        ·
          refine ⟨5520094343731994772723041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680062895821329848482027 5520094343731994772723041)
          ·
            refine ⟨4140070757798996079542281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5520094343731994772723041 4140070757798996079542281)
            ·
              refine ⟨3105053068349247059656711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4140070757798996079542281 3105053068349247059656711)
              ·
                refine ⟨4657579602523870589485067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105053068349247059656711 4657579602523870589485067)
                ·
                  refine ⟨6986369403785805884227601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4657579602523870589485067 6986369403785805884227601)
                  ·
                    refine ⟨5239777052839354413170701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6986369403785805884227601 5239777052839354413170701)
                    ·
                      refine ⟨1964916394814757904939013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5239777052839354413170701 1964916394814757904939013)
                      ·
                        rfl

theorem cell23_3826661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_3826661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826661 prefixEnd_3826661 := by exact prefixLift 3826661
  have htrace : WordTrace (prefixWord ++ tailWord_3826661) baseStart_3826661 baseEnd_3826661 := by
    simpa [prefixWord, tailWord_3826661, baseEnd_3826661] using wordTrace_append hprefix tailTrace_3826661
  have hstable : (prefixWord ++ tailWord_3826661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826661).length < 2 ^ (prefixWord ++ tailWord_3826661).sum := by decide
  have hdescent : baseEnd_3826661 < baseStart_3826661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826673 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 2, 6]
def baseStart_3826673 : Nat := 118140960795 + 3826673 * 2 ^ 59
def prefixEnd_3826673 : Nat := 4983230072969 + 3 ^ 40 * 3826673 * 2
def baseEnd_3826673 : Nat := 654974185527537285996319

theorem tailTrace_3826673 : CollatzResearch.WordTrace tailWord_3826673 prefixEnd_3826673 654974185527537285996319 := by
  unfold tailWord_3826673
  simp only [CollatzResearch.WordTrace]
  refine ⟨139570230465624739562236673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93046820310416493041491115 139570230465624739562236673)
  ·
    refine ⟨104677672849218554671677505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139570230465624739562236673 104677672849218554671677505)
    ·
      refine ⟨78508254636913916003758129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104677672849218554671677505 78508254636913916003758129)
      ·
        refine ⟨58881190977685437002818597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78508254636913916003758129 58881190977685437002818597)
        ·
          refine ⟨11040223308316019438028487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58881190977685437002818597 11040223308316019438028487)
          ·
            refine ⟨16560334962474029157042731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11040223308316019438028487 16560334962474029157042731)
            ·
              refine ⟨24840502443711043735564097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16560334962474029157042731 24840502443711043735564097)
              ·
                refine ⟨18630376832783282801673073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24840502443711043735564097 18630376832783282801673073)
                ·
                  refine ⟨13972782624587462101254805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18630376832783282801673073 13972782624587462101254805)
                  ·
                    refine ⟨654974185527537285996319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13972782624587462101254805 654974185527537285996319)
                    ·
                      rfl

theorem cell23_3826673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_3826673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826673 prefixEnd_3826673 := by exact prefixLift 3826673
  have htrace : WordTrace (prefixWord ++ tailWord_3826673) baseStart_3826673 baseEnd_3826673 := by
    simpa [prefixWord, tailWord_3826673, baseEnd_3826673] using wordTrace_append hprefix tailTrace_3826673
  have hstable : (prefixWord ++ tailWord_3826673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826673).length < 2 ^ (prefixWord ++ tailWord_3826673).sum := by decide
  have hdescent : baseEnd_3826673 < baseStart_3826673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826674 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3826674 : Nat := 118140960795 + 3826674 * 2 ^ 59
def prefixEnd_3826674 : Nat := 4983230072969 + 3 ^ 40 * 3826674 * 2
def baseEnd_3826674 : Nat := 1964923070063266354076453

theorem tailTrace_3826674 : CollatzResearch.WordTrace tailWord_3826674 prefixEnd_3826674 1964923070063266354076453 := by
  unfold tailWord_3826674
  simp only [CollatzResearch.WordTrace]
  refine ⟨34892566734655279183255769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93046844625747411155348717 34892566734655279183255769)
  ·
    refine ⟨26169425050991459387441827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34892566734655279183255769 26169425050991459387441827)
    ·
      refine ⟨39254137576487189081162741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26169425050991459387441827 39254137576487189081162741)
      ·
        refine ⟨3680075397795673976359007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39254137576487189081162741 3680075397795673976359007)
        ·
          refine ⟨5520113096693510964538511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680075397795673976359007 5520113096693510964538511)
          ·
            refine ⟨8280169645040266446807767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5520113096693510964538511 8280169645040266446807767)
            ·
              refine ⟨12420254467560399670211651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8280169645040266446807767 12420254467560399670211651)
              ·
                refine ⟨18630381701340599505317477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12420254467560399670211651 18630381701340599505317477)
                ·
                  refine ⟨3493196569001362407247027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18630381701340599505317477 3493196569001362407247027)
                  ·
                    refine ⟨5239794853502043610870541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3493196569001362407247027 5239794853502043610870541)
                    ·
                      refine ⟨1964923070063266354076453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5239794853502043610870541 1964923070063266354076453)
                      ·
                        rfl

theorem cell23_3826674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3826674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826674 prefixEnd_3826674 := by exact prefixLift 3826674
  have htrace : WordTrace (prefixWord ++ tailWord_3826674) baseStart_3826674 baseEnd_3826674 := by
    simpa [prefixWord, tailWord_3826674, baseEnd_3826674] using wordTrace_append hprefix tailTrace_3826674
  have hstable : (prefixWord ++ tailWord_3826674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826674).length < 2 ^ (prefixWord ++ tailWord_3826674).sum := by decide
  have hdescent : baseEnd_3826674 < baseStart_3826674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826693 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_3826693 : Nat := 118140960795 + 3826693 * 2 ^ 59
def prefixEnd_3826693 : Nat := 4983230072969 + 3 ^ 40 * 3826693 * 2
def baseEnd_3826693 : Nat := 1964932826195701779738865

theorem tailTrace_3826693 : CollatzResearch.WordTrace tailWord_3826693 prefixEnd_3826693 1964932826195701779738865 := by
  unfold tailWord_3826693
  simp only [CollatzResearch.WordTrace]
  refine ⟨139570959925552282977964733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93047306617034855318643155 139570959925552282977964733)
  ·
    refine ⟨52339109972082106116736775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139570959925552282977964733 52339109972082106116736775)
    ·
      refine ⟨78508664958123159175105163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52339109972082106116736775 78508664958123159175105163)
      ·
        refine ⟨117762997437184738762657745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78508664958123159175105163 117762997437184738762657745)
        ·
          refine ⟨88322248077888554071993309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117762997437184738762657745 88322248077888554071993309)
          ·
            refine ⟨33120843029208207776997491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88322248077888554071993309 33120843029208207776997491)
            ·
              refine ⟨49681264543812311665496237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33120843029208207776997491 49681264543812311665496237)
              ·
                refine ⟨18630474203929616874561089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49681264543812311665496237 18630474203929616874561089)
                ·
                  refine ⟨13972855652947212655920817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18630474203929616874561089 13972855652947212655920817)
                  ·
                    refine ⟨10479641739710409491940613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13972855652947212655920817 10479641739710409491940613)
                    ·
                      refine ⟨1964932826195701779738865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10479641739710409491940613 1964932826195701779738865)
                      ·
                        rfl

theorem cell23_3826693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_3826693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826693 prefixEnd_3826693 := by exact prefixLift 3826693
  have htrace : WordTrace (prefixWord ++ tailWord_3826693) baseStart_3826693 baseEnd_3826693 := by
    simpa [prefixWord, tailWord_3826693, baseEnd_3826693] using wordTrace_append hprefix tailTrace_3826693
  have hstable : (prefixWord ++ tailWord_3826693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826693).length < 2 ^ (prefixWord ++ tailWord_3826693).sum := by decide
  have hdescent : baseEnd_3826693 < baseStart_3826693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826697 : List Nat := [1, 2, 1, 1, 3, 1, 1, 7, 2, 2, 2]
def baseStart_3826697 : Nat := 118140960795 + 3826697 * 2 ^ 59
def prefixEnd_3826697 : Nat := 4983230072969 + 3 ^ 40 * 3826697 * 2
def baseEnd_3826697 : Nat := 1964934880118319764088847

theorem tailTrace_3826697 : CollatzResearch.WordTrace tailWord_3826697 prefixEnd_3826697 1964934880118319764088847 := by
  unfold tailWord_3826697
  simp only [CollatzResearch.WordTrace]
  refine ⟨139571105817537791661110345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93047403878358527774073563 139571105817537791661110345)
  ·
    refine ⟨104678329363153343745832759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139571105817537791661110345 104678329363153343745832759)
    ·
      refine ⟨157017494044730015618749139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104678329363153343745832759 157017494044730015618749139)
      ·
        refine ⟨235526241067095023428123709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157017494044730015618749139 235526241067095023428123709)
        ·
          refine ⟨88322340400160633785546391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235526241067095023428123709 88322340400160633785546391)
          ·
            refine ⟨132483510600240950678319587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88322340400160633785546391 132483510600240950678319587)
            ·
              refine ⟨198725265900361426017479381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132483510600240950678319587 198725265900361426017479381)
              ·
                refine ⟨4657623419539720922284673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 198725265900361426017479381 4657623419539720922284673)
                ·
                  refine ⟨3493217564654790691713505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4657623419539720922284673 3493217564654790691713505)
                  ·
                    refine ⟨2619913173491093018785129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3493217564654790691713505 2619913173491093018785129)
                    ·
                      refine ⟨1964934880118319764088847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2619913173491093018785129 1964934880118319764088847)
                      ·
                        rfl

theorem cell23_3826697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 2, 2].length) (baseStart_3826697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826697 prefixEnd_3826697 := by exact prefixLift 3826697
  have htrace : WordTrace (prefixWord ++ tailWord_3826697) baseStart_3826697 baseEnd_3826697 := by
    simpa [prefixWord, tailWord_3826697, baseEnd_3826697] using wordTrace_append hprefix tailTrace_3826697
  have hstable : (prefixWord ++ tailWord_3826697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826697).length < 2 ^ (prefixWord ++ tailWord_3826697).sum := by decide
  have hdescent : baseEnd_3826697 < baseStart_3826697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826713 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 1, 5, 3]
def baseStart_3826713 : Nat := 118140960795 + 3826713 * 2 ^ 59
def prefixEnd_3826713 : Nat := 4983230072969 + 3 ^ 40 * 3826713 * 2
def baseEnd_3826713 : Nat := 1964943095808791701488773

theorem tailTrace_3826713 : CollatzResearch.WordTrace tailWord_3826713 prefixEnd_3826713 1964943095808791701488773 := by
  unfold tailWord_3826713
  simp only [CollatzResearch.WordTrace]
  refine ⟨139571689385479826393692793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93047792923653217595795195 139571689385479826393692793)
  ·
    refine ⟨104678767039109869795269595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139571689385479826393692793 104678767039109869795269595)
    ·
      refine ⟨157018150558664804692904393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104678767039109869795269595 157018150558664804692904393)
      ·
        refine ⟨117763612918998603519678295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157018150558664804692904393 117763612918998603519678295)
        ·
          refine ⟨176645419378497905279517443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117763612918998603519678295 176645419378497905279517443)
          ·
            refine ⟨264968129067746857919276165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176645419378497905279517443 264968129067746857919276165)
            ·
              refine ⟨49681524200202535859864281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264968129067746857919276165 49681524200202535859864281)
              ·
                refine ⟨37261143150151901894898211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49681524200202535859864281 37261143150151901894898211)
                ·
                  refine ⟨55891714725227852842347317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37261143150151901894898211 55891714725227852842347317)
                  ·
                    refine ⟨5239848255490111203970061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55891714725227852842347317 5239848255490111203970061)
                    ·
                      refine ⟨1964943095808791701488773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5239848255490111203970061 1964943095808791701488773)
                      ·
                        rfl

theorem cell23_3826713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_3826713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826713 prefixEnd_3826713 := by exact prefixLift 3826713
  have htrace : WordTrace (prefixWord ++ tailWord_3826713) baseStart_3826713 baseEnd_3826713 := by
    simpa [prefixWord, tailWord_3826713, baseEnd_3826713] using wordTrace_append hprefix tailTrace_3826713
  have hstable : (prefixWord ++ tailWord_3826713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826713).length < 2 ^ (prefixWord ++ tailWord_3826713).sum := by decide
  have hdescent : baseEnd_3826713 < baseStart_3826713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826737 : List Nat := [1, 2, 2, 3, 1, 2, 5, 2, 5]
def baseStart_3826737 : Nat := 118140960795 + 3826737 * 2 ^ 59
def prefixEnd_3826737 : Nat := 4983230072969 + 3 ^ 40 * 3826737 * 2
def baseEnd_3826737 : Nat := 218328379927166623065407

theorem tailTrace_3826737 : CollatzResearch.WordTrace tailWord_3826737 prefixEnd_3826737 218328379927166623065407 := by
  unfold tailWord_3826737
  simp only [CollatzResearch.WordTrace]
  refine ⟨139572564737392878492566465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93048376491595252328377643 139572564737392878492566465)
  ·
    refine ⟨104679423553044658869424849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139572564737392878492566465 104679423553044658869424849)
    ·
      refine ⟨78509567664783494152068637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104679423553044658869424849 78509567664783494152068637)
      ·
        refine ⟨29441087874293810307025739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78509567664783494152068637 29441087874293810307025739)
        ·
          refine ⟨44161631811440715460538609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29441087874293810307025739 44161631811440715460538609)
          ·
            refine ⟨33121223858580536595403957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44161631811440715460538609 33121223858580536595403957)
            ·
              refine ⟨3105114736741925305819121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33121223858580536595403957 3105114736741925305819121)
              ·
                refine ⟨2328836052556443979364341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3105114736741925305819121 2328836052556443979364341)
                ·
                  refine ⟨218328379927166623065407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2328836052556443979364341 218328379927166623065407)
                  ·
                    rfl

theorem cell23_3826737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 5].length) (baseStart_3826737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826737 prefixEnd_3826737 := by exact prefixLift 3826737
  have htrace : WordTrace (prefixWord ++ tailWord_3826737) baseStart_3826737 baseEnd_3826737 := by
    simpa [prefixWord, tailWord_3826737, baseEnd_3826737] using wordTrace_append hprefix tailTrace_3826737
  have hstable : (prefixWord ++ tailWord_3826737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826737).length < 2 ^ (prefixWord ++ tailWord_3826737).sum := by decide
  have hdescent : baseEnd_3826737 < baseStart_3826737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826783 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 6]
def baseStart_3826783 : Nat := 118140960795 + 3826783 * 2 ^ 59
def prefixEnd_3826783 : Nat := 4983230072969 + 3 ^ 40 * 3826783 * 2
def baseEnd_3826783 : Nat := 1964979039454606427613451

theorem tailTrace_3826783 : CollatzResearch.WordTrace tailWord_3826783 prefixEnd_3826783 1964979039454606427613451 := by
  unfold tailWord_3826783
  simp only [CollatzResearch.WordTrace]
  refine ⟨139574242495226228348741003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93049494996817485565827335 139574242495226228348741003)
  ·
    refine ⟨209361363742839342523111505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139574242495226228348741003 209361363742839342523111505)
    ·
      refine ⟨157021022807129506892333629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209361363742839342523111505 157021022807129506892333629)
      ·
        refine ⟨58882883552673565084625111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157021022807129506892333629 58882883552673565084625111)
        ·
          refine ⟨88324325329010347626937667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58882883552673565084625111 88324325329010347626937667)
          ·
            refine ⟨132486487993515521440406501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88324325329010347626937667 132486487993515521440406501)
            ·
              refine ⟨24841216498784160270076219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132486487993515521440406501 24841216498784160270076219)
              ·
                refine ⟨37261824748176240405114329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24841216498784160270076219 37261824748176240405114329)
                ·
                  refine ⟨27946368561132180303835747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37261824748176240405114329 27946368561132180303835747)
                  ·
                    refine ⟨41919552841698270455753621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27946368561132180303835747 41919552841698270455753621)
                    ·
                      refine ⟨1964979039454606427613451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41919552841698270455753621 1964979039454606427613451)
                      ·
                        rfl

theorem cell23_3826783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_3826783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826783 prefixEnd_3826783 := by exact prefixLift 3826783
  have htrace : WordTrace (prefixWord ++ tailWord_3826783) baseStart_3826783 baseEnd_3826783 := by
    simpa [prefixWord, tailWord_3826783, baseEnd_3826783] using wordTrace_append hprefix tailTrace_3826783
  have hstable : (prefixWord ++ tailWord_3826783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826783).length < 2 ^ (prefixWord ++ tailWord_3826783).sum := by decide
  have hdescent : baseEnd_3826783 < baseStart_3826783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826860 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_3826860 : Nat := 118140960795 + 3826860 * 2 ^ 59
def prefixEnd_3826860 : Nat := 4983230072969 + 3 ^ 40 * 3826860 * 2
def baseEnd_3826860 : Nat := 1965018577465002626350597

theorem tailTrace_3826860 : CollatzResearch.WordTrace tailWord_3826860 prefixEnd_3826860 1965018577465002626350597 := by
  unfold tailWord_3826860
  simp only [CollatzResearch.WordTrace]
  refine ⟨69788525457973635249647017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93051367277298180332862689 69788525457973635249647017)
  ·
    refine ⟨52341394093480226437235263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69788525457973635249647017 52341394093480226437235263)
    ·
      refine ⟨78512091140220339655852895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52341394093480226437235263 78512091140220339655852895)
      ·
        refine ⟨117768136710330509483779343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78512091140220339655852895 117768136710330509483779343)
        ·
          refine ⟨176652205065495764225669015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117768136710330509483779343 176652205065495764225669015)
          ·
            refine ⟨264978307598243646338503523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176652205065495764225669015 264978307598243646338503523)
            ·
              refine ⟨397467461397365469507755285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264978307598243646338503523 397467461397365469507755285)
              ·
                refine ⟨18631287253001506383176029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 397467461397365469507755285 18631287253001506383176029)
                ·
                  refine ⟨6986732719875564893691011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18631287253001506383176029 6986732719875564893691011)
                  ·
                    refine ⟨10480099079813347340536517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6986732719875564893691011 10480099079813347340536517)
                    ·
                      refine ⟨1965018577465002626350597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10480099079813347340536517 1965018577465002626350597)
                      ·
                        rfl

theorem cell23_3826860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_3826860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826860 prefixEnd_3826860 := by exact prefixLift 3826860
  have htrace : WordTrace (prefixWord ++ tailWord_3826860) baseStart_3826860 baseEnd_3826860 := by
    simpa [prefixWord, tailWord_3826860, baseEnd_3826860] using wordTrace_append hprefix tailTrace_3826860
  have hstable : (prefixWord ++ tailWord_3826860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826860).length < 2 ^ (prefixWord ++ tailWord_3826860).sum := by decide
  have hdescent : baseEnd_3826860 < baseStart_3826860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826877 : List Nat := [1, 4, 1, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_3826877 : Nat := 118140960795 + 3826877 * 2 ^ 59
def prefixEnd_3826877 : Nat := 4983230072969 + 3 ^ 40 * 3826877 * 2
def baseEnd_3826877 : Nat := 1965027306636129059838019

theorem tailTrace_3826877 : CollatzResearch.WordTrace tailWord_3826877 prefixEnd_3826877 1965027306636129059838019 := by
  unfold tailWord_3826877
  simp only [CollatzResearch.WordTrace]
  refine ⟨139577670956885682402662885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93051780637923788268441923 139577670956885682402662885)
  ·
    refine ⟨26170813304416065450499291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139577670956885682402662885 26170813304416065450499291)
    ·
      refine ⟨39256219956624098175748937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26170813304416065450499291 39256219956624098175748937)
      ·
        refine ⟨29442164967468073631811703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39256219956624098175748937 29442164967468073631811703)
        ·
          refine ⟨44163247451202110447717555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29442164967468073631811703 44163247451202110447717555)
          ·
            refine ⟨66244871176803165671576333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44163247451202110447717555 66244871176803165671576333)
            ·
              refine ⟨24841826691301187126841125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66244871176803165671576333 24841826691301187126841125)
              ·
                refine ⟨4657842504618972586282711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24841826691301187126841125 4657842504618972586282711)
                ·
                  refine ⟨6986763756928458879424067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4657842504618972586282711 6986763756928458879424067)
                  ·
                    refine ⟨10480145635392688319136101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6986763756928458879424067 10480145635392688319136101)
                    ·
                      refine ⟨1965027306636129059838019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10480145635392688319136101 1965027306636129059838019)
                      ·
                        rfl

theorem cell23_3826877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_3826877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826877 prefixEnd_3826877 := by exact prefixLift 3826877
  have htrace : WordTrace (prefixWord ++ tailWord_3826877) baseStart_3826877 baseEnd_3826877 := by
    simpa [prefixWord, tailWord_3826877, baseEnd_3826877] using wordTrace_append hprefix tailTrace_3826877
  have hstable : (prefixWord ++ tailWord_3826877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826877).length < 2 ^ (prefixWord ++ tailWord_3826877).sum := by decide
  have hdescent : baseEnd_3826877 < baseStart_3826877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826882 : List Nat := [3, 5, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3826882 : Nat := 118140960795 + 3826882 * 2 ^ 59
def prefixEnd_3826882 : Nat := 4983230072969 + 3 ^ 40 * 3826882 * 2
def baseEnd_3826882 : Nat := 655009958013133846758499

theorem tailTrace_3826882 : CollatzResearch.WordTrace tailWord_3826882 prefixEnd_3826882 655009958013133846758499 := by
  unfold tailWord_3826882
  simp only [CollatzResearch.WordTrace]
  refine ⟨34894463330466892064148725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93051902214578378837729933 34894463330466892064148725)
  ·
    refine ⟨3271355937231271131013943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34894463330466892064148725 3271355937231271131013943)
    ·
      refine ⟨4907033905846906696520915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3271355937231271131013943 4907033905846906696520915)
      ·
        refine ⟨7360550858770360044781373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4907033905846906696520915 7360550858770360044781373)
        ·
          refine ⟨2760206572038885016793015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7360550858770360044781373 2760206572038885016793015)
          ·
            refine ⟨4140309858058327525189523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760206572038885016793015 4140309858058327525189523)
            ·
              refine ⟨6210464787087491287784285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4140309858058327525189523 6210464787087491287784285)
              ·
                refine ⟨2328924295157809232919107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6210464787087491287784285 2328924295157809232919107)
                ·
                  refine ⟨3493386442736713849378661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328924295157809232919107 3493386442736713849378661)
                  ·
                    refine ⟨655009958013133846758499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3493386442736713849378661 655009958013133846758499)
                    ·
                      rfl

theorem cell23_3826882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3826882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826882 prefixEnd_3826882 := by exact prefixLift 3826882
  have htrace : WordTrace (prefixWord ++ tailWord_3826882) baseStart_3826882 baseEnd_3826882 := by
    simpa [prefixWord, tailWord_3826882, baseEnd_3826882] using wordTrace_append hprefix tailTrace_3826882
  have hstable : (prefixWord ++ tailWord_3826882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826882).length < 2 ^ (prefixWord ++ tailWord_3826882).sum := by decide
  have hdescent : baseEnd_3826882 < baseStart_3826882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826911 : List Nat := [1, 1, 2, 3, 2, 1, 2, 6, 1, 2, 2]
def baseStart_3826911 : Nat := 118140960795 + 3826911 * 2 ^ 59
def prefixEnd_3826911 : Nat := 4983230072969 + 3 ^ 40 * 3826911 * 2
def baseEnd_3826911 : Nat := 1965044764978381926812863

theorem tailTrace_3826911 : CollatzResearch.WordTrace tailWord_3826911 prefixEnd_3826911 1965044764978381926812863 := by
  unfold tailWord_3826911
  simp only [CollatzResearch.WordTrace]
  refine ⟨139578911038762506209400587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93052607359175004139600391 139578911038762506209400587)
  ·
    refine ⟨209368366558143759314100881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139578911038762506209400587 209368366558143759314100881)
    ·
      refine ⟨157026274918607819485575661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209368366558143759314100881 157026274918607819485575661)
      ·
        refine ⟨58884853094477932307090873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157026274918607819485575661 58884853094477932307090873)
        ·
          refine ⟨44163639820858449230318155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58884853094477932307090873 44163639820858449230318155)
          ·
            refine ⟨66245459731287673845477233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44163639820858449230318155 66245459731287673845477233)
            ·
              refine ⟨49684094798465755384107925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66245459731287673845477233 49684094798465755384107925)
              ·
                refine ⟨2328941943678082283630059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49684094798465755384107925 2328941943678082283630059)
                ·
                  refine ⟨3493412915517123425445089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328941943678082283630059 3493412915517123425445089)
                  ·
                    refine ⟨2620059686637842569083817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3493412915517123425445089 2620059686637842569083817)
                    ·
                      refine ⟨1965044764978381926812863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2620059686637842569083817 1965044764978381926812863)
                      ·
                        rfl

theorem cell23_3826911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_3826911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826911 prefixEnd_3826911 := by exact prefixLift 3826911
  have htrace : WordTrace (prefixWord ++ tailWord_3826911) baseStart_3826911 baseEnd_3826911 := by
    simpa [prefixWord, tailWord_3826911, baseEnd_3826911] using wordTrace_append hprefix tailTrace_3826911
  have hstable : (prefixWord ++ tailWord_3826911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826911).length < 2 ^ (prefixWord ++ tailWord_3826911).sum := by decide
  have hdescent : baseEnd_3826911 < baseStart_3826911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826917 : List Nat := [1, 3, 1, 4, 3, 1, 2, 8]
def baseStart_3826917 : Nat := 118140960795 + 3826917 * 2 ^ 59
def prefixEnd_3826917 : Nat := 4983230072969 + 3 ^ 40 * 3826917 * 2
def baseEnd_3826917 : Nat := 72779549846752181605105

theorem tailTrace_3826917 : CollatzResearch.WordTrace tailWord_3826917 prefixEnd_3826917 72779549846752181605105 := by
  unfold tailWord_3826917
  simp only [CollatzResearch.WordTrace]
  refine ⟨139579129876740769234119005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93052753251160512822746003 139579129876740769234119005)
  ·
    refine ⟨52342173703777788462794627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139579129876740769234119005 52342173703777788462794627)
    ·
      refine ⟨78513260555666682694191941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52342173703777788462794627 78513260555666682694191941)
      ·
        refine ⟨14721236354187503005160989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78513260555666682694191941 14721236354187503005160989)
        ·
          refine ⟨5520463632820313626935371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14721236354187503005160989 5520463632820313626935371)
          ·
            refine ⟨8280695449230470440403057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5520463632820313626935371 8280695449230470440403057)
            ·
              refine ⟨6210521586922852830302293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8280695449230470440403057 6210521586922852830302293)
              ·
                refine ⟨72779549846752181605105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6210521586922852830302293 72779549846752181605105)
                ·
                  rfl

theorem cell23_3826917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 8].length) (baseStart_3826917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826917 prefixEnd_3826917 := by exact prefixLift 3826917
  have htrace : WordTrace (prefixWord ++ tailWord_3826917) baseStart_3826917 baseEnd_3826917 := by
    simpa [prefixWord, tailWord_3826917, baseEnd_3826917] using wordTrace_append hprefix tailTrace_3826917
  have hstable : (prefixWord ++ tailWord_3826917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826917).length < 2 ^ (prefixWord ++ tailWord_3826917).sum := by decide
  have hdescent : baseEnd_3826917 < baseStart_3826917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826920 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3826920 : Nat := 118140960795 + 3826920 * 2 ^ 59
def prefixEnd_3826920 : Nat := 4983230072969 + 3 ^ 40 * 3826920 * 2
def baseEnd_3826920 : Nat := 1965049386304272391600321

theorem tailTrace_3826920 : CollatzResearch.WordTrace tailWord_3826920 prefixEnd_3826920 1965049386304272391600321 := by
  unfold tailWord_3826920
  simp only [CollatzResearch.WordTrace]
  refine ⟨69789619647864950373239107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93052826197153267164318809 69789619647864950373239107)
  ·
    refine ⟨104684429471797425559858661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69789619647864950373239107 104684429471797425559858661)
    ·
      refine ⟨19628330525962017292473499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104684429471797425559858661 19628330525962017292473499)
      ·
        refine ⟨29442495788943025938710249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19628330525962017292473499 29442495788943025938710249)
        ·
          refine ⟨22081871841707269454032687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29442495788943025938710249 22081871841707269454032687)
          ·
            refine ⟨33122807762560904181049031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22081871841707269454032687 33122807762560904181049031)
            ·
              refine ⟨49684211643841356271573547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33122807762560904181049031 49684211643841356271573547)
              ·
                refine ⟨74526317465762034407360321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49684211643841356271573547 74526317465762034407360321)
                ·
                  refine ⟨55894738099321525805520241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74526317465762034407360321 55894738099321525805520241)
                  ·
                    refine ⟨41921053574491144354140181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55894738099321525805520241 41921053574491144354140181)
                    ·
                      refine ⟨1965049386304272391600321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41921053574491144354140181 1965049386304272391600321)
                      ·
                        rfl

theorem cell23_3826920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3826920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826920 prefixEnd_3826920 := by exact prefixLift 3826920
  have htrace : WordTrace (prefixWord ++ tailWord_3826920) baseStart_3826920 baseEnd_3826920 := by
    simpa [prefixWord, tailWord_3826920, baseEnd_3826920] using wordTrace_append hprefix tailTrace_3826920
  have hstable : (prefixWord ++ tailWord_3826920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826920).length < 2 ^ (prefixWord ++ tailWord_3826920).sum := by decide
  have hdescent : baseEnd_3826920 < baseStart_3826920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826962 : List Nat := [3, 2, 4, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3826962 : Nat := 118140960795 + 3826962 * 2 ^ 59
def prefixEnd_3826962 : Nat := 4983230072969 + 3 ^ 40 * 3826962 * 2
def baseEnd_3826962 : Nat := 1965070952491761227275129

theorem tailTrace_3826962 : CollatzResearch.WordTrace tailWord_3826962 prefixEnd_3826962 1965070952491761227275129 := by
  unfold tailWord_3826962
  simp only [CollatzResearch.WordTrace]
  refine ⟨34895192790394435479876785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93053847441051827946338093 34895192790394435479876785)
  ·
    refine ⟨26171394592795826609907589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34895192790394435479876785 26171394592795826609907589)
    ·
      refine ⟨4907136486149217489357673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26171394592795826609907589 4907136486149217489357673)
      ·
        refine ⟨3680352364611913117018255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4907136486149217489357673 3680352364611913117018255)
        ·
          refine ⟨5520528546917869675527383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680352364611913117018255 5520528546917869675527383)
          ·
            refine ⟨8280792820376804513291075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5520528546917869675527383 8280792820376804513291075)
            ·
              refine ⟨12421189230565206769936613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8280792820376804513291075 12421189230565206769936613)
              ·
                refine ⟨2328972980730976269363115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12421189230565206769936613 2328972980730976269363115)
                ·
                  refine ⟨3493459471096464404044673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328972980730976269363115 3493459471096464404044673)
                  ·
                    refine ⟨2620094603322348303033505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3493459471096464404044673 2620094603322348303033505)
                    ·
                      refine ⟨1965070952491761227275129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2620094603322348303033505 1965070952491761227275129)
                      ·
                        rfl

theorem cell23_3826962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3826962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3826962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3826962 prefixEnd_3826962 := by exact prefixLift 3826962
  have htrace : WordTrace (prefixWord ++ tailWord_3826962) baseStart_3826962 baseEnd_3826962 := by
    simpa [prefixWord, tailWord_3826962, baseEnd_3826962] using wordTrace_append hprefix tailTrace_3826962
  have hstable : (prefixWord ++ tailWord_3826962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826962).length < 2 ^ (prefixWord ++ tailWord_3826962).sum := by decide
  have hdescent : baseEnd_3826962 < baseStart_3826962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827000 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_3827000 : Nat := 118140960795 + 3827000 * 2 ^ 59
def prefixEnd_3827000 : Nat := 4983230072969 + 3 ^ 40 * 3827000 * 2
def baseEnd_3827000 : Nat := 1965090464756632078599953

theorem tailTrace_3827000 : CollatzResearch.WordTrace tailWord_3827000 prefixEnd_3827000 1965090464756632078599953 := by
  unfold tailWord_3827000
  simp only [CollatzResearch.WordTrace]
  refine ⟨69791078567720037204695227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93054771423626716272926969 69791078567720037204695227)
  ·
    refine ⟨104686617851580055807042841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69791078567720037204695227 104686617851580055807042841)
    ·
      refine ⟨78514963388685041855282131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104686617851580055807042841 78514963388685041855282131)
      ·
        refine ⟨117772445083027562782923197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78514963388685041855282131 117772445083027562782923197)
        ·
          refine ⟨44164666906135336043596199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117772445083027562782923197 44164666906135336043596199)
          ·
            refine ⟨66247000359203004065394299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44164666906135336043596199 66247000359203004065394299)
            ·
              refine ⟨99370500538804506098091449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66247000359203004065394299 99370500538804506098091449)
              ·
                refine ⟨74527875404103379573568587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99370500538804506098091449 74527875404103379573568587)
                ·
                  refine ⟨111791813106155069360352881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74527875404103379573568587 111791813106155069360352881)
                  ·
                    refine ⟨83843859829616302020264661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111791813106155069360352881 83843859829616302020264661)
                    ·
                      refine ⟨1965090464756632078599953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83843859829616302020264661 1965090464756632078599953)
                      ·
                        rfl

theorem cell23_3827000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_3827000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827000 prefixEnd_3827000 := by exact prefixLift 3827000
  have htrace : WordTrace (prefixWord ++ tailWord_3827000) baseStart_3827000 baseEnd_3827000 := by
    simpa [prefixWord, tailWord_3827000, baseEnd_3827000] using wordTrace_append hprefix tailTrace_3827000
  have hstable : (prefixWord ++ tailWord_3827000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827000).length < 2 ^ (prefixWord ++ tailWord_3827000).sum := by decide
  have hdescent : baseEnd_3827000 < baseStart_3827000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827017 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 2, 3, 3]
def baseStart_3827017 : Nat := 118140960795 + 3827017 * 2 ^ 59
def prefixEnd_3827017 : Nat := 4983230072969 + 3 ^ 40 * 3827017 * 2
def baseEnd_3827017 : Nat := 1965099193927758512087375

theorem tailTrace_3827017 : CollatzResearch.WordTrace tailWord_3827017 prefixEnd_3827017 1965099193927758512087375 := by
  unfold tailWord_3827017
  simp only [CollatzResearch.WordTrace]
  refine ⟨139582777176378486312759305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93055184784252324208506203 139582777176378486312759305)
  ·
    refine ⟨104687082882283864734569479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139582777176378486312759305 104687082882283864734569479)
    ·
      refine ⟨157030624323425797101854219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104687082882283864734569479 157030624323425797101854219)
      ·
        refine ⟨235545936485138695652781329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157030624323425797101854219 235545936485138695652781329)
        ·
          refine ⟨176659452363854021739585997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235545936485138695652781329 176659452363854021739585997)
          ·
            refine ⟨66247294636445258152344749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176659452363854021739585997 66247294636445258152344749)
            ·
              refine ⟨24842735488666971807129281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66247294636445258152344749 24842735488666971807129281)
              ·
                refine ⟨18632051616500228855346961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24842735488666971807129281 18632051616500228855346961)
                ·
                  refine ⟨13974038712375171641510221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18632051616500228855346961 13974038712375171641510221)
                  ·
                    refine ⟨5240264517140689365566333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13974038712375171641510221 5240264517140689365566333)
                    ·
                      refine ⟨1965099193927758512087375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5240264517140689365566333 1965099193927758512087375)
                      ·
                        rfl

theorem cell23_3827017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 3, 3].length) (baseStart_3827017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827017 prefixEnd_3827017 := by exact prefixLift 3827017
  have htrace : WordTrace (prefixWord ++ tailWord_3827017) baseStart_3827017 baseEnd_3827017 := by
    simpa [prefixWord, tailWord_3827017, baseEnd_3827017] using wordTrace_append hprefix tailTrace_3827017
  have hstable : (prefixWord ++ tailWord_3827017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827017).length < 2 ^ (prefixWord ++ tailWord_3827017).sum := by decide
  have hdescent : baseEnd_3827017 < baseStart_3827017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827057 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_3827057 : Nat := 118140960795 + 3827057 * 2 ^ 59
def prefixEnd_3827057 : Nat := 4983230072969 + 3 ^ 40 * 3827057 * 2
def baseEnd_3827057 : Nat := 1965119733153938355587191

theorem tailTrace_3827057 : CollatzResearch.WordTrace tailWord_3827057 prefixEnd_3827057 1965119733153938355587191 := by
  unfold tailWord_3827057
  simp only [CollatzResearch.WordTrace]
  refine ⟨139584236096233573144215425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93056157397489048762810283 139584236096233573144215425)
  ·
    refine ⟨104688177072175179858161569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139584236096233573144215425 104688177072175179858161569)
    ·
      refine ⟨78516132804131384893621177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104688177072175179858161569 78516132804131384893621177)
      ·
        refine ⟨58887099603098538670215883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78516132804131384893621177 58887099603098538670215883)
        ·
          refine ⟨88330649404647808005323825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58887099603098538670215883 88330649404647808005323825)
          ·
            refine ⟨66247987053485856003992869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88330649404647808005323825 66247987053485856003992869)
            ·
              refine ⟨12421497572528598000748663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66247987053485856003992869 12421497572528598000748663)
              ·
                refine ⟨18632246358792897001122995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12421497572528598000748663 18632246358792897001122995)
                ·
                  refine ⟨27948369538189345501684493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18632246358792897001122995 27948369538189345501684493)
                  ·
                    refine ⟨10480638576821004563131685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27948369538189345501684493 10480638576821004563131685)
                    ·
                      refine ⟨1965119733153938355587191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10480638576821004563131685 1965119733153938355587191)
                      ·
                        rfl

theorem cell23_3827057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_3827057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827057 prefixEnd_3827057 := by exact prefixLift 3827057
  have htrace : WordTrace (prefixWord ++ tailWord_3827057) baseStart_3827057 baseEnd_3827057 := by
    simpa [prefixWord, tailWord_3827057, baseEnd_3827057] using wordTrace_append hprefix tailTrace_3827057
  have hstable : (prefixWord ++ tailWord_3827057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827057).length < 2 ^ (prefixWord ++ tailWord_3827057).sum := by decide
  have hdescent : baseEnd_3827057 < baseStart_3827057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827111 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_3827111 : Nat := 118140960795 + 3827111 * 2 ^ 59
def prefixEnd_3827111 : Nat := 4983230072969 + 3 ^ 40 * 3827111 * 2
def baseEnd_3827111 : Nat := 1965147461109281144311943

theorem tailTrace_3827111 : CollatzResearch.WordTrace tailWord_3827111 prefixEnd_3827111 1965147461109281144311943 := by
  unfold tailWord_3827111
  simp only [CollatzResearch.WordTrace]
  refine ⟨139586205638037940366681187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93057470425358626911120791 139586205638037940366681187)
  ·
    refine ⟨209379308457056910550021781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139586205638037940366681187 209379308457056910550021781)
    ·
      refine ⟨9814655083924542682032271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209379308457056910550021781 9814655083924542682032271)
      ·
        refine ⟨14721982625886814023048407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9814655083924542682032271 14721982625886814023048407)
        ·
          refine ⟨22082973938830221034572611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14721982625886814023048407 22082973938830221034572611)
          ·
            refine ⟨33124460908245331551858917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22082973938830221034572611 33124460908245331551858917)
            ·
              refine ⟨6210836420295999665973547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33124460908245331551858917 6210836420295999665973547)
              ·
                refine ⟨9316254630443999498960321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6210836420295999665973547 9316254630443999498960321)
                ·
                  refine ⟨6987190972832999624220241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9316254630443999498960321 6987190972832999624220241)
                  ·
                    refine ⟨5240393229624749718165181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6987190972832999624220241 5240393229624749718165181)
                    ·
                      refine ⟨1965147461109281144311943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5240393229624749718165181 1965147461109281144311943)
                      ·
                        rfl

theorem cell23_3827111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_3827111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827111 prefixEnd_3827111 := by exact prefixLift 3827111
  have htrace : WordTrace (prefixWord ++ tailWord_3827111) baseStart_3827111 baseEnd_3827111 := by
    simpa [prefixWord, tailWord_3827111, baseEnd_3827111] using wordTrace_append hprefix tailTrace_3827111
  have hstable : (prefixWord ++ tailWord_3827111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827111).length < 2 ^ (prefixWord ++ tailWord_3827111).sum := by decide
  have hdescent : baseEnd_3827111 < baseStart_3827111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827158 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3827158 : Nat := 118140960795 + 3827158 * 2 ^ 59
def prefixEnd_3827158 : Nat := 4983230072969 + 3 ^ 40 * 3827158 * 2
def baseEnd_3827158 : Nat := 1965171594700042460424227

theorem tailTrace_3827158 : CollatzResearch.WordTrace tailWord_3827158 prefixEnd_3827158 1965171594700042460424227 := by
  unfold tailWord_3827158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8724244991804229212102633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93058613245911778262428085 8724244991804229212102633)
  ·
    refine ⟨6543183743853171909076975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8724244991804229212102633 6543183743853171909076975)
    ·
      refine ⟨9814775615779757863615463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6543183743853171909076975 9814775615779757863615463)
      ·
        refine ⟨14722163423669636795423195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9814775615779757863615463 14722163423669636795423195)
        ·
          refine ⟨22083245135504455193134793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14722163423669636795423195 22083245135504455193134793)
          ·
            refine ⟨16562433851628341394851095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22083245135504455193134793 16562433851628341394851095)
            ·
              refine ⟨24843650777442512092276643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16562433851628341394851095 24843650777442512092276643)
              ·
                refine ⟨37265476166163768138414965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24843650777442512092276643 37265476166163768138414965)
                ·
                  refine ⟨3493638390577853262976403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37265476166163768138414965 3493638390577853262976403)
                  ·
                    refine ⟨5240457585866779894464605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3493638390577853262976403 5240457585866779894464605)
                    ·
                      refine ⟨1965171594700042460424227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5240457585866779894464605 1965171594700042460424227)
                      ·
                        rfl

theorem cell23_3827158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3827158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827158 prefixEnd_3827158 := by exact prefixLift 3827158
  have htrace : WordTrace (prefixWord ++ tailWord_3827158) baseStart_3827158 baseEnd_3827158 := by
    simpa [prefixWord, tailWord_3827158, baseEnd_3827158] using wordTrace_append hprefix tailTrace_3827158
  have hstable : (prefixWord ++ tailWord_3827158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827158).length < 2 ^ (prefixWord ++ tailWord_3827158).sum := by decide
  have hdescent : baseEnd_3827158 < baseStart_3827158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827175 : List Nat := [1, 1, 5, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_3827175 : Nat := 118140960795 + 3827175 * 2 ^ 59
def prefixEnd_3827175 : Nat := 4983230072969 + 3 ^ 40 * 3827175 * 2
def baseEnd_3827175 : Nat := 1965180323871168893911649

theorem tailTrace_3827175 : CollatzResearch.WordTrace tailWord_3827175 prefixEnd_3827175 1965180323871168893911649 := by
  unfold tailWord_3827175
  simp only [CollatzResearch.WordTrace]
  refine ⟨139588539909806079297010979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93059026606537386198007319 139588539909806079297010979)
  ·
    refine ⟨209382809864709118945516469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139588539909806079297010979 209382809864709118945516469)
    ·
      refine ⟨19629638424816479901142169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209382809864709118945516469 19629638424816479901142169)
      ·
        refine ⟨14722228818612359925856627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19629638424816479901142169 14722228818612359925856627)
        ·
          refine ⟨22083343227918539888784941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14722228818612359925856627 22083343227918539888784941)
          ·
            refine ⟨8281253710469452458294353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22083343227918539888784941 8281253710469452458294353)
            ·
              refine ⟨6210940282852089343720765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8281253710469452458294353 6210940282852089343720765)
              ·
                refine ⟨2329102606069533503895287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6210940282852089343720765 2329102606069533503895287)
                ·
                  refine ⟨3493653909104300255842931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329102606069533503895287 3493653909104300255842931)
                  ·
                    refine ⟨5240480863656450383764397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3493653909104300255842931 5240480863656450383764397)
                    ·
                      refine ⟨1965180323871168893911649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5240480863656450383764397 1965180323871168893911649)
                      ·
                        rfl

theorem cell23_3827175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_3827175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827175 prefixEnd_3827175 := by exact prefixLift 3827175
  have htrace : WordTrace (prefixWord ++ tailWord_3827175) baseStart_3827175 baseEnd_3827175 := by
    simpa [prefixWord, tailWord_3827175, baseEnd_3827175] using wordTrace_append hprefix tailTrace_3827175
  have hstable : (prefixWord ++ tailWord_3827175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827175).length < 2 ^ (prefixWord ++ tailWord_3827175).sum := by decide
  have hdescent : baseEnd_3827175 < baseStart_3827175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827177 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 2, 6, 4]
def baseStart_3827177 : Nat := 118140960795 + 3827177 * 2 ^ 59
def prefixEnd_3827177 : Nat := 4983230072969 + 3 ^ 40 * 3827177 * 2
def baseEnd_3827177 : Nat := 1965181350832477886086639

theorem tailTrace_3827177 : CollatzResearch.WordTrace tailWord_3827177 prefixEnd_3827177 1965181350832477886086639 := by
  unfold tailWord_3827177
  simp only [CollatzResearch.WordTrace]
  refine ⟨139588612855798833638583785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93059075237199222425722523 139588612855798833638583785)
  ·
    refine ⟨104691459641849125228937839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139588612855798833638583785 104691459641849125228937839)
    ·
      refine ⟨157037189462773687843406759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104691459641849125228937839 157037189462773687843406759)
      ·
        refine ⟨235555784194160531765110139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157037189462773687843406759 235555784194160531765110139)
        ·
          refine ⟨353333676291240797647665209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235555784194160531765110139 353333676291240797647665209)
          ·
            refine ⟨265000257218430598235748907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353333676291240797647665209 265000257218430598235748907)
            ·
              refine ⟨397500385827645897353623361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265000257218430598235748907 397500385827645897353623361)
              ·
                refine ⟨298125289370734423015217521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397500385827645897353623361 298125289370734423015217521)
                ·
                  refine ⟨223593967028050817261413141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298125289370734423015217521 223593967028050817261413141)
                  ·
                    refine ⟨10480967204439882059128741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 223593967028050817261413141 10480967204439882059128741)
                    ·
                      refine ⟨1965181350832477886086639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10480967204439882059128741 1965181350832477886086639)
                      ·
                        rfl

theorem cell23_3827177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_3827177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827177 prefixEnd_3827177 := by exact prefixLift 3827177
  have htrace : WordTrace (prefixWord ++ tailWord_3827177) baseStart_3827177 baseEnd_3827177 := by
    simpa [prefixWord, tailWord_3827177, baseEnd_3827177] using wordTrace_append hprefix tailTrace_3827177
  have hstable : (prefixWord ++ tailWord_3827177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827177).length < 2 ^ (prefixWord ++ tailWord_3827177).sum := by decide
  have hdescent : baseEnd_3827177 < baseStart_3827177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827201 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_3827201 : Nat := 118140960795 + 3827201 * 2 ^ 59
def prefixEnd_3827201 : Nat := 4983230072969 + 3 ^ 40 * 3827201 * 2
def baseEnd_3827201 : Nat := 1965193674368185792186529

theorem tailTrace_3827201 : CollatzResearch.WordTrace tailWord_3827201 prefixEnd_3827201 1965193674368185792186529 := by
  unfold tailWord_3827201
  simp only [CollatzResearch.WordTrace]
  refine ⟨139589488207711885737457457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93059658805141257158304971 139589488207711885737457457)
  ·
    refine ⟨104692116155783914303093093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139589488207711885737457457 104692116155783914303093093)
    ·
      refine ⟨19629771779209483931829955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104692116155783914303093093 19629771779209483931829955)
      ·
        refine ⟨29444657668814225897744933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19629771779209483931829955 29444657668814225897744933)
        ·
          refine ⟨5520873312902667355827175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29444657668814225897744933 5520873312902667355827175)
          ·
            refine ⟨8281309969354001033740763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5520873312902667355827175 8281309969354001033740763)
            ·
              refine ⟨12421964954031001550611145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8281309969354001033740763 12421964954031001550611145)
              ·
                refine ⟨9316473715523251162958359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12421964954031001550611145 9316473715523251162958359)
                ·
                  refine ⟨13974710573284876744437539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9316473715523251162958359 13974710573284876744437539)
                  ·
                    refine ⟨20962065859927315116656309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13974710573284876744437539 20962065859927315116656309)
                    ·
                      refine ⟨1965193674368185792186529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20962065859927315116656309 1965193674368185792186529)
                      ·
                        rfl

theorem cell23_3827201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_3827201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827201 prefixEnd_3827201 := by exact prefixLift 3827201
  have htrace : WordTrace (prefixWord ++ tailWord_3827201) baseStart_3827201 baseEnd_3827201 := by
    simpa [prefixWord, tailWord_3827201, baseEnd_3827201] using wordTrace_append hprefix tailTrace_3827201
  have hstable : (prefixWord ++ tailWord_3827201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827201).length < 2 ^ (prefixWord ++ tailWord_3827201).sum := by decide
  have hdescent : baseEnd_3827201 < baseStart_3827201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827221 : List Nat := [1, 3, 2, 1, 3, 4, 2, 7]
def baseStart_3827221 : Nat := 118140960795 + 3827221 * 2 ^ 59
def prefixEnd_3827221 : Nat := 4983230072969 + 3 ^ 40 * 3827221 * 2
def baseEnd_3827221 : Nat := 72785331258565767182831

theorem tailTrace_3827221 : CollatzResearch.WordTrace tailWord_3827221 prefixEnd_3827221 72785331258565767182831 := by
  unfold tailWord_3827221
  simp only [CollatzResearch.WordTrace]
  refine ⟨139590217667639429153185517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93060145111759619435457011 139590217667639429153185517)
  ·
    refine ⟨52346331625364785932444569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139590217667639429153185517 52346331625364785932444569)
    ·
      refine ⟨39259748719023589449333427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52346331625364785932444569 39259748719023589449333427)
      ·
        refine ⟨58889623078535384174000141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39259748719023589449333427 58889623078535384174000141)
        ·
          refine ⟨22083608654450769065250053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58889623078535384174000141 22083608654450769065250053)
          ·
            refine ⟨4140676622709519199734385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22083608654450769065250053 4140676622709519199734385)
            ·
              refine ⟨3105507467032139399800789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4140676622709519199734385 3105507467032139399800789)
              ·
                refine ⟨72785331258565767182831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3105507467032139399800789 72785331258565767182831)
                ·
                  rfl

theorem cell23_3827221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 7].length) (baseStart_3827221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827221 prefixEnd_3827221 := by exact prefixLift 3827221
  have htrace : WordTrace (prefixWord ++ tailWord_3827221) baseStart_3827221 baseEnd_3827221 := by
    simpa [prefixWord, tailWord_3827221, baseEnd_3827221] using wordTrace_append hprefix tailTrace_3827221
  have hstable : (prefixWord ++ tailWord_3827221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827221).length < 2 ^ (prefixWord ++ tailWord_3827221).sum := by decide
  have hdescent : baseEnd_3827221 < baseStart_3827221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827231 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 4, 1, 3]
def baseStart_3827231 : Nat := 118140960795 + 3827231 * 2 ^ 59
def prefixEnd_3827231 : Nat := 4983230072969 + 3 ^ 40 * 3827231 * 2
def baseEnd_3827231 : Nat := 1965209078787820674811391

theorem tailTrace_3827231 : CollatzResearch.WordTrace tailWord_3827231 prefixEnd_3827231 1965209078787820674811391 := by
  unfold tailWord_3827231
  simp only [CollatzResearch.WordTrace]
  refine ⟨139590582397603200861049547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93060388265068800574033031 139590582397603200861049547)
  ·
    refine ⟨209385873596404801291574321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139590582397603200861049547 209385873596404801291574321)
    ·
      refine ⟨157039405197303600968680741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209385873596404801291574321 157039405197303600968680741)
      ·
        refine ⟨29444888474494425181627639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157039405197303600968680741 29444888474494425181627639)
        ·
          refine ⟨44167332711741637772441459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29444888474494425181627639 44167332711741637772441459)
          ·
            refine ⟨66250999067612456658662189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44167332711741637772441459 66250999067612456658662189)
            ·
              refine ⟨24844124650354671246998321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66250999067612456658662189 24844124650354671246998321)
              ·
                refine ⟨18633093487766003435248741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24844124650354671246998321 18633093487766003435248741)
                ·
                  refine ⟨3493705028956125644109139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18633093487766003435248741 3493705028956125644109139)
                  ·
                    refine ⟨5240557543434188466163709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3493705028956125644109139 5240557543434188466163709)
                    ·
                      refine ⟨1965209078787820674811391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5240557543434188466163709 1965209078787820674811391)
                      ·
                        rfl

theorem cell23_3827231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_3827231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827231 prefixEnd_3827231 := by exact prefixLift 3827231
  have htrace : WordTrace (prefixWord ++ tailWord_3827231) baseStart_3827231 baseEnd_3827231 := by
    simpa [prefixWord, tailWord_3827231, baseEnd_3827231] using wordTrace_append hprefix tailTrace_3827231
  have hstable : (prefixWord ++ tailWord_3827231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827231).length < 2 ^ (prefixWord ++ tailWord_3827231).sum := by decide
  have hdescent : baseEnd_3827231 < baseStart_3827231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827232 : List Nat := [2, 1, 1, 6, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3827232 : Nat := 118140960795 + 3827232 * 2 ^ 59
def prefixEnd_3827232 : Nat := 4983230072969 + 3 ^ 40 * 3827232 * 2
def baseEnd_3827232 : Nat := 1965209592268475170898887

theorem tailTrace_3827232 : CollatzResearch.WordTrace tailWord_3827232 prefixEnd_3827232 1965209592268475170898887 := by
  unfold tailWord_3827232
  simp only [CollatzResearch.WordTrace]
  refine ⟨69795309435299789015917975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93060412580399718687890633 69795309435299789015917975)
  ·
    refine ⟨104692964152949683523876963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69795309435299789015917975 104692964152949683523876963)
    ·
      refine ⟨157039446229424525285815445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104692964152949683523876963 157039446229424525285815445)
      ·
        refine ⟨7361224042004274622772599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157039446229424525285815445 7361224042004274622772599)
        ·
          refine ⟨11041836063006411934158899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7361224042004274622772599 11041836063006411934158899)
          ·
            refine ⟨16562754094509617901238349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11041836063006411934158899 16562754094509617901238349)
            ·
              refine ⟨6211032785441106712964381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16562754094509617901238349 6211032785441106712964381)
              ·
                refine ⟨2329137294540415017361643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6211032785441106712964381 2329137294540415017361643)
                ·
                  refine ⟨3493705941810622526042465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329137294540415017361643 3493705941810622526042465)
                  ·
                    refine ⟨2620279456357966894531849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3493705941810622526042465 2620279456357966894531849)
                    ·
                      refine ⟨1965209592268475170898887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2620279456357966894531849 1965209592268475170898887)
                      ·
                        rfl

theorem cell23_3827232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3827232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827232 prefixEnd_3827232 := by exact prefixLift 3827232
  have htrace : WordTrace (prefixWord ++ tailWord_3827232) baseStart_3827232 baseEnd_3827232 := by
    simpa [prefixWord, tailWord_3827232, baseEnd_3827232] using wordTrace_append hprefix tailTrace_3827232
  have hstable : (prefixWord ++ tailWord_3827232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827232).length < 2 ^ (prefixWord ++ tailWord_3827232).sum := by decide
  have hdescent : baseEnd_3827232 < baseStart_3827232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827274 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_3827274 : Nat := 118140960795 + 3827274 * 2 ^ 59
def prefixEnd_3827274 : Nat := 4983230072969 + 3 ^ 40 * 3827274 * 2
def baseEnd_3827274 : Nat := 1965231158455964006573693

theorem tailTrace_3827274 : CollatzResearch.WordTrace tailWord_3827274 prefixEnd_3827274 1965231158455964006573693 := by
  unfold tailWord_3827274
  simp only [CollatzResearch.WordTrace]
  refine ⟨34898037684111854801216219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93061433824298279469909917 34898037684111854801216219)
  ·
    refine ⟨52347056526167782201824329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34898037684111854801216219 52347056526167782201824329)
    ·
      refine ⟨39260292394625836651368247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52347056526167782201824329 39260292394625836651368247)
      ·
        refine ⟨58890438591938754977052371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39260292394625836651368247 58890438591938754977052371)
        ·
          refine ⟨88335657887908132465578557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58890438591938754977052371 88335657887908132465578557)
          ·
            refine ⟨33125871707965549674591959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88335657887908132465578557 33125871707965549674591959)
            ·
              refine ⟨49688807561948324511887939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33125871707965549674591959 49688807561948324511887939)
              ·
                refine ⟨74533211342922486767831909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49688807561948324511887939 74533211342922486767831909)
                ·
                  refine ⟨13974977126797966268968483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74533211342922486767831909 13974977126797966268968483)
                  ·
                    refine ⟨20962465690196949403452725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13974977126797966268968483 20962465690196949403452725)
                    ·
                      refine ⟨1965231158455964006573693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20962465690196949403452725 1965231158455964006573693)
                      ·
                        rfl

theorem cell23_3827274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_3827274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827274 prefixEnd_3827274 := by exact prefixLift 3827274
  have htrace : WordTrace (prefixWord ++ tailWord_3827274) baseStart_3827274 baseEnd_3827274 := by
    simpa [prefixWord, tailWord_3827274, baseEnd_3827274] using wordTrace_append hprefix tailTrace_3827274
  have hstable : (prefixWord ++ tailWord_3827274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827274).length < 2 ^ (prefixWord ++ tailWord_3827274).sum := by decide
  have hdescent : baseEnd_3827274 < baseStart_3827274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827292 : List Nat := [2, 2, 4, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_3827292 : Nat := 118140960795 + 3827292 * 2 ^ 59
def prefixEnd_3827292 : Nat := 4983230072969 + 3 ^ 40 * 3827292 * 2
def baseEnd_3827292 : Nat := 1965240401107744936148611

theorem tailTrace_3827292 : CollatzResearch.WordTrace tailWord_3827292 prefixEnd_3827292 1965240401107744936148611 := by
  unfold tailWord_3827292
  simp only [CollatzResearch.WordTrace]
  refine ⟨69796403625191104139510065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93061871500254805519346753 69796403625191104139510065)
  ·
    refine ⟨52347302718893328104632549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69796403625191104139510065 52347302718893328104632549)
    ·
      refine ⟨9815119259792499019618603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52347302718893328104632549 9815119259792499019618603)
      ·
        refine ⟨14722678889688748529427905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9815119259792499019618603 14722678889688748529427905)
        ·
          refine ⟨11042009167266561397070929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14722678889688748529427905 11042009167266561397070929)
          ·
            refine ⟨8281506875449921047803197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11042009167266561397070929 8281506875449921047803197)
            ·
              refine ⟨3105565078293720392926199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8281506875449921047803197 3105565078293720392926199)
              ·
                refine ⟨4658347617440580589389299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105565078293720392926199 4658347617440580589389299)
                ·
                  refine ⟨6987521426160870884083949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658347617440580589389299 6987521426160870884083949)
                  ·
                    refine ⟨2620320534810326581531481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6987521426160870884083949 2620320534810326581531481)
                    ·
                      refine ⟨1965240401107744936148611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2620320534810326581531481 1965240401107744936148611)
                      ·
                        rfl

theorem cell23_3827292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_3827292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827292 prefixEnd_3827292 := by exact prefixLift 3827292
  have htrace : WordTrace (prefixWord ++ tailWord_3827292) baseStart_3827292 baseEnd_3827292 := by
    simpa [prefixWord, tailWord_3827292, baseEnd_3827292] using wordTrace_append hprefix tailTrace_3827292
  have hstable : (prefixWord ++ tailWord_3827292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827292).length < 2 ^ (prefixWord ++ tailWord_3827292).sum := by decide
  have hdescent : baseEnd_3827292 < baseStart_3827292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827318 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3827318 : Nat := 118140960795 + 3827318 * 2 ^ 59
def prefixEnd_3827318 : Nat := 4983230072969 + 3 ^ 40 * 3827318 * 2
def baseEnd_3827318 : Nat := 1965253751604761834423491

theorem tailTrace_3827318 : CollatzResearch.WordTrace tailWord_3827318 prefixEnd_3827318 1965253751604761834423491 := by
  unfold tailWord_3827318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8724609721768000919966663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93062503698858676479644405 8724609721768000919966663)
  ·
    refine ⟨13086914582652001379949995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8724609721768000919966663 13086914582652001379949995)
    ·
      refine ⟨19630371873978002069924993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13086914582652001379949995 19630371873978002069924993)
      ·
        refine ⟨14722778905483501552443745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19630371873978002069924993 14722778905483501552443745)
        ·
          refine ⟨11042084179112626164332809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14722778905483501552443745 11042084179112626164332809)
          ·
            refine ⟨8281563134334469623249607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11042084179112626164332809 8281563134334469623249607)
            ·
              refine ⟨12422344701501704434874411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8281563134334469623249607 12422344701501704434874411)
              ·
                refine ⟨18633517052252556652311617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12422344701501704434874411 18633517052252556652311617)
                ·
                  refine ⟨13975137789189417489233713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18633517052252556652311617 13975137789189417489233713)
                  ·
                    refine ⟨10481353341892063116925285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13975137789189417489233713 10481353341892063116925285)
                    ·
                      refine ⟨1965253751604761834423491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10481353341892063116925285 1965253751604761834423491)
                      ·
                        rfl

theorem cell23_3827318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3827318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827318 prefixEnd_3827318 := by exact prefixLift 3827318
  have htrace : WordTrace (prefixWord ++ tailWord_3827318) baseStart_3827318 baseEnd_3827318 := by
    simpa [prefixWord, tailWord_3827318, baseEnd_3827318] using wordTrace_append hprefix tailTrace_3827318
  have hstable : (prefixWord ++ tailWord_3827318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827318).length < 2 ^ (prefixWord ++ tailWord_3827318).sum := by decide
  have hdescent : baseEnd_3827318 < baseStart_3827318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827321 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 2, 3, 3]
def baseStart_3827321 : Nat := 118140960795 + 3827321 * 2 ^ 59
def prefixEnd_3827321 : Nat := 4983230072969 + 3 ^ 40 * 3827321 * 2
def baseEnd_3827321 : Nat := 1965255292046725322685977

theorem tailTrace_3827321 : CollatzResearch.WordTrace tailWord_3827321 prefixEnd_3827321 1965255292046725322685977 := by
  unfold tailWord_3827321
  simp only [CollatzResearch.WordTrace]
  refine ⟨139593864967277146231825817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93062576644851430821217211 139593864967277146231825817)
  ·
    refine ⟨104695398725457859673869363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139593864967277146231825817 104695398725457859673869363)
    ·
      refine ⟨157043098088186789510804045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104695398725457859673869363 157043098088186789510804045)
      ·
        refine ⟨58891161783070046066551517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157043098088186789510804045 58891161783070046066551517)
        ·
          refine ⟨22084185668651267274956819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58891161783070046066551517 22084185668651267274956819)
          ·
            refine ⟨33126278502976900912435229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22084185668651267274956819 33126278502976900912435229)
            ·
              refine ⟨12422354438616337842163211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33126278502976900912435229 12422354438616337842163211)
              ·
                refine ⟨18633531657924506763244817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12422354438616337842163211 18633531657924506763244817)
                ·
                  refine ⟨13975148743443380072433613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18633531657924506763244817 13975148743443380072433613)
                  ·
                    refine ⟨5240680778791267527162605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13975148743443380072433613 5240680778791267527162605)
                    ·
                      refine ⟨1965255292046725322685977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5240680778791267527162605 1965255292046725322685977)
                      ·
                        rfl

theorem cell23_3827321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_3827321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827321 prefixEnd_3827321 := by exact prefixLift 3827321
  have htrace : WordTrace (prefixWord ++ tailWord_3827321) baseStart_3827321 baseEnd_3827321 := by
    simpa [prefixWord, tailWord_3827321, baseEnd_3827321] using wordTrace_append hprefix tailTrace_3827321
  have hstable : (prefixWord ++ tailWord_3827321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827321).length < 2 ^ (prefixWord ++ tailWord_3827321).sum := by decide
  have hdescent : baseEnd_3827321 < baseStart_3827321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827324 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 1, 7]
def baseStart_3827324 : Nat := 118140960795 + 3827324 * 2 ^ 59
def prefixEnd_3827324 : Nat := 4983230072969 + 3 ^ 40 * 3827324 * 2
def baseEnd_3827324 : Nat := 655085610829562936982821

theorem tailTrace_3827324 : CollatzResearch.WordTrace tailWord_3827324 prefixEnd_3827324 655085610829562936982821 := by
  unfold tailWord_3827324
  simp only [CollatzResearch.WordTrace]
  refine ⟨69796987193133138872092513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93062649590844185162790017 69796987193133138872092513)
  ·
    refine ⟨52347740394849854154069385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69796987193133138872092513 52347740394849854154069385)
    ·
      refine ⟨39260805296137390615552039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52347740394849854154069385 39260805296137390615552039)
      ·
        refine ⟨58891207944206085923328059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39260805296137390615552039 58891207944206085923328059)
        ·
          refine ⟨88336811916309128884992089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58891207944206085923328059 88336811916309128884992089)
          ·
            refine ⟨66252608937231846663744067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88336811916309128884992089 66252608937231846663744067)
            ·
              refine ⟨99378913405847769995616101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66252608937231846663744067 99378913405847769995616101)
              ·
                refine ⟨18633546263596456874178019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99378913405847769995616101 18633546263596456874178019)
                ·
                  refine ⟨27950319395394685311267029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18633546263596456874178019 27950319395394685311267029)
                  ·
                    refine ⟨655085610829562936982821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27950319395394685311267029 655085610829562936982821)
                    ·
                      rfl

theorem cell23_3827324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_3827324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827324 prefixEnd_3827324 := by exact prefixLift 3827324
  have htrace : WordTrace (prefixWord ++ tailWord_3827324) baseStart_3827324 baseEnd_3827324 := by
    simpa [prefixWord, tailWord_3827324, baseEnd_3827324] using wordTrace_append hprefix tailTrace_3827324
  have hstable : (prefixWord ++ tailWord_3827324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827324).length < 2 ^ (prefixWord ++ tailWord_3827324).sum := by decide
  have hdescent : baseEnd_3827324 < baseStart_3827324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827331 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 4, 5, 2]
def baseStart_3827331 : Nat := 118140960795 + 3827331 * 2 ^ 59
def prefixEnd_3827331 : Nat := 4983230072969 + 3 ^ 40 * 3827331 * 2
def baseEnd_3827331 : Nat := 1965260426853270283560931

theorem tailTrace_3827331 : CollatzResearch.WordTrace tailWord_3827331 prefixEnd_3827331 1965260426853270283560931 := by
  unfold tailWord_3827331
  simp only [CollatzResearch.WordTrace]
  refine ⟨139594229697240917939689847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93062819798160611959793231 139594229697240917939689847)
  ·
    refine ⟨209391344545861376909534771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139594229697240917939689847 209391344545861376909534771)
    ·
      refine ⟨314087016818792065364302157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209391344545861376909534771 314087016818792065364302157)
      ·
        refine ⟨117782631307047024511613309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314087016818792065364302157 117782631307047024511613309)
        ·
          refine ⟨44168486740142634191854991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117782631307047024511613309 44168486740142634191854991)
          ·
            refine ⟨66252730110213951287782487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44168486740142634191854991 66252730110213951287782487)
            ·
              refine ⟨99379095165320926931673731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66252730110213951287782487 99379095165320926931673731)
              ·
                refine ⟨149068642747981390397510597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99379095165320926931673731 149068642747981390397510597)
                ·
                  refine ⟨27950370515246510699533237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149068642747981390397510597 27950370515246510699533237)
                  ·
                    refine ⟨2620347235804360378081241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27950370515246510699533237 2620347235804360378081241)
                    ·
                      refine ⟨1965260426853270283560931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2620347235804360378081241 1965260426853270283560931)
                      ·
                        rfl

theorem cell23_3827331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 5, 2].length) (baseStart_3827331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827331 prefixEnd_3827331 := by exact prefixLift 3827331
  have htrace : WordTrace (prefixWord ++ tailWord_3827331) baseStart_3827331 baseEnd_3827331 := by
    simpa [prefixWord, tailWord_3827331, baseEnd_3827331] using wordTrace_append hprefix tailTrace_3827331
  have hstable : (prefixWord ++ tailWord_3827331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827331).length < 2 ^ (prefixWord ++ tailWord_3827331).sum := by decide
  have hdescent : baseEnd_3827331 < baseStart_3827331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827378 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2]
def baseStart_3827378 : Nat := 118140960795 + 3827378 * 2 ^ 59
def prefixEnd_3827378 : Nat := 4983230072969 + 3 ^ 40 * 3827378 * 2
def baseEnd_3827378 : Nat := 1965284560444031599673215

theorem tailTrace_3827378 : CollatzResearch.WordTrace tailWord_3827378 prefixEnd_3827378 1965284560444031599673215 := by
  unfold tailWord_3827378
  simp only [CollatzResearch.WordTrace]
  refine ⟨34898985982017661241662697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93063962618713763311100525 34898985982017661241662697)
  ·
    refine ⟨26174239486513245931247023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34898985982017661241662697 26174239486513245931247023)
    ·
      refine ⟨39261359229769868896870535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26174239486513245931247023 39261359229769868896870535)
      ·
        refine ⟨58892038844654803345305803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39261359229769868896870535 58892038844654803345305803)
        ·
          refine ⟨88338058266982205017958705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58892038844654803345305803 88338058266982205017958705)
          ·
            refine ⟨66253543700236653763469029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88338058266982205017958705 66253543700236653763469029)
            ·
              refine ⟨12422539443794372580650443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66253543700236653763469029 12422539443794372580650443)
              ·
                refine ⟨18633809165691558870975665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12422539443794372580650443 18633809165691558870975665)
                ·
                  refine ⟨13975356874268669153231749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18633809165691558870975665 13975356874268669153231749)
                  ·
                    refine ⟨2620379413925375466230953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13975356874268669153231749 2620379413925375466230953)
                    ·
                      refine ⟨1965284560444031599673215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2620379413925375466230953 1965284560444031599673215)
                      ·
                        rfl

theorem cell23_3827378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_3827378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827378 prefixEnd_3827378 := by exact prefixLift 3827378
  have htrace : WordTrace (prefixWord ++ tailWord_3827378) baseStart_3827378 baseEnd_3827378 := by
    simpa [prefixWord, tailWord_3827378, baseEnd_3827378] using wordTrace_append hprefix tailTrace_3827378
  have hstable : (prefixWord ++ tailWord_3827378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827378).length < 2 ^ (prefixWord ++ tailWord_3827378).sum := by decide
  have hdescent : baseEnd_3827378 < baseStart_3827378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827388 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 3, 4]
def baseStart_3827388 : Nat := 118140960795 + 3827388 * 2 ^ 59
def prefixEnd_3827388 : Nat := 4983230072969 + 3 ^ 40 * 3827388 * 2
def baseEnd_3827388 : Nat := 655096565083525520182723

theorem tailTrace_3827388 : CollatzResearch.WordTrace tailWord_3827388 prefixEnd_3827388 655096565083525520182723 := by
  unfold tailWord_3827388
  simp only [CollatzResearch.WordTrace]
  refine ⟨69798154329017208337257409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93064205772022944449676545 69798154329017208337257409)
  ·
    refine ⟨52348615746762906252943057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69798154329017208337257409 52348615746762906252943057)
    ·
      refine ⟨39261461810072179689707293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52348615746762906252943057 39261461810072179689707293)
      ·
        refine ⟨14723048178777067383640235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39261461810072179689707293 14723048178777067383640235)
        ·
          refine ⟨22084572268165601075460353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14723048178777067383640235 22084572268165601075460353)
          ·
            refine ⟨16563429201124200806595265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22084572268165601075460353 16563429201124200806595265)
            ·
              refine ⟨12422571900843150604946449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16563429201124200806595265 12422571900843150604946449)
              ·
                refine ⟨9316928925632362953709837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12422571900843150604946449 9316928925632362953709837)
                ·
                  refine ⟨3493848347112136107641189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9316928925632362953709837 3493848347112136107641189)
                  ·
                    refine ⟨655096565083525520182723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3493848347112136107641189 655096565083525520182723)
                    ·
                      rfl

theorem cell23_3827388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_3827388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827388 prefixEnd_3827388 := by exact prefixLift 3827388
  have htrace : WordTrace (prefixWord ++ tailWord_3827388) baseStart_3827388 baseEnd_3827388 := by
    simpa [prefixWord, tailWord_3827388, baseEnd_3827388] using wordTrace_append hprefix tailTrace_3827388
  have hstable : (prefixWord ++ tailWord_3827388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827388).length < 2 ^ (prefixWord ++ tailWord_3827388).sum := by decide
  have hdescent : baseEnd_3827388 < baseStart_3827388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827468 : List Nat := [2, 2, 1, 2, 2, 1, 2, 5, 1, 1, 4]
def baseStart_3827468 : Nat := 118140960795 + 3827468 * 2 ^ 59
def prefixEnd_3827468 : Nat := 4983230072969 + 3 ^ 40 * 3827468 * 2
def baseEnd_3827468 : Nat := 1965330773702936247547801

theorem tailTrace_3827468 : CollatzResearch.WordTrace tailWord_3827468 prefixEnd_3827468 1965330773702936247547801 := by
  unfold tailWord_3827468
  simp only [CollatzResearch.WordTrace]
  refine ⟨69799613248872295168713529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93066150998496393558284705 69799613248872295168713529)
  ·
    refine ⟨52349709936654221376535147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69799613248872295168713529 52349709936654221376535147)
    ·
      refine ⟨78524564904981332064802721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52349709936654221376535147 78524564904981332064802721)
      ·
        refine ⟨58893423678735999048602041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78524564904981332064802721 58893423678735999048602041)
        ·
          refine ⟨44170067759051999286451531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58893423678735999048602041 44170067759051999286451531)
          ·
            refine ⟨66255101638577998929677297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44170067759051999286451531 66255101638577998929677297)
            ·
              refine ⟨49691326228933499197257973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66255101638577998929677297 49691326228933499197257973)
              ·
                refine ⟨4658561833962515549742935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49691326228933499197257973 4658561833962515549742935)
                ·
                  refine ⟨6987842750943773324614403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658561833962515549742935 6987842750943773324614403)
                  ·
                    refine ⟨10481764126415659986921605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6987842750943773324614403 10481764126415659986921605)
                    ·
                      refine ⟨1965330773702936247547801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10481764126415659986921605 1965330773702936247547801)
                      ·
                        rfl

theorem cell23_3827468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_3827468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827468 prefixEnd_3827468 := by exact prefixLift 3827468
  have htrace : WordTrace (prefixWord ++ tailWord_3827468) baseStart_3827468 baseEnd_3827468 := by
    simpa [prefixWord, tailWord_3827468, baseEnd_3827468] using wordTrace_append hprefix tailTrace_3827468
  have hstable : (prefixWord ++ tailWord_3827468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827468).length < 2 ^ (prefixWord ++ tailWord_3827468).sum := by decide
  have hdescent : baseEnd_3827468 < baseStart_3827468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827471 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 5]
def baseStart_3827471 : Nat := 118140960795 + 3827471 * 2 ^ 59
def prefixEnd_3827471 : Nat := 4983230072969 + 3 ^ 40 * 3827471 * 2
def baseEnd_3827471 : Nat := 1965332314144899735810287

theorem tailTrace_3827471 : CollatzResearch.WordTrace tailWord_3827471 prefixEnd_3827471 1965332314144899735810287 := by
  unfold tailWord_3827471
  simp only [CollatzResearch.WordTrace]
  refine ⟨139599335916733721849786267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93066223944489147899857511 139599335916733721849786267)
  ·
    refine ⟨209399003875100582774679401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139599335916733721849786267 209399003875100582774679401)
    ·
      refine ⟨157049252906325437081009551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209399003875100582774679401 157049252906325437081009551)
      ·
        refine ⟨235573879359488155621514327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157049252906325437081009551 235573879359488155621514327)
        ·
          refine ⟨353360819039232233432271491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235573879359488155621514327 353360819039232233432271491)
          ·
            refine ⟨530041228558848350148407237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353360819039232233432271491 530041228558848350148407237)
            ·
              refine ⟨99382730354784065652826357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530041228558848350148407237 99382730354784065652826357)
              ·
                refine ⟨9317130970761006154952471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99382730354784065652826357 9317130970761006154952471)
                ·
                  refine ⟨13975696456141509232428707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9317130970761006154952471 13975696456141509232428707)
                  ·
                    refine ⟨20963544684212263848643061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13975696456141509232428707 20963544684212263848643061)
                    ·
                      refine ⟨1965332314144899735810287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20963544684212263848643061 1965332314144899735810287)
                      ·
                        rfl

theorem cell23_3827471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_3827471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827471 prefixEnd_3827471 := by exact prefixLift 3827471
  have htrace : WordTrace (prefixWord ++ tailWord_3827471) baseStart_3827471 baseEnd_3827471 := by
    simpa [prefixWord, tailWord_3827471, baseEnd_3827471] using wordTrace_append hprefix tailTrace_3827471
  have hstable : (prefixWord ++ tailWord_3827471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827471).length < 2 ^ (prefixWord ++ tailWord_3827471).sum := by decide
  have hdescent : baseEnd_3827471 < baseStart_3827471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827479 : List Nat := [1, 1, 3, 4, 2, 1, 4, 2, 1, 1, 3]
def baseStart_3827479 : Nat := 118140960795 + 3827479 * 2 ^ 59
def prefixEnd_3827479 : Nat := 4983230072969 + 3 ^ 40 * 3827479 * 2
def baseEnd_3827479 : Nat := 1965336421990135704510251

theorem tailTrace_3827479 : CollatzResearch.WordTrace tailWord_3827479 prefixEnd_3827479 1965336421990135704510251 := by
  unfold tailWord_3827479
  simp only [CollatzResearch.WordTrace]
  refine ⟨139599627700704739216077491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93066418467136492810718327 139599627700704739216077491)
  ·
    refine ⟨209399441551057108824116237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139599627700704739216077491 209399441551057108824116237)
    ·
      refine ⟨78524790581646415809043589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209399441551057108824116237 78524790581646415809043589)
      ·
        refine ⟨14723398234058702964195673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78524790581646415809043589 14723398234058702964195673)
        ·
          refine ⟨11042548675544027223146755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14723398234058702964195673 11042548675544027223146755)
          ·
            refine ⟨16563823013316040834720133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11042548675544027223146755 16563823013316040834720133)
            ·
              refine ⟨3105716814996757656510025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16563823013316040834720133 3105716814996757656510025)
              ·
                refine ⟨2329287611247568242382519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3105716814996757656510025 2329287611247568242382519)
                ·
                  refine ⟨3493931416871352363573779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329287611247568242382519 3493931416871352363573779)
                  ·
                    refine ⟨5240897125307028545360669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3493931416871352363573779 5240897125307028545360669)
                    ·
                      refine ⟨1965336421990135704510251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5240897125307028545360669 1965336421990135704510251)
                      ·
                        rfl

theorem cell23_3827479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_3827479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827479 prefixEnd_3827479 := by exact prefixLift 3827479
  have htrace : WordTrace (prefixWord ++ tailWord_3827479) baseStart_3827479 baseEnd_3827479 := by
    simpa [prefixWord, tailWord_3827479, baseEnd_3827479] using wordTrace_append hprefix tailTrace_3827479
  have hstable : (prefixWord ++ tailWord_3827479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827479).length < 2 ^ (prefixWord ++ tailWord_3827479).sum := by decide
  have hdescent : baseEnd_3827479 < baseStart_3827479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827488 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3827488 : Nat := 118140960795 + 3827488 * 2 ^ 59
def prefixEnd_3827488 : Nat := 4983230072969 + 3 ^ 40 * 3827488 * 2
def baseEnd_3827488 : Nat := 1965341043316026169297709

theorem tailTrace_3827488 : CollatzResearch.WordTrace tailWord_3827488 prefixEnd_3827488 1965341043316026169297709 := by
  unfold tailWord_3827488
  simp only [CollatzResearch.WordTrace]
  refine ⟨69799977978836066876577559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93066637305114755835436745 69799977978836066876577559)
  ·
    refine ⟨104699966968254100314866339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69799977978836066876577559 104699966968254100314866339)
    ·
      refine ⟨157049950452381150472299509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104699966968254100314866339 157049950452381150472299509)
      ·
        refine ⟨14723432854910732856778079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157049950452381150472299509 14723432854910732856778079)
        ·
          refine ⟨22085149282366099285167119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14723432854910732856778079 22085149282366099285167119)
          ·
            refine ⟨33127723923549148927750679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22085149282366099285167119 33127723923549148927750679)
            ·
              refine ⟨49691585885323723391626019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33127723923549148927750679 49691585885323723391626019)
              ·
                refine ⟨74537378827985585087439029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49691585885323723391626019 74537378827985585087439029)
                ·
                  refine ⟨6987879265123648601947409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74537378827985585087439029 6987879265123648601947409)
                  ·
                    refine ⟨5240909448842736451460557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6987879265123648601947409 5240909448842736451460557)
                    ·
                      refine ⟨1965341043316026169297709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5240909448842736451460557 1965341043316026169297709)
                      ·
                        rfl

theorem cell23_3827488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3827488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827488 prefixEnd_3827488 := by exact prefixLift 3827488
  have htrace : WordTrace (prefixWord ++ tailWord_3827488) baseStart_3827488 baseEnd_3827488 := by
    simpa [prefixWord, tailWord_3827488, baseEnd_3827488] using wordTrace_append hprefix tailTrace_3827488
  have hstable : (prefixWord ++ tailWord_3827488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827488).length < 2 ^ (prefixWord ++ tailWord_3827488).sum := by decide
  have hdescent : baseEnd_3827488 < baseStart_3827488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827491 : List Nat := [1, 1, 1, 4, 2, 1, 5, 8]
def baseStart_3827491 : Nat := 118140960795 + 3827491 * 2 ^ 59
def prefixEnd_3827491 : Nat := 4983230072969 + 3 ^ 40 * 3827491 * 2
def baseEnd_3827491 : Nat := 72790466065110728057785

theorem tailTrace_3827491 : CollatzResearch.WordTrace tailWord_3827491 prefixEnd_3827491 72790466065110728057785 := by
  unfold tailWord_3827491
  simp only [CollatzResearch.WordTrace]
  refine ⟨139600065376661265265514327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93066710251107510177009551 139600065376661265265514327)
  ·
    refine ⟨209400098064991897898271491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139600065376661265265514327 209400098064991897898271491)
    ·
      refine ⟨314100147097487846847407237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209400098064991897898271491 314100147097487846847407237)
      ·
        refine ⟨58893777580778971283888857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314100147097487846847407237 58893777580778971283888857)
        ·
          refine ⟨44170333185584228462916643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58893777580778971283888857 44170333185584228462916643)
          ·
            refine ⟨66255499778376342694374965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44170333185584228462916643 66255499778376342694374965)
            ·
              refine ⟨6211453104222782127597653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66255499778376342694374965 6211453104222782127597653)
              ·
                refine ⟨72790466065110728057785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6211453104222782127597653 72790466065110728057785)
                ·
                  rfl

theorem cell23_3827491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 8].length) (baseStart_3827491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827491 prefixEnd_3827491 := by exact prefixLift 3827491
  have htrace : WordTrace (prefixWord ++ tailWord_3827491) baseStart_3827491 baseEnd_3827491 := by
    simpa [prefixWord, tailWord_3827491, baseEnd_3827491] using wordTrace_append hprefix tailTrace_3827491
  have hstable : (prefixWord ++ tailWord_3827491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827491).length < 2 ^ (prefixWord ++ tailWord_3827491).sum := by decide
  have hdescent : baseEnd_3827491 < baseStart_3827491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827519 : List Nat := [1, 1, 2, 2, 7, 1, 2, 1, 1, 1, 4]
def baseStart_3827519 : Nat := 118140960795 + 3827519 * 2 ^ 59
def prefixEnd_3827519 : Nat := 4983230072969 + 3 ^ 40 * 3827519 * 2
def baseEnd_3827519 : Nat := 1965356961216315548010067

theorem tailTrace_3827519 : CollatzResearch.WordTrace tailWord_3827519 prefixEnd_3827519 1965356961216315548010067 := by
  unfold tailWord_3827519
  simp only [CollatzResearch.WordTrace]
  refine ⟨139601086620559826047533611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93067391080373217365022407 139601086620559826047533611)
  ·
    refine ⟨209401629930839739071300417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139601086620559826047533611 209401629930839739071300417)
    ·
      refine ⟨157051222448129804303475313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209401629930839739071300417 157051222448129804303475313)
      ·
        refine ⟨117788416836097353227606485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157051222448129804303475313 117788416836097353227606485)
        ·
          refine ⟨2760666019596031716272027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 117788416836097353227606485 2760666019596031716272027)
          ·
            refine ⟨4140999029394047574408041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760666019596031716272027 4140999029394047574408041)
            ·
              refine ⟨3105749272045535680806031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4140999029394047574408041 3105749272045535680806031)
              ·
                refine ⟨4658623908068303521209047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105749272045535680806031 4658623908068303521209047)
                ·
                  refine ⟨6987935862102455281813571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658623908068303521209047 6987935862102455281813571)
                  ·
                    refine ⟨10481903793153682922720357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6987935862102455281813571 10481903793153682922720357)
                    ·
                      refine ⟨1965356961216315548010067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10481903793153682922720357 1965356961216315548010067)
                      ·
                        rfl

theorem cell23_3827519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 1, 1, 4].length) (baseStart_3827519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827519 prefixEnd_3827519 := by exact prefixLift 3827519
  have htrace : WordTrace (prefixWord ++ tailWord_3827519) baseStart_3827519 baseEnd_3827519 := by
    simpa [prefixWord, tailWord_3827519, baseEnd_3827519] using wordTrace_append hprefix tailTrace_3827519
  have hstable : (prefixWord ++ tailWord_3827519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827519).length < 2 ^ (prefixWord ++ tailWord_3827519).sum := by decide
  have hdescent : baseEnd_3827519 < baseStart_3827519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827561 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 5]
def baseStart_3827561 : Nat := 118140960795 + 3827561 * 2 ^ 59
def prefixEnd_3827561 : Nat := 4983230072969 + 3 ^ 40 * 3827561 * 2
def baseEnd_3827561 : Nat := 1965378527403804383684873

theorem tailTrace_3827561 : CollatzResearch.WordTrace tailWord_3827561 prefixEnd_3827561 1965378527403804383684873 := by
  unfold tailWord_3827561
  simp only [CollatzResearch.WordTrace]
  refine ⟨139602618486407667220562537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93068412324271778147041691 139602618486407667220562537)
  ·
    refine ⟨104701963864805750415421903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139602618486407667220562537 104701963864805750415421903)
    ·
      refine ⟨157052945797208625623132855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104701963864805750415421903 157052945797208625623132855)
      ·
        refine ⟨235579418695812938434699283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157052945797208625623132855 235579418695812938434699283)
        ·
          refine ⟨353369128043719407652048925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235579418695812938434699283 353369128043719407652048925)
          ·
            refine ⟨132513423016394777869518347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353369128043719407652048925 132513423016394777869518347)
            ·
              refine ⟨198770134524592166804277521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132513423016394777869518347 198770134524592166804277521)
              ·
                refine ⟨149077600893444125103208141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198770134524592166804277521 149077600893444125103208141)
                ·
                  refine ⟨55904100335041546913703053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149077600893444125103208141 55904100335041546913703053)
                  ·
                    refine ⟨20964037625640580092638645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55904100335041546913703053 20964037625640580092638645)
                    ·
                      refine ⟨1965378527403804383684873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20964037625640580092638645 1965378527403804383684873)
                      ·
                        rfl

theorem cell23_3827561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_3827561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827561 prefixEnd_3827561 := by exact prefixLift 3827561
  have htrace : WordTrace (prefixWord ++ tailWord_3827561) baseStart_3827561 baseEnd_3827561 := by
    simpa [prefixWord, tailWord_3827561, baseEnd_3827561] using wordTrace_append hprefix tailTrace_3827561
  have hstable : (prefixWord ++ tailWord_3827561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827561).length < 2 ^ (prefixWord ++ tailWord_3827561).sum := by decide
  have hdescent : baseEnd_3827561 < baseStart_3827561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827588 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3827588 : Nat := 118140960795 + 3827588 * 2 ^ 59
def prefixEnd_3827588 : Nat := 4983230072969 + 3 ^ 40 * 3827588 * 2
def baseEnd_3827588 : Nat := 1965392391381475778047249

theorem tailTrace_3827588 : CollatzResearch.WordTrace tailWord_3827588 prefixEnd_3827588 1965392391381475778047249 := by
  unfold tailWord_3827588
  simp only [CollatzResearch.WordTrace]
  refine ⟨69801801628654925415897709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93069068838206567221196945 69801801628654925415897709)
  ·
    refine ⟨26175675610745597030961641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69801801628654925415897709 26175675610745597030961641)
    ·
      refine ⟨19631756708059197773221231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26175675610745597030961641 19631756708059197773221231)
      ·
        refine ⟨29447635062088796659831847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19631756708059197773221231 29447635062088796659831847)
        ·
          refine ⟨44171452593133194989747771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29447635062088796659831847 44171452593133194989747771)
          ·
            refine ⟨66257178889699792484621657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44171452593133194989747771 66257178889699792484621657)
            ·
              refine ⟨49692884167274844363466243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66257178889699792484621657 49692884167274844363466243)
              ·
                refine ⟨74539326250912266545199365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49692884167274844363466243 74539326250912266545199365)
                ·
                  refine ⟨13976123672046049977224881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74539326250912266545199365 13976123672046049977224881)
                  ·
                    refine ⟨10482092754034537482918661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13976123672046049977224881 10482092754034537482918661)
                    ·
                      refine ⟨1965392391381475778047249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10482092754034537482918661 1965392391381475778047249)
                      ·
                        rfl

theorem cell23_3827588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3827588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827588 prefixEnd_3827588 := by exact prefixLift 3827588
  have htrace : WordTrace (prefixWord ++ tailWord_3827588) baseStart_3827588 baseEnd_3827588 := by
    simpa [prefixWord, tailWord_3827588, baseEnd_3827588] using wordTrace_append hprefix tailTrace_3827588
  have hstable : (prefixWord ++ tailWord_3827588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827588).length < 2 ^ (prefixWord ++ tailWord_3827588).sum := by decide
  have hdescent : baseEnd_3827588 < baseStart_3827588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827609 : List Nat := [1, 2, 1, 2, 1, 3, 6, 1, 2, 2, 2]
def baseStart_3827609 : Nat := 118140960795 + 3827609 * 2 ^ 59
def prefixEnd_3827609 : Nat := 4983230072969 + 3 ^ 40 * 3827609 * 2
def baseEnd_3827609 : Nat := 1965403174475220195884653

theorem tailTrace_3827609 : CollatzResearch.WordTrace tailWord_3827609 prefixEnd_3827609 1965403174475220195884653 := by
  unfold tailWord_3827609
  simp only [CollatzResearch.WordTrace]
  refine ⟨139604369190233771418309881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93069579460155847612206587 139604369190233771418309881)
  ·
    refine ⟨104703276892675328563732411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139604369190233771418309881 104703276892675328563732411)
    ·
      refine ⟨157054915339012992845598617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104703276892675328563732411 157054915339012992845598617)
      ·
        refine ⟨117791186504259744634198963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157054915339012992845598617 117791186504259744634198963)
        ·
          refine ⟨176686779756389616951298445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117791186504259744634198963 176686779756389616951298445)
          ·
            refine ⟨66257542408646106356736917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176686779756389616951298445 66257542408646106356736917)
            ·
              refine ⟨3105822300405286235472043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66257542408646106356736917 3105822300405286235472043)
              ·
                refine ⟨4658733450607929353208065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105822300405286235472043 4658733450607929353208065)
                ·
                  refine ⟨3494050087955947014906049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4658733450607929353208065 3494050087955947014906049)
                  ·
                    refine ⟨2620537565966960261179537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3494050087955947014906049 2620537565966960261179537)
                    ·
                      refine ⟨1965403174475220195884653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2620537565966960261179537 1965403174475220195884653)
                      ·
                        rfl

theorem cell23_3827609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 2, 2, 2].length) (baseStart_3827609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827609 prefixEnd_3827609 := by exact prefixLift 3827609
  have htrace : WordTrace (prefixWord ++ tailWord_3827609) baseStart_3827609 baseEnd_3827609 := by
    simpa [prefixWord, tailWord_3827609, baseEnd_3827609] using wordTrace_append hprefix tailTrace_3827609
  have hstable : (prefixWord ++ tailWord_3827609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827609).length < 2 ^ (prefixWord ++ tailWord_3827609).sum := by decide
  have hdescent : baseEnd_3827609 < baseStart_3827609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827630 : List Nat := [4, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_3827630 : Nat := 118140960795 + 3827630 * 2 ^ 59
def prefixEnd_3827630 : Nat := 4983230072969 + 3 ^ 40 * 3827630 * 2
def baseEnd_3827630 : Nat := 1965413957568964613722057

theorem tailTrace_3827630 : CollatzResearch.WordTrace tailWord_3827630 prefixEnd_3827630 1965413957568964613722057 := by
  unfold tailWord_3827630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17450641890394711500603043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93070090082105128003216229 17450641890394711500603043)
  ·
    refine ⟨26175962835592067250904565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17450641890394711500603043 26175962835592067250904565)
    ·
      refine ⟨2453996515836756304772303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26175962835592067250904565 2453996515836756304772303)
      ·
        refine ⟨3680994773755134457158455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2453996515836756304772303 3680994773755134457158455)
        ·
          refine ⟨5521492160632701685737683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680994773755134457158455 5521492160632701685737683)
          ·
            refine ⟨8282238240949052528606525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5521492160632701685737683 8282238240949052528606525)
            ·
              refine ⟨3105839340355894698227447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8282238240949052528606525 3105839340355894698227447)
              ·
                refine ⟨4658759010533842047341171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105839340355894698227447 4658759010533842047341171)
                ·
                  refine ⟨6988138515800763071011757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658759010533842047341171 6988138515800763071011757)
                  ·
                    refine ⟨2620551943425286151629409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6988138515800763071011757 2620551943425286151629409)
                    ·
                      refine ⟨1965413957568964613722057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2620551943425286151629409 1965413957568964613722057)
                      ·
                        rfl

theorem cell23_3827630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_3827630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827630 prefixEnd_3827630 := by exact prefixLift 3827630
  have htrace : WordTrace (prefixWord ++ tailWord_3827630) baseStart_3827630 baseEnd_3827630 := by
    simpa [prefixWord, tailWord_3827630, baseEnd_3827630] using wordTrace_append hprefix tailTrace_3827630
  have hstable : (prefixWord ++ tailWord_3827630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827630).length < 2 ^ (prefixWord ++ tailWord_3827630).sum := by decide
  have hdescent : baseEnd_3827630 < baseStart_3827630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827645 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_3827645 : Nat := 118140960795 + 3827645 * 2 ^ 59
def prefixEnd_3827645 : Nat := 4983230072969 + 3 ^ 40 * 3827645 * 2
def baseEnd_3827645 : Nat := 655140553259594018344829

theorem tailTrace_3827645 : CollatzResearch.WordTrace tailWord_3827645 prefixEnd_3827645 655140553259594018344829 := by
  unfold tailWord_3827645
  simp only [CollatzResearch.WordTrace]
  refine ⟨139605682218103349566620389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93070454812068899711080259 139605682218103349566620389)
  ·
    refine ⟨26176065415894378043741323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139605682218103349566620389 26176065415894378043741323)
    ·
      refine ⟨39264098123841567065611985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26176065415894378043741323 39264098123841567065611985)
      ·
        refine ⟨29448073592881175299208989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39264098123841567065611985 29448073592881175299208989)
        ·
          refine ⟨11043027597330440737203371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29448073592881175299208989 11043027597330440737203371)
          ·
            refine ⟨16564541395995661105805057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11043027597330440737203371 16564541395995661105805057)
            ·
              refine ⟨12423406046996745829353793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16564541395995661105805057 12423406046996745829353793)
              ·
                refine ⟨9317554535247559372015345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12423406046996745829353793 9317554535247559372015345)
                ·
                  refine ⟨6988165901435669529011509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9317554535247559372015345 6988165901435669529011509)
                  ·
                    refine ⟨655140553259594018344829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6988165901435669529011509 655140553259594018344829)
                    ·
                      rfl

theorem cell23_3827645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_3827645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827645 prefixEnd_3827645 := by exact prefixLift 3827645
  have htrace : WordTrace (prefixWord ++ tailWord_3827645) baseStart_3827645 baseEnd_3827645 := by
    simpa [prefixWord, tailWord_3827645, baseEnd_3827645] using wordTrace_append hprefix tailTrace_3827645
  have hstable : (prefixWord ++ tailWord_3827645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827645).length < 2 ^ (prefixWord ++ tailWord_3827645).sum := by decide
  have hdescent : baseEnd_3827645 < baseStart_3827645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827688 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 8]
def baseStart_3827688 : Nat := 118140960795 + 3827688 * 2 ^ 59
def prefixEnd_3827688 : Nat := 4983230072969 + 3 ^ 40 * 3827688 * 2
def baseEnd_3827688 : Nat := 218382637716325042977421

theorem tailTrace_3827688 : CollatzResearch.WordTrace tailWord_3827688 prefixEnd_3827688 218382637716325042977421 := by
  unfold tailWord_3827688
  simp only [CollatzResearch.WordTrace]
  refine ⟨69803625278473783955217859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93071500371298378606957145 69803625278473783955217859)
  ·
    refine ⟨104705437917710675932826789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69803625278473783955217859 104705437917710675932826789)
    ·
      refine ⟨19632269609570751737405023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104705437917710675932826789 19632269609570751737405023)
      ·
        refine ⟨29448404414356127606107535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19632269609570751737405023 29448404414356127606107535)
        ·
          refine ⟨44172606621534191409161303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29448404414356127606107535 44172606621534191409161303)
          ·
            refine ⟨66258909932301287113741955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44172606621534191409161303 66258909932301287113741955)
            ·
              refine ⟨99388364898451930670612933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66258909932301287113741955 99388364898451930670612933)
              ·
                refine ⟨18635318418459737000739925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99388364898451930670612933 18635318418459737000739925)
                ·
                  refine ⟨218382637716325042977421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18635318418459737000739925 218382637716325042977421)
                  ·
                    rfl

theorem cell23_3827688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 8].length) (baseStart_3827688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827688 prefixEnd_3827688 := by exact prefixLift 3827688
  have htrace : WordTrace (prefixWord ++ tailWord_3827688) baseStart_3827688 baseEnd_3827688 := by
    simpa [prefixWord, tailWord_3827688, baseEnd_3827688] using wordTrace_append hprefix tailTrace_3827688
  have hstable : (prefixWord ++ tailWord_3827688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827688).length < 2 ^ (prefixWord ++ tailWord_3827688).sum := by decide
  have hdescent : baseEnd_3827688 < baseStart_3827688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827705 : List Nat := [1, 2, 1, 3, 1, 4, 3, 2, 6]
def baseStart_3827705 : Nat := 118140960795 + 3827705 * 2 ^ 59
def prefixEnd_3827705 : Nat := 4983230072969 + 3 ^ 40 * 3827705 * 2
def baseEnd_3827705 : Nat := 218383607624227980031579

theorem tailTrace_3827705 : CollatzResearch.WordTrace tailWord_3827705 prefixEnd_3827705 218383607624227980031579 := by
  unfold tailWord_3827705
  simp only [CollatzResearch.WordTrace]
  refine ⟨139607870597885979813804569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93071913731923986542536379 139607870597885979813804569)
  ·
    refine ⟨104705902948414484860353427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139607870597885979813804569 104705902948414484860353427)
    ·
      refine ⟨157058854422621727290530141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104705902948414484860353427 157058854422621727290530141)
      ·
        refine ⟨58897070408483147733948803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157058854422621727290530141 58897070408483147733948803)
        ·
          refine ⟨88345605612724721600923205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58897070408483147733948803 88345605612724721600923205)
          ·
            refine ⟨16564801052385885300173101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88345605612724721600923205 16564801052385885300173101)
            ·
              refine ⟨6211800394644706987564913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16564801052385885300173101 6211800394644706987564913)
              ·
                refine ⟨4658850295983530240673685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6211800394644706987564913 4658850295983530240673685)
                ·
                  refine ⟨218383607624227980031579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4658850295983530240673685 218383607624227980031579)
                  ·
                    rfl

theorem cell23_3827705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 6].length) (baseStart_3827705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827705 prefixEnd_3827705 := by exact prefixLift 3827705
  have htrace : WordTrace (prefixWord ++ tailWord_3827705) baseStart_3827705 baseEnd_3827705 := by
    simpa [prefixWord, tailWord_3827705, baseEnd_3827705] using wordTrace_append hprefix tailTrace_3827705
  have hstable : (prefixWord ++ tailWord_3827705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827705).length < 2 ^ (prefixWord ++ tailWord_3827705).sum := by decide
  have hdescent : baseEnd_3827705 < baseStart_3827705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827708 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_3827708 : Nat := 118140960795 + 3827708 * 2 ^ 59
def prefixEnd_3827708 : Nat := 4983230072969 + 3 ^ 40 * 3827708 * 2
def baseEnd_3827708 : Nat := 1965454009060015308546697

theorem tailTrace_3827708 : CollatzResearch.WordTrace tailWord_3827708 prefixEnd_3827708 1965454009060015308546697 := by
  unfold tailWord_3827708
  simp only [CollatzResearch.WordTrace]
  refine ⟨69803990008437555663081889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93071986677916740884109185 69803990008437555663081889)
  ·
    refine ⟨52352992506328166747311417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69803990008437555663081889 52352992506328166747311417)
    ·
      refine ⟨39264744379746125060483563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52352992506328166747311417 39264744379746125060483563)
      ·
        refine ⟨58897116569619187590725345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39264744379746125060483563 58897116569619187590725345)
        ·
          refine ⟨44172837427214390693044009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58897116569619187590725345 44172837427214390693044009)
          ·
            refine ⟨33129628070410793019783007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44172837427214390693044009 33129628070410793019783007)
            ·
              refine ⟨49694442105616189529674511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33129628070410793019783007 49694442105616189529674511)
              ·
                refine ⟨74541663158424284294511767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49694442105616189529674511 74541663158424284294511767)
                ·
                  refine ⟨111812494737636426441767651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74541663158424284294511767 111812494737636426441767651)
                  ·
                    refine ⟨167718742106454639662651477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111812494737636426441767651 167718742106454639662651477)
                    ·
                      refine ⟨1965454009060015308546697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 167718742106454639662651477 1965454009060015308546697)
                      ·
                        rfl

theorem cell23_3827708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_3827708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827708 prefixEnd_3827708 := by exact prefixLift 3827708
  have htrace : WordTrace (prefixWord ++ tailWord_3827708) baseStart_3827708 baseEnd_3827708 := by
    simpa [prefixWord, tailWord_3827708, baseEnd_3827708] using wordTrace_append hprefix tailTrace_3827708
  have hstable : (prefixWord ++ tailWord_3827708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827708).length < 2 ^ (prefixWord ++ tailWord_3827708).sum := by decide
  have hdescent : baseEnd_3827708 < baseStart_3827708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827775 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 5]
def baseStart_3827775 : Nat := 118140960795 + 3827775 * 2 ^ 59
def prefixEnd_3827775 : Nat := 4983230072969 + 3 ^ 40 * 3827775 * 2
def baseEnd_3827775 : Nat := 1965488412263866546408889

theorem tailTrace_3827775 : CollatzResearch.WordTrace tailWord_3827775 prefixEnd_3827775 1965488412263866546408889 := by
  unfold tailWord_3827775
  simp only [CollatzResearch.WordTrace]
  refine ⟨139610423707632381768852779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93073615805088254512568519 139610423707632381768852779)
  ·
    refine ⟨209415635561448572653279169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139610423707632381768852779 209415635561448572653279169)
    ·
      refine ⟨157061726671086429489959377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209415635561448572653279169 157061726671086429489959377)
      ·
        refine ⟨117796295003314822117469533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157061726671086429489959377 117796295003314822117469533)
        ·
          refine ⟨44173610626243058294051075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117796295003314822117469533 44173610626243058294051075)
          ·
            refine ⟨66260415939364587441076613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44173610626243058294051075 66260415939364587441076613)
            ·
              refine ⟨12423827988630860145201865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66260415939364587441076613 12423827988630860145201865)
              ·
                refine ⟨9317870991473145108901399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12423827988630860145201865 9317870991473145108901399)
                ·
                  refine ⟨13976806487209717663352099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9317870991473145108901399 13976806487209717663352099)
                  ·
                    refine ⟨20965209730814576495028149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13976806487209717663352099 20965209730814576495028149)
                    ·
                      refine ⟨1965488412263866546408889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20965209730814576495028149 1965488412263866546408889)
                      ·
                        rfl

theorem cell23_3827775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_3827775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827775 prefixEnd_3827775 := by exact prefixLift 3827775
  have htrace : WordTrace (prefixWord ++ tailWord_3827775) baseStart_3827775 baseEnd_3827775 := by
    simpa [prefixWord, tailWord_3827775, baseEnd_3827775] using wordTrace_append hprefix tailTrace_3827775
  have hstable : (prefixWord ++ tailWord_3827775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827775).length < 2 ^ (prefixWord ++ tailWord_3827775).sum := by decide
  have hdescent : baseEnd_3827775 < baseStart_3827775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827785 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 1, 2, 4]
def baseStart_3827785 : Nat := 118140960795 + 3827785 * 2 ^ 59
def prefixEnd_3827785 : Nat := 4983230072969 + 3 ^ 40 * 3827785 * 2
def baseEnd_3827785 : Nat := 1965493547070411507283843

theorem tailTrace_3827785 : CollatzResearch.WordTrace tailWord_3827785 prefixEnd_3827785 1965493547070411507283843 := by
  unfold tailWord_3827785
  simp only [CollatzResearch.WordTrace]
  refine ⟨139610788437596153476716809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93073858958397435651144539 139610788437596153476716809)
  ·
    refine ⟨104708091328197115107537607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139610788437596153476716809 104708091328197115107537607)
    ·
      refine ⟨157062136992295672661306411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104708091328197115107537607 157062136992295672661306411)
      ·
        refine ⟨235593205488443508991959617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157062136992295672661306411 235593205488443508991959617)
        ·
          refine ⟨176694904116332631743969713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235593205488443508991959617 176694904116332631743969713)
          ·
            refine ⟨132521178087249473807977285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176694904116332631743969713 132521178087249473807977285)
            ·
              refine ⟨24847720891359276338995741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132521178087249473807977285 24847720891359276338995741)
              ·
                refine ⟨9317895334259728627123403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24847720891359276338995741 9317895334259728627123403)
                ·
                  refine ⟨13976843001389592940685105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9317895334259728627123403 13976843001389592940685105)
                  ·
                    refine ⟨10482632251042194705513829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13976843001389592940685105 10482632251042194705513829)
                    ·
                      refine ⟨1965493547070411507283843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10482632251042194705513829 1965493547070411507283843)
                      ·
                        rfl

theorem cell23_3827785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_3827785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827785 prefixEnd_3827785 := by exact prefixLift 3827785
  have htrace : WordTrace (prefixWord ++ tailWord_3827785) baseStart_3827785 baseEnd_3827785 := by
    simpa [prefixWord, tailWord_3827785, baseEnd_3827785] using wordTrace_append hprefix tailTrace_3827785
  have hstable : (prefixWord ++ tailWord_3827785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827785).length < 2 ^ (prefixWord ++ tailWord_3827785).sum := by decide
  have hdescent : baseEnd_3827785 < baseStart_3827785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827822 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_3827822 : Nat := 118140960795 + 3827822 * 2 ^ 59
def prefixEnd_3827822 : Nat := 4983230072969 + 3 ^ 40 * 3827822 * 2
def baseEnd_3827822 : Nat := 1965512545854627862521173

theorem tailTrace_3827822 : CollatzResearch.WordTrace tailWord_3827822 prefixEnd_3827822 1965512545854627862521173 := by
  unfold tailWord_3827822
  simp only [CollatzResearch.WordTrace]
  refine ⟨17451517242307763599476715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93074758625641405863875813 17451517242307763599476715)
  ·
    refine ⟨26177275863461645399215073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17451517242307763599476715 26177275863461645399215073)
    ·
      refine ⟨19632956897596234049411305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26177275863461645399215073 19632956897596234049411305)
      ·
        refine ⟨14724717673197175537058479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19632956897596234049411305 14724717673197175537058479)
        ·
          refine ⟨22087076509795763305587719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14724717673197175537058479 22087076509795763305587719)
          ·
            refine ⟨33130614764693644958381579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22087076509795763305587719 33130614764693644958381579)
            ·
              refine ⟨49695922147040467437572369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33130614764693644958381579 49695922147040467437572369)
              ·
                refine ⟨37271941610280350578179277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49695922147040467437572369 37271941610280350578179277)
                ·
                  refine ⟨13976978103855131466817229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37271941610280350578179277 13976978103855131466817229)
                  ·
                    refine ⟨5241366788945674300056461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13976978103855131466817229 5241366788945674300056461)
                    ·
                      refine ⟨1965512545854627862521173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5241366788945674300056461 1965512545854627862521173)
                      ·
                        rfl

theorem cell23_3827822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_3827822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827822 prefixEnd_3827822 := by exact prefixLift 3827822
  have htrace : WordTrace (prefixWord ++ tailWord_3827822) baseStart_3827822 baseEnd_3827822 := by
    simpa [prefixWord, tailWord_3827822, baseEnd_3827822] using wordTrace_append hprefix tailTrace_3827822
  have hstable : (prefixWord ++ tailWord_3827822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827822).length < 2 ^ (prefixWord ++ tailWord_3827822).sum := by decide
  have hdescent : baseEnd_3827822 < baseStart_3827822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827823 : List Nat := [1, 1, 2, 1, 3, 4, 4, 2, 1, 2, 2]
def baseStart_3827823 : Nat := 118140960795 + 3827823 * 2 ^ 59
def prefixEnd_3827823 : Nat := 4983230072969 + 3 ^ 40 * 3827823 * 2
def baseEnd_3827823 : Nat := 1965513059335282358608669

theorem tailTrace_3827823 : CollatzResearch.WordTrace tailWord_3827823 prefixEnd_3827823 1965513059335282358608669 := by
  unfold tailWord_3827823
  simp only [CollatzResearch.WordTrace]
  refine ⟨139612174411458485966600123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93074782940972323977733415 139612174411458485966600123)
  ·
    refine ⟨209418261617187728949900185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139612174411458485966600123 209418261617187728949900185)
    ·
      refine ⟨157063696212890796712425139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209418261617187728949900185 157063696212890796712425139)
      ·
        refine ⟨235595544319336195068637709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157063696212890796712425139 235595544319336195068637709)
        ·
          refine ⟨88348329119751073150739141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235595544319336195068637709 88348329119751073150739141)
          ·
            refine ⟨16565311709953326215763589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88348329119751073150739141 16565311709953326215763589)
            ·
              refine ⟨3105995945616248665455673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16565311709953326215763589 3105995945616248665455673)
              ·
                refine ⟨2329496959212186499091755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3105995945616248665455673 2329496959212186499091755)
                ·
                  refine ⟨3494245438818279748637633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329496959212186499091755 3494245438818279748637633)
                  ·
                    refine ⟨2620684079113709811478225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3494245438818279748637633 2620684079113709811478225)
                    ·
                      refine ⟨1965513059335282358608669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2620684079113709811478225 1965513059335282358608669)
                      ·
                        rfl

theorem cell23_3827823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 1, 2, 2].length) (baseStart_3827823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827823 prefixEnd_3827823 := by exact prefixLift 3827823
  have htrace : WordTrace (prefixWord ++ tailWord_3827823) baseStart_3827823 baseEnd_3827823 := by
    simpa [prefixWord, tailWord_3827823, baseEnd_3827823] using wordTrace_append hprefix tailTrace_3827823
  have hstable : (prefixWord ++ tailWord_3827823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827823).length < 2 ^ (prefixWord ++ tailWord_3827823).sum := by decide
  have hdescent : baseEnd_3827823 < baseStart_3827823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827849 : List Nat := [1, 2, 1, 1, 4, 2, 2, 4, 1, 3, 2]
def baseStart_3827849 : Nat := 118140960795 + 3827849 * 2 ^ 59
def prefixEnd_3827849 : Nat := 4983230072969 + 3 ^ 40 * 3827849 * 2
def baseEnd_3827849 : Nat := 1965526409832299256883549

theorem tailTrace_3827849 : CollatzResearch.WordTrace tailWord_3827849 prefixEnd_3827849 1965526409832299256883549 := by
  unfold tailWord_3827849
  simp only [CollatzResearch.WordTrace]
  refine ⟨139613122709364292407046601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93075415139576194938031067 139613122709364292407046601)
  ·
    refine ⟨104709842032023219305284951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139613122709364292407046601 104709842032023219305284951)
    ·
      refine ⟨157064763048034828957927427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104709842032023219305284951 157064763048034828957927427)
      ·
        refine ⟨235597144572052243436891141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157064763048034828957927427 235597144572052243436891141)
        ·
          refine ⟨44174464607259795644417089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235597144572052243436891141 44174464607259795644417089)
          ·
            refine ⟨33130848455444846733312817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44174464607259795644417089 33130848455444846733312817)
            ·
              refine ⟨24848136341583635049984613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33130848455444846733312817 24848136341583635049984613)
              ·
                refine ⟨4659025564046931571872115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24848136341583635049984613 4659025564046931571872115)
                ·
                  refine ⟨6988538346070397357808173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4659025564046931571872115 6988538346070397357808173)
                  ·
                    refine ⟨2620701879776399009178065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6988538346070397357808173 2620701879776399009178065)
                    ·
                      refine ⟨1965526409832299256883549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2620701879776399009178065 1965526409832299256883549)
                      ·
                        rfl

theorem cell23_3827849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 3, 2].length) (baseStart_3827849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827849 prefixEnd_3827849 := by exact prefixLift 3827849
  have htrace : WordTrace (prefixWord ++ tailWord_3827849) baseStart_3827849 baseEnd_3827849 := by
    simpa [prefixWord, tailWord_3827849, baseEnd_3827849] using wordTrace_append hprefix tailTrace_3827849
  have hstable : (prefixWord ++ tailWord_3827849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827849).length < 2 ^ (prefixWord ++ tailWord_3827849).sum := by decide
  have hdescent : baseEnd_3827849 < baseStart_3827849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827860 : List Nat := [2, 4, 2, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_3827860 : Nat := 118140960795 + 3827860 * 2 ^ 59
def prefixEnd_3827860 : Nat := 4983230072969 + 3 ^ 40 * 3827860 * 2
def baseEnd_3827860 : Nat := 1965532058119498713845999

theorem tailTrace_3827860 : CollatzResearch.WordTrace tailWord_3827860 prefixEnd_3827860 1965532058119498713845999 := by
  unfold tailWord_3827860
  simp only [CollatzResearch.WordTrace]
  refine ⟨69806761956162220642848517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93075682608216294190464689 69806761956162220642848517)
  ·
    refine ⟨13088767866780416370534097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69806761956162220642848517 13088767866780416370534097)
    ·
      refine ⟨9816575900085312277900573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13088767866780416370534097 9816575900085312277900573)
      ·
        refine ⟨3681215962531992104212715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9816575900085312277900573 3681215962531992104212715)
        ·
          refine ⟨5521823943797988156319073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3681215962531992104212715 5521823943797988156319073)
          ·
            refine ⟨4141367957848491117239305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5521823943797988156319073 4141367957848491117239305)
            ·
              refine ⟨3106025968386368337929479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4141367957848491117239305 3106025968386368337929479)
              ·
                refine ⟨4659038952579552506894219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106025968386368337929479 4659038952579552506894219)
                ·
                  refine ⟨6988558428869328760341329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4659038952579552506894219 6988558428869328760341329)
                  ·
                    refine ⟨5241418821651996570255997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6988558428869328760341329 5241418821651996570255997)
                    ·
                      refine ⟨1965532058119498713845999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5241418821651996570255997 1965532058119498713845999)
                      ·
                        rfl

theorem cell23_3827860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_3827860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827860 prefixEnd_3827860 := by exact prefixLift 3827860
  have htrace : WordTrace (prefixWord ++ tailWord_3827860) baseStart_3827860 baseEnd_3827860 := by
    simpa [prefixWord, tailWord_3827860, baseEnd_3827860] using wordTrace_append hprefix tailTrace_3827860
  have hstable : (prefixWord ++ tailWord_3827860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827860).length < 2 ^ (prefixWord ++ tailWord_3827860).sum := by decide
  have hdescent : baseEnd_3827860 < baseStart_3827860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827865 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 5]
def baseStart_3827865 : Nat := 118140960795 + 3827865 * 2 ^ 59
def prefixEnd_3827865 : Nat := 4983230072969 + 3 ^ 40 * 3827865 * 2
def baseEnd_3827865 : Nat := 1965534625522771194283475

theorem tailTrace_3827865 : CollatzResearch.WordTrace tailWord_3827865 prefixEnd_3827865 1965534625522771194283475 := by
  unfold tailWord_3827865
  simp only [CollatzResearch.WordTrace]
  refine ⟨139613706277306327139629049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93075804184870884759752699 139613706277306327139629049)
  ·
    refine ⟨104710279707979745354721787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139613706277306327139629049 104710279707979745354721787)
    ·
      refine ⟨157065419561969618032082681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104710279707979745354721787 157065419561969618032082681)
      ·
        refine ⟨117799064671477213524062011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157065419561969618032082681 117799064671477213524062011)
        ·
          refine ⟨176698597007215820286093017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117799064671477213524062011 176698597007215820286093017)
          ·
            refine ⟨132523947755411865214569763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176698597007215820286093017 132523947755411865214569763)
            ·
              refine ⟨198785921633117797821854645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132523947755411865214569763 198785921633117797821854645)
              ·
                refine ⟨18636180153104793545798873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198785921633117797821854645 18636180153104793545798873)
                ·
                  refine ⟨13977135114828595159349155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18636180153104793545798873 13977135114828595159349155)
                  ·
                    refine ⟨20965702672242892739023733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13977135114828595159349155 20965702672242892739023733)
                    ·
                      refine ⟨1965534625522771194283475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20965702672242892739023733 1965534625522771194283475)
                      ·
                        rfl

theorem cell23_3827865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_3827865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827865 prefixEnd_3827865 := by exact prefixLift 3827865
  have htrace : WordTrace (prefixWord ++ tailWord_3827865) baseStart_3827865 baseEnd_3827865 := by
    simpa [prefixWord, tailWord_3827865, baseEnd_3827865] using wordTrace_append hprefix tailTrace_3827865
  have hstable : (prefixWord ++ tailWord_3827865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827865).length < 2 ^ (prefixWord ++ tailWord_3827865).sum := by decide
  have hdescent : baseEnd_3827865 < baseStart_3827865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827915 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 1, 7]
def baseStart_3827915 : Nat := 118140960795 + 3827915 * 2 ^ 59
def prefixEnd_3827915 : Nat := 4983230072969 + 3 ^ 40 * 3827915 * 2
def baseEnd_3827915 : Nat := 655186766518498666219415

theorem tailTrace_3827915 : CollatzResearch.WordTrace tailWord_3827915 prefixEnd_3827915 655186766518498666219415 := by
  unfold tailWord_3827915
  simp only [CollatzResearch.WordTrace]
  refine ⟨139615529927125185678949199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93077019951416790452632799 139615529927125185678949199)
  ·
    refine ⟨209423294890687778518423799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139615529927125185678949199 209423294890687778518423799)
    ·
      refine ⟨314134942336031667777635699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209423294890687778518423799 314134942336031667777635699)
      ·
        refine ⟨471202413504047501666453549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314134942336031667777635699 471202413504047501666453549)
        ·
          refine ⟨176700905064017813124920081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471202413504047501666453549 176700905064017813124920081)
          ·
            refine ⟨132525678798013359843690061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176700905064017813124920081 132525678798013359843690061)
            ·
              refine ⟨49697129549255009941383773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132525678798013359843690061 49697129549255009941383773)
              ·
                refine ⟨18636423580970628728018915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49697129549255009941383773 18636423580970628728018915)
                ·
                  refine ⟨27954635371455943092028373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18636423580970628728018915 27954635371455943092028373)
                  ·
                    refine ⟨655186766518498666219415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27954635371455943092028373 655186766518498666219415)
                    ·
                      rfl

theorem cell23_3827915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 7].length) (baseStart_3827915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827915 prefixEnd_3827915 := by exact prefixLift 3827915
  have htrace : WordTrace (prefixWord ++ tailWord_3827915) baseStart_3827915 baseEnd_3827915 := by
    simpa [prefixWord, tailWord_3827915, baseEnd_3827915] using wordTrace_append hprefix tailTrace_3827915
  have hstable : (prefixWord ++ tailWord_3827915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827915).length < 2 ^ (prefixWord ++ tailWord_3827915).sum := by decide
  have hdescent : baseEnd_3827915 < baseStart_3827915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827969 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_3827969 : Nat := 118140960795 + 3827969 * 2 ^ 59
def prefixEnd_3827969 : Nat := 4983230072969 + 3 ^ 40 * 3827969 * 2
def baseEnd_3827969 : Nat := 1965588027510838787382997

theorem tailTrace_3827969 : CollatzResearch.WordTrace tailWord_3827969 prefixEnd_3827969 1965588027510838787382997 := by
  unfold tailWord_3827969
  simp only [CollatzResearch.WordTrace]
  refine ⟨139617499468929552901414961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93078332979286368600943307 139617499468929552901414961)
  ·
    refine ⟨104713124601697164676061221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139617499468929552901414961 104713124601697164676061221)
    ·
      refine ⟨19633710862818218376761479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104713124601697164676061221 19633710862818218376761479)
      ·
        refine ⟨29450566294227327565142219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19633710862818218376761479 29450566294227327565142219)
        ·
          refine ⟨44175849441340991347713329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29450566294227327565142219 44175849441340991347713329)
          ·
            refine ⟨33131887081005743510784997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44175849441340991347713329 33131887081005743510784997)
            ·
              refine ⟨6212228827688576908272187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33131887081005743510784997 6212228827688576908272187)
              ·
                refine ⟨9318343241532865362408281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212228827688576908272187 9318343241532865362408281)
                ·
                  refine ⟨6988757431149649021806211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9318343241532865362408281 6988757431149649021806211)
                  ·
                    refine ⟨10483136146724473532709317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6988757431149649021806211 10483136146724473532709317)
                    ·
                      refine ⟨1965588027510838787382997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10483136146724473532709317 1965588027510838787382997)
                      ·
                        rfl

theorem cell23_3827969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_3827969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827969 prefixEnd_3827969 := by exact prefixLift 3827969
  have htrace : WordTrace (prefixWord ++ tailWord_3827969) baseStart_3827969 baseEnd_3827969 := by
    simpa [prefixWord, tailWord_3827969, baseEnd_3827969] using wordTrace_append hprefix tailTrace_3827969
  have hstable : (prefixWord ++ tailWord_3827969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827969).length < 2 ^ (prefixWord ++ tailWord_3827969).sum := by decide
  have hdescent : baseEnd_3827969 < baseStart_3827969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827982 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3827982 : Nat := 118140960795 + 3827982 * 2 ^ 59
def prefixEnd_3827982 : Nat := 4983230072969 + 3 ^ 40 * 3827982 * 2
def baseEnd_3827982 : Nat := 1965594702759347236520437

theorem tailTrace_3827982 : CollatzResearch.WordTrace tailWord_3827982 prefixEnd_3827982 1965594702759347236520437 := by
  unfold tailWord_3827982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17452246702235307015204775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93078649078588304081092133 17452246702235307015204775)
  ·
    refine ⟨26178370053352960522807163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17452246702235307015204775 26178370053352960522807163)
    ·
      refine ⟨39267555080029440784210745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26178370053352960522807163 39267555080029440784210745)
      ·
        refine ⟨29450666310022080588158059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39267555080029440784210745 29450666310022080588158059)
        ·
          refine ⟨44175999465033120882237089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29450666310022080588158059 44175999465033120882237089)
          ·
            refine ⟨33131999598774840661677817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44175999465033120882237089 33131999598774840661677817)
            ·
              refine ⟨24848999699081130496258363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33131999598774840661677817 24848999699081130496258363)
              ·
                refine ⟨37273499548621695744387545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24848999699081130496258363 37273499548621695744387545)
                ·
                  refine ⟨27955124661466271808290659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37273499548621695744387545 27955124661466271808290659)
                  ·
                    refine ⟨41932686992199407712435989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27955124661466271808290659 41932686992199407712435989)
                    ·
                      refine ⟨1965594702759347236520437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41932686992199407712435989 1965594702759347236520437)
                      ·
                        rfl

theorem cell23_3827982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3827982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827982 prefixEnd_3827982 := by exact prefixLift 3827982
  have htrace : WordTrace (prefixWord ++ tailWord_3827982) baseStart_3827982 baseEnd_3827982 := by
    simpa [prefixWord, tailWord_3827982, baseEnd_3827982] using wordTrace_append hprefix tailTrace_3827982
  have hstable : (prefixWord ++ tailWord_3827982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827982).length < 2 ^ (prefixWord ++ tailWord_3827982).sum := by decide
  have hdescent : baseEnd_3827982 < baseStart_3827982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827989 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_3827989 : Nat := 118140960795 + 3827989 * 2 ^ 59
def prefixEnd_3827989 : Nat := 4983230072969 + 3 ^ 40 * 3827989 * 2
def baseEnd_3827989 : Nat := 1965598297123928709132905

theorem tailTrace_3827989 : CollatzResearch.WordTrace tailWord_3827989 prefixEnd_3827989 1965598297123928709132905 := by
  unfold tailWord_3827989
  simp only [CollatzResearch.WordTrace]
  refine ⟨139618228928857096317143021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93078819285904730878095347 139618228928857096317143021)
  ·
    refine ⟨52356835848321411118928633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139618228928857096317143021 52356835848321411118928633)
    ·
      refine ⟨39267626886241058339196475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52356835848321411118928633 39267626886241058339196475)
      ·
        refine ⟨58901440329361587508794713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39267626886241058339196475 58901440329361587508794713)
        ·
          refine ⟨44176080247021190631596035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58901440329361587508794713 44176080247021190631596035)
          ·
            refine ⟨66264120370531785947394053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44176080247021190631596035 66264120370531785947394053)
            ·
              refine ⟨12424522569474709865136385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66264120370531785947394053 12424522569474709865136385)
              ·
                refine ⟨9318391927106032398852289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12424522569474709865136385 9318391927106032398852289)
                ·
                  refine ⟨6988793945329524299139217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9318391927106032398852289 6988793945329524299139217)
                  ·
                    refine ⟨5241595458997143224354413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6988793945329524299139217 5241595458997143224354413)
                    ·
                      refine ⟨1965598297123928709132905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5241595458997143224354413 1965598297123928709132905)
                      ·
                        rfl

theorem cell23_3827989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_3827989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3827989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3827989 prefixEnd_3827989 := by exact prefixLift 3827989
  have htrace : WordTrace (prefixWord ++ tailWord_3827989) baseStart_3827989 baseEnd_3827989 := by
    simpa [prefixWord, tailWord_3827989, baseEnd_3827989] using wordTrace_append hprefix tailTrace_3827989
  have hstable : (prefixWord ++ tailWord_3827989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827989).length < 2 ^ (prefixWord ++ tailWord_3827989).sum := by decide
  have hdescent : baseEnd_3827989 < baseStart_3827989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828013 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_3828013 : Nat := 118140960795 + 3828013 * 2 ^ 59
def prefixEnd_3828013 : Nat := 4983230072969 + 3 ^ 40 * 3828013 * 2
def baseEnd_3828013 : Nat := 655203540219878871744265

theorem tailTrace_3828013 : CollatzResearch.WordTrace tailWord_3828013 prefixEnd_3828013 655203540219878871744265 := by
  unfold tailWord_3828013
  simp only [CollatzResearch.WordTrace]
  refine ⟨139619104280770148416016693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93079402853846765610677795 139619104280770148416016693)
  ·
    refine ⟨13089291026322201414001565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139619104280770148416016693 13089291026322201414001565)
    ·
      refine ⟨4908484134870825530250587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13089291026322201414001565 4908484134870825530250587)
      ·
        refine ⟨7362726202306238295375881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4908484134870825530250587 7362726202306238295375881)
        ·
          refine ⟨5522044651729678721531911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7362726202306238295375881 5522044651729678721531911)
          ·
            refine ⟨8283066977594518082297867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522044651729678721531911 8283066977594518082297867)
            ·
              refine ⟨12424600466391777123446801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8283066977594518082297867 12424600466391777123446801)
              ·
                refine ⟨9318450349793832842585101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12424600466391777123446801 9318450349793832842585101)
                ·
                  refine ⟨3494418881172687315969413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9318450349793832842585101 3494418881172687315969413)
                  ·
                    refine ⟨655203540219878871744265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3494418881172687315969413 655203540219878871744265)
                    ·
                      rfl

theorem cell23_3828013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_3828013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828013 prefixEnd_3828013 := by exact prefixLift 3828013
  have htrace : WordTrace (prefixWord ++ tailWord_3828013) baseStart_3828013 baseEnd_3828013 := by
    simpa [prefixWord, tailWord_3828013, baseEnd_3828013] using wordTrace_append hprefix tailTrace_3828013
  have hstable : (prefixWord ++ tailWord_3828013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828013).length < 2 ^ (prefixWord ++ tailWord_3828013).sum := by decide
  have hdescent : baseEnd_3828013 < baseStart_3828013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828039 : List Nat := [1, 1, 4, 1, 2, 2, 3, 3, 1, 5]
def baseStart_3828039 : Nat := 118140960795 + 3828039 * 2 ^ 59
def prefixEnd_3828039 : Nat := 4983230072969 + 3 ^ 40 * 3828039 * 2
def baseEnd_3828039 : Nat := 655207990385551171169225

theorem tailTrace_3828039 : CollatzResearch.WordTrace tailWord_3828039 prefixEnd_3828039 655207990385551171169225 := by
  unfold tailWord_3828039
  simp only [CollatzResearch.WordTrace]
  refine ⟨139620052578675954856463171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93080035052450636570975447 139620052578675954856463171)
  ·
    refine ⟨209430078868013932284694757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139620052578675954856463171 209430078868013932284694757)
    ·
      refine ⟨39268139787752612303380267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209430078868013932284694757 39268139787752612303380267)
      ·
        refine ⟨58902209681628918455070401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39268139787752612303380267 58902209681628918455070401)
        ·
          refine ⟨44176657261221688841302801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58902209681628918455070401 44176657261221688841302801)
          ·
            refine ⟨33132492945916266630977101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44176657261221688841302801 33132492945916266630977101)
            ·
              refine ⟨12424684854718599986616413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33132492945916266630977101 12424684854718599986616413)
              ·
                refine ⟨4659256820519474994981155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12424684854718599986616413 4659256820519474994981155)
                ·
                  refine ⟨6988885230779212492471733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4659256820519474994981155 6988885230779212492471733)
                  ·
                    refine ⟨655207990385551171169225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6988885230779212492471733 655207990385551171169225)
                    ·
                      rfl

theorem cell23_3828039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_3828039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828039 prefixEnd_3828039 := by exact prefixLift 3828039
  have htrace : WordTrace (prefixWord ++ tailWord_3828039) baseStart_3828039 baseEnd_3828039 := by
    simpa [prefixWord, tailWord_3828039, baseEnd_3828039] using wordTrace_append hprefix tailTrace_3828039
  have hstable : (prefixWord ++ tailWord_3828039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828039).length < 2 ^ (prefixWord ++ tailWord_3828039).sum := by decide
  have hdescent : baseEnd_3828039 < baseStart_3828039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828053 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3828053 : Nat := 118140960795 + 3828053 * 2 ^ 59
def prefixEnd_3828053 : Nat := 4983230072969 + 3 ^ 40 * 3828053 * 2
def baseEnd_3828053 : Nat := 1965631159885816458732611

theorem tailTrace_3828053 : CollatzResearch.WordTrace tailWord_3828053 prefixEnd_3828053 1965631159885816458732611 := by
  unfold tailWord_3828053
  simp only [CollatzResearch.WordTrace]
  refine ⟨139620563200625235247472813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93080375467083490164981875 139620563200625235247472813)
  ·
    refine ⟨52357711200234463217802305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139620563200625235247472813 52357711200234463217802305)
    ·
      refine ⟨39268283400175847413351729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52357711200234463217802305 39268283400175847413351729)
      ·
        refine ⟨29451212550131885560013797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39268283400175847413351729 29451212550131885560013797)
        ·
          refine ⟨5522102353149728542502587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29451212550131885560013797 5522102353149728542502587)
          ·
            refine ⟨8283153529724592813753881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522102353149728542502587 8283153529724592813753881)
            ·
              refine ⟨6212365147293444610315411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8283153529724592813753881 6212365147293444610315411)
              ·
                refine ⟨9318547720940166915473117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212365147293444610315411 9318547720940166915473117)
                ·
                  refine ⟨3494455395352562593302419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9318547720940166915473117 3494455395352562593302419)
                  ·
                    refine ⟨5241683093028843889953629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3494455395352562593302419 5241683093028843889953629)
                    ·
                      refine ⟨1965631159885816458732611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5241683093028843889953629 1965631159885816458732611)
                      ·
                        rfl

theorem cell23_3828053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3828053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828053 prefixEnd_3828053 := by exact prefixLift 3828053
  have htrace : WordTrace (prefixWord ++ tailWord_3828053) baseStart_3828053 baseEnd_3828053 := by
    simpa [prefixWord, tailWord_3828053, baseEnd_3828053] using wordTrace_append hprefix tailTrace_3828053
  have hstable : (prefixWord ++ tailWord_3828053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828053).length < 2 ^ (prefixWord ++ tailWord_3828053).sum := by decide
  have hdescent : baseEnd_3828053 < baseStart_3828053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828069 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 1, 6]
def baseStart_3828069 : Nat := 118140960795 + 3828069 * 2 ^ 59
def prefixEnd_3828069 : Nat := 4983230072969 + 3 ^ 40 * 3828069 * 2
def baseEnd_3828069 : Nat := 655213125192096132044179

theorem tailTrace_3828069 : CollatzResearch.WordTrace tailWord_3828069 prefixEnd_3828069 655213125192096132044179 := by
  unfold tailWord_3828069
  simp only [CollatzResearch.WordTrace]
  refine ⟨139621146768567269980055261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93080764512378179986703507 139621146768567269980055261)
  ·
    refine ⟨52357930038212726242520723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139621146768567269980055261 52357930038212726242520723)
    ·
      refine ⟨78536895057319089363781085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52357930038212726242520723 78536895057319089363781085)
      ·
        refine ⟨29451335646494658511417907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78536895057319089363781085 29451335646494658511417907)
        ·
          refine ⟨44177003469741987767126861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29451335646494658511417907 44177003469741987767126861)
          ·
            refine ⟨16566376301153245412672573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44177003469741987767126861 16566376301153245412672573)
            ·
              refine ⟨6212391112932467029752215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16566376301153245412672573 6212391112932467029752215)
              ·
                refine ⟨9318586669398700544628323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212391112932467029752215 9318586669398700544628323)
                ·
                  refine ⟨13977880004098050816942485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9318586669398700544628323 13977880004098050816942485)
                  ·
                    refine ⟨655213125192096132044179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13977880004098050816942485 655213125192096132044179)
                    ·
                      rfl

theorem cell23_3828069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_3828069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828069 prefixEnd_3828069 := by exact prefixLift 3828069
  have htrace : WordTrace (prefixWord ++ tailWord_3828069) baseStart_3828069 baseEnd_3828069 := by
    simpa [prefixWord, tailWord_3828069, baseEnd_3828069] using wordTrace_append hprefix tailTrace_3828069
  have hstable : (prefixWord ++ tailWord_3828069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828069).length < 2 ^ (prefixWord ++ tailWord_3828069).sum := by decide
  have hdescent : baseEnd_3828069 < baseStart_3828069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828099 : List Nat := [1, 1, 1, 3, 6, 2, 9]
def baseStart_3828099 : Nat := 118140960795 + 3828099 * 2 ^ 59
def prefixEnd_3828099 : Nat := 4983230072969 + 3 ^ 40 * 3828099 * 2
def baseEnd_3828099 : Nat := 24267342962912633071079

theorem tailTrace_3828099 : CollatzResearch.WordTrace tailWord_3828099 prefixEnd_3828099 24267342962912633071079 := by
  unfold tailWord_3828099
  simp only [CollatzResearch.WordTrace]
  refine ⟨139622240958458585103647351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93081493972305723402431567 139622240958458585103647351)
  ·
    refine ⟨209433361437687877655471027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139622240958458585103647351 209433361437687877655471027)
    ·
      refine ⟨314150042156531816483206541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209433361437687877655471027 314150042156531816483206541)
      ·
        refine ⟨117806265808699431181202453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314150042156531816483206541 117806265808699431181202453)
        ·
          refine ⟨5522168709782785836618865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117806265808699431181202453 5522168709782785836618865)
          ·
            refine ⟨4141626532337089377464149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5522168709782785836618865 4141626532337089377464149)
            ·
              refine ⟨24267342962912633071079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4141626532337089377464149 24267342962912633071079)
              ·
                rfl

theorem cell23_3828099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 9].length) (baseStart_3828099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828099 prefixEnd_3828099 := by exact prefixLift 3828099
  have htrace : WordTrace (prefixWord ++ tailWord_3828099) baseStart_3828099 baseEnd_3828099 := by
    simpa [prefixWord, tailWord_3828099, baseEnd_3828099] using wordTrace_append hprefix tailTrace_3828099
  have hstable : (prefixWord ++ tailWord_3828099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828099).length < 2 ^ (prefixWord ++ tailWord_3828099).sum := by decide
  have hdescent : baseEnd_3828099 < baseStart_3828099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828110 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2]
def baseStart_3828110 : Nat := 118140960795 + 3828110 * 2 ^ 59
def prefixEnd_3828110 : Nat := 4983230072969 + 3 ^ 40 * 3828110 * 2
def baseEnd_3828110 : Nat := 1965660428283122735719849

theorem tailTrace_3828110 : CollatzResearch.WordTrace tailWord_3828110 prefixEnd_3828110 1965660428283122735719849 := by
  unfold tailWord_3828110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17452830270177341747787223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93081761440945822654865189 17452830270177341747787223)
  ·
    refine ⟨26179245405266012621680835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17452830270177341747787223 26179245405266012621680835)
    ·
      refine ⟨39268868107899018932521253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26179245405266012621680835 39268868107899018932521253)
      ·
        refine ⟨7362912770231066049847735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39268868107899018932521253 7362912770231066049847735)
        ·
          refine ⟨11044369155346599074771603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362912770231066049847735 11044369155346599074771603)
          ·
            refine ⟨16566553733019898612157405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11044369155346599074771603 16566553733019898612157405)
            ·
              refine ⟨6212457649882461979559027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16566553733019898612157405 6212457649882461979559027)
              ·
                refine ⟨9318686474823692969338541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212457649882461979559027 9318686474823692969338541)
                ·
                  refine ⟨3494507428058884863501953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9318686474823692969338541 3494507428058884863501953)
                  ·
                    refine ⟨2620880571044163647626465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3494507428058884863501953 2620880571044163647626465)
                    ·
                      refine ⟨1965660428283122735719849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2620880571044163647626465 1965660428283122735719849)
                      ·
                        rfl

theorem cell23_3828110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_3828110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828110 prefixEnd_3828110 := by exact prefixLift 3828110
  have htrace : WordTrace (prefixWord ++ tailWord_3828110) baseStart_3828110 baseEnd_3828110 := by
    simpa [prefixWord, tailWord_3828110, baseEnd_3828110] using wordTrace_append hprefix tailTrace_3828110
  have hstable : (prefixWord ++ tailWord_3828110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828110).length < 2 ^ (prefixWord ++ tailWord_3828110).sum := by decide
  have hdescent : baseEnd_3828110 < baseStart_3828110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828116 : List Nat := [2, 4, 2, 1, 3, 1, 2, 8]
def baseStart_3828116 : Nat := 118140960795 + 3828116 * 2 ^ 59
def prefixEnd_3828116 : Nat := 4983230072969 + 3 ^ 40 * 3828116 * 2
def baseEnd_3828116 : Nat := 72802352191372211564623

theorem tailTrace_3828116 : CollatzResearch.WordTrace tailWord_3828116 prefixEnd_3828116 72802352191372211564623 := by
  unfold tailWord_3828116
  simp only [CollatzResearch.WordTrace]
  refine ⟨69811430499698498503508101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93081907332931331338010801 69811430499698498503508101)
  ·
    refine ⟨13089643218693468469407769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69811430499698498503508101 13089643218693468469407769)
    ·
      refine ⟨9817232414020101352055827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13089643218693468469407769 9817232414020101352055827)
      ·
        refine ⟨14725848621030152028083741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9817232414020101352055827 14725848621030152028083741)
        ·
          refine ⟨5522193232886307010531403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14725848621030152028083741 5522193232886307010531403)
          ·
            refine ⟨8283289849329460515797105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522193232886307010531403 8283289849329460515797105)
            ·
              refine ⟨6212467386997095386847829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8283289849329460515797105 6212467386997095386847829)
              ·
                refine ⟨72802352191372211564623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6212467386997095386847829 72802352191372211564623)
                ·
                  rfl

theorem cell23_3828116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 8].length) (baseStart_3828116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828116 prefixEnd_3828116 := by exact prefixLift 3828116
  have htrace : WordTrace (prefixWord ++ tailWord_3828116) baseStart_3828116 baseEnd_3828116 := by
    simpa [prefixWord, tailWord_3828116, baseEnd_3828116] using wordTrace_append hprefix tailTrace_3828116
  have hstable : (prefixWord ++ tailWord_3828116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828116).length < 2 ^ (prefixWord ++ tailWord_3828116).sum := by decide
  have hdescent : baseEnd_3828116 < baseStart_3828116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828120 : List Nat := [2, 1, 2, 5, 1, 3, 2, 1, 2, 4]
def baseStart_3828120 : Nat := 118140960795 + 3828120 * 2 ^ 59
def prefixEnd_3828120 : Nat := 4983230072969 + 3 ^ 40 * 3828120 * 2
def baseEnd_3828120 : Nat := 655221854363222565531601

theorem tailTrace_3828120 : CollatzResearch.WordTrace tailWord_3828120 prefixEnd_3828120 655221854363222565531601 := by
  unfold tailWord_3828120
  simp only [CollatzResearch.WordTrace]
  refine ⟨69811503445691252845080907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93082004594255003793441209 69811503445691252845080907)
  ·
    refine ⟨104717255168536879267621361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69811503445691252845080907 104717255168536879267621361)
    ·
      refine ⟨78537941376402659450716021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104717255168536879267621361 78537941376402659450716021)
      ·
        refine ⟨7362932004037749323504627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78537941376402659450716021 7362932004037749323504627)
        ·
          refine ⟨11044398006056623985256941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362932004037749323504627 11044398006056623985256941)
          ·
            refine ⟨4141649252271233994471353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11044398006056623985256941 4141649252271233994471353)
            ·
              refine ⟨3106236939203425495853515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4141649252271233994471353 3106236939203425495853515)
              ·
                refine ⟨4659355408805138243780273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106236939203425495853515 4659355408805138243780273)
                ·
                  refine ⟨3494516556603853682835205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4659355408805138243780273 3494516556603853682835205)
                  ·
                    refine ⟨655221854363222565531601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3494516556603853682835205 655221854363222565531601)
                    ·
                      rfl

theorem cell23_3828120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_3828120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828120 prefixEnd_3828120 := by exact prefixLift 3828120
  have htrace : WordTrace (prefixWord ++ tailWord_3828120) baseStart_3828120 baseEnd_3828120 := by
    simpa [prefixWord, tailWord_3828120, baseEnd_3828120] using wordTrace_append hprefix tailTrace_3828120
  have hstable : (prefixWord ++ tailWord_3828120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828120).length < 2 ^ (prefixWord ++ tailWord_3828120).sum := by decide
  have hdescent : baseEnd_3828120 < baseStart_3828120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828161 : List Nat := [1, 2, 7, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3828161 : Nat := 118140960795 + 3828161 * 2 ^ 59
def prefixEnd_3828161 : Nat := 4983230072969 + 3 ^ 40 * 3828161 * 2
def baseEnd_3828161 : Nat := 1965686615796502036182115

theorem tailTrace_3828161 : CollatzResearch.WordTrace tailWord_3828161 prefixEnd_3828161 1965686615796502036182115 := by
  unfold tailWord_3828161
  simp only [CollatzResearch.WordTrace]
  refine ⟨139624502284233969692404337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93083001522822646461602891 139624502284233969692404337)
  ·
    refine ⟨104718376713175477269303253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139624502284233969692404337 104718376713175477269303253)
    ·
      refine ⟨2454336954215050248499295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 104718376713175477269303253 2454336954215050248499295)
      ·
        refine ⟨3681505431322575372748943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2454336954215050248499295 3681505431322575372748943)
        ·
          refine ⟨5522258146983863059123415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3681505431322575372748943 5522258146983863059123415)
          ·
            refine ⟨8283387220475794588685123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522258146983863059123415 8283387220475794588685123)
            ·
              refine ⟨12425080830713691883027685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8283387220475794588685123 12425080830713691883027685)
              ·
                refine ⟨2329702655758817228067691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12425080830713691883027685 2329702655758817228067691)
                ·
                  refine ⟨3494553983638225842101537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329702655758817228067691 3494553983638225842101537)
                  ·
                    refine ⟨2620915487728669381576153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3494553983638225842101537 2620915487728669381576153)
                    ·
                      refine ⟨1965686615796502036182115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2620915487728669381576153 1965686615796502036182115)
                      ·
                        rfl

theorem cell23_3828161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3828161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828161 prefixEnd_3828161 := by exact prefixLift 3828161
  have htrace : WordTrace (prefixWord ++ tailWord_3828161) baseStart_3828161 baseEnd_3828161 := by
    simpa [prefixWord, tailWord_3828161, baseEnd_3828161] using wordTrace_append hprefix tailTrace_3828161
  have hstable : (prefixWord ++ tailWord_3828161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828161).length < 2 ^ (prefixWord ++ tailWord_3828161).sum := by decide
  have hdescent : baseEnd_3828161 < baseStart_3828161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828169 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 2, 4, 3]
def baseStart_3828169 : Nat := 118140960795 + 3828169 * 2 ^ 59
def prefixEnd_3828169 : Nat := 4983230072969 + 3 ^ 40 * 3828169 * 2
def baseEnd_3828169 : Nat := 1965690723641738004882077

theorem tailTrace_3828169 : CollatzResearch.WordTrace tailWord_3828169 prefixEnd_3828169 1965690723641738004882077 := by
  unfold tailWord_3828169
  simp only [CollatzResearch.WordTrace]
  refine ⟨139624794068204987058695561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93083196045469991372463707 139624794068204987058695561)
  ·
    refine ⟨104718595551153740294021671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139624794068204987058695561 104718595551153740294021671)
    ·
      refine ⟨157077893326730610441032507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104718595551153740294021671 157077893326730610441032507)
      ·
        refine ⟨235616839990095915661548761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157077893326730610441032507 235616839990095915661548761)
        ·
          refine ⟨176712629992571936746161571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235616839990095915661548761 176712629992571936746161571)
          ·
            refine ⟨265068944988857905119242357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176712629992571936746161571 265068944988857905119242357)
            ·
              refine ⟨24850213592705428604928971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265068944988857905119242357 24850213592705428604928971)
              ·
                refine ⟨37275320389058142907393457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24850213592705428604928971 37275320389058142907393457)
                ·
                  refine ⟨27956490291793607180545093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37275320389058142907393457 27956490291793607180545093)
                  ·
                    refine ⟨5241841929711301346352205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27956490291793607180545093 5241841929711301346352205)
                    ·
                      refine ⟨1965690723641738004882077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5241841929711301346352205 1965690723641738004882077)
                      ·
                        rfl

theorem cell23_3828169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 4, 3].length) (baseStart_3828169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828169 prefixEnd_3828169 := by exact prefixLift 3828169
  have htrace : WordTrace (prefixWord ++ tailWord_3828169) baseStart_3828169 baseEnd_3828169 := by
    simpa [prefixWord, tailWord_3828169, baseEnd_3828169] using wordTrace_append hprefix tailTrace_3828169
  have hstable : (prefixWord ++ tailWord_3828169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828169).length < 2 ^ (prefixWord ++ tailWord_3828169).sum := by decide
  have hdescent : baseEnd_3828169 < baseStart_3828169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828229 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_3828229 : Nat := 118140960795 + 3828229 * 2 ^ 59
def prefixEnd_3828229 : Nat := 4983230072969 + 3 ^ 40 * 3828229 * 2
def baseEnd_3828229 : Nat := 1965721532481007770131801

theorem tailTrace_3828229 : CollatzResearch.WordTrace tailWord_3828229 prefixEnd_3828229 1965721532481007770131801 := by
  unfold tailWord_3828229
  simp only [CollatzResearch.WordTrace]
  refine ⟨139626982447987617305879741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93084654965325078203919827 139626982447987617305879741)
  ·
    refine ⟨52360118417995356489704903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139626982447987617305879741 52360118417995356489704903)
    ·
      refine ⟨78540177626993034734557355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52360118417995356489704903 78540177626993034734557355)
      ·
        refine ⟨117810266440489552101836033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78540177626993034734557355 117810266440489552101836033)
        ·
          refine ⟨88357699830367164076377025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117810266440489552101836033 88357699830367164076377025)
          ·
            refine ⟨66268274872775373057282769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88357699830367164076377025 66268274872775373057282769)
            ·
              refine ⟨49701206154581529792962077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66268274872775373057282769 49701206154581529792962077)
              ·
                refine ⟨18637952307968073672360779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49701206154581529792962077 18637952307968073672360779)
                ·
                  refine ⟨27956928461952110508541169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18637952307968073672360779 27956928461952110508541169)
                  ·
                    refine ⟨20967696346464082881405877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27956928461952110508541169 20967696346464082881405877)
                    ·
                      refine ⟨1965721532481007770131801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20967696346464082881405877 1965721532481007770131801)
                      ·
                        rfl

theorem cell23_3828229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_3828229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828229 prefixEnd_3828229 := by exact prefixLift 3828229
  have htrace : WordTrace (prefixWord ++ tailWord_3828229) baseStart_3828229 baseEnd_3828229 := by
    simpa [prefixWord, tailWord_3828229, baseEnd_3828229] using wordTrace_append hprefix tailTrace_3828229
  have hstable : (prefixWord ++ tailWord_3828229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828229).length < 2 ^ (prefixWord ++ tailWord_3828229).sum := by decide
  have hdescent : baseEnd_3828229 < baseStart_3828229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828239 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 4]
def baseStart_3828239 : Nat := 118140960795 + 3828239 * 2 ^ 59
def prefixEnd_3828239 : Nat := 4983230072969 + 3 ^ 40 * 3828239 * 2
def baseEnd_3828239 : Nat := 1965726667287552731006755

theorem tailTrace_3828239 : CollatzResearch.WordTrace tailWord_3828239 prefixEnd_3828239 1965726667287552731006755 := by
  unfold tailWord_3828239
  simp only [CollatzResearch.WordTrace]
  refine ⟨139627347177951389013743771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93084898118634259342495847 139627347177951389013743771)
  ·
    refine ⟨209441020766927083520615657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139627347177951389013743771 209441020766927083520615657)
    ·
      refine ⟨157080765575195312640461743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209441020766927083520615657 157080765575195312640461743)
      ·
        refine ⟨235621148362792968960692615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157080765575195312640461743 235621148362792968960692615)
        ·
          refine ⟨353431722544189453441038923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235621148362792968960692615 353431722544189453441038923)
          ·
            refine ⟨530147583816284180161558385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353431722544189453441038923 530147583816284180161558385)
            ·
              refine ⟨397610687862213135121168789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530147583816284180161558385 397610687862213135121168789)
              ·
                refine ⟨18638000993541240708804787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 397610687862213135121168789 18638000993541240708804787)
                ·
                  refine ⟨27957001490311861063207181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18638000993541240708804787 27957001490311861063207181)
                  ·
                    refine ⟨10483875558866947898702693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27957001490311861063207181 10483875558866947898702693)
                    ·
                      refine ⟨1965726667287552731006755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10483875558866947898702693 1965726667287552731006755)
                      ·
                        rfl

theorem cell23_3828239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_3828239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828239 prefixEnd_3828239 := by exact prefixLift 3828239
  have htrace : WordTrace (prefixWord ++ tailWord_3828239) baseStart_3828239 baseEnd_3828239 := by
    simpa [prefixWord, tailWord_3828239, baseEnd_3828239] using wordTrace_append hprefix tailTrace_3828239
  have hstable : (prefixWord ++ tailWord_3828239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828239).length < 2 ^ (prefixWord ++ tailWord_3828239).sum := by decide
  have hdescent : baseEnd_3828239 < baseStart_3828239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828279 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 8]
def baseStart_3828279 : Nat := 118140960795 + 3828279 * 2 ^ 59
def prefixEnd_3828279 : Nat := 4983230072969 + 3 ^ 40 * 3828279 * 2
def baseEnd_3828279 : Nat := 218416356279303619389619

theorem tailTrace_3828279 : CollatzResearch.WordTrace tailWord_3828279 prefixEnd_3828279 218416356279303619389619 := by
  unfold tailWord_3828279
  simp only [CollatzResearch.WordTrace]
  refine ⟨139628806097806475845199891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93085870731870983896799927 139628806097806475845199891)
  ·
    refine ⟨209443209146709713767799837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139628806097806475845199891 209443209146709713767799837)
    ·
      refine ⟨78541203430016142662924939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209443209146709713767799837 78541203430016142662924939)
      ·
        refine ⟨117811805145024213994387409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78541203430016142662924939 117811805145024213994387409)
        ·
          refine ⟨88358853858768160495790557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117811805145024213994387409 88358853858768160495790557)
          ·
            refine ⟨33134570197038060185921459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88358853858768160495790557 33134570197038060185921459)
            ·
              refine ⟨49701855295557090278882189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33134570197038060185921459 49701855295557090278882189)
              ·
                refine ⟨18638195735833908854580821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49701855295557090278882189 18638195735833908854580821)
                ·
                  refine ⟨218416356279303619389619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18638195735833908854580821 218416356279303619389619)
                  ·
                    rfl

theorem cell23_3828279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 8].length) (baseStart_3828279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828279 prefixEnd_3828279 := by exact prefixLift 3828279
  have htrace : WordTrace (prefixWord ++ tailWord_3828279) baseStart_3828279 baseEnd_3828279 := by
    simpa [prefixWord, tailWord_3828279, baseEnd_3828279] using wordTrace_append hprefix tailTrace_3828279
  have hstable : (prefixWord ++ tailWord_3828279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828279).length < 2 ^ (prefixWord ++ tailWord_3828279).sum := by decide
  have hdescent : baseEnd_3828279 < baseStart_3828279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828299 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 6]
def baseStart_3828299 : Nat := 118140960795 + 3828299 * 2 ^ 59
def prefixEnd_3828299 : Nat := 4983230072969 + 3 ^ 40 * 3828299 * 2
def baseEnd_3828299 : Nat := 1965757476126822496256479

theorem tailTrace_3828299 : CollatzResearch.WordTrace tailWord_3828299 prefixEnd_3828299 1965757476126822496256479 := by
  unfold tailWord_3828299
  simp only [CollatzResearch.WordTrace]
  refine ⟨139629535557734019260927951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93086357038489346173951967 139629535557734019260927951)
  ·
    refine ⟨209444303336601028891391927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139629535557734019260927951 209444303336601028891391927)
    ·
      refine ⟨314166455004901543337087891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209444303336601028891391927 314166455004901543337087891)
      ·
        refine ⟨471249682507352315005631837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314166455004901543337087891 471249682507352315005631837)
        ·
          refine ⟨176718630940257118127111939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471249682507352315005631837 176718630940257118127111939)
          ·
            refine ⟨265077946410385677190667909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176718630940257118127111939 265077946410385677190667909)
            ·
              refine ⟨49702114951947314473250233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265077946410385677190667909 49702114951947314473250233)
              ·
                refine ⟨37276586213960485854937675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49702114951947314473250233 37276586213960485854937675)
                ·
                  refine ⟨55914879320940728782406513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37276586213960485854937675 55914879320940728782406513)
                  ·
                    refine ⟨41936159490705546586804885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55914879320940728782406513 41936159490705546586804885)
                    ·
                      refine ⟨1965757476126822496256479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41936159490705546586804885 1965757476126822496256479)
                      ·
                        rfl

theorem cell23_3828299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_3828299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828299 prefixEnd_3828299 := by exact prefixLift 3828299
  have htrace : WordTrace (prefixWord ++ tailWord_3828299) baseStart_3828299 baseEnd_3828299 := by
    simpa [prefixWord, tailWord_3828299, baseEnd_3828299] using wordTrace_append hprefix tailTrace_3828299
  have hstable : (prefixWord ++ tailWord_3828299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828299).length < 2 ^ (prefixWord ++ tailWord_3828299).sum := by decide
  have hdescent : baseEnd_3828299 < baseStart_3828299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828319 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 7]
def baseStart_3828319 : Nat := 118140960795 + 3828319 * 2 ^ 59
def prefixEnd_3828319 : Nat := 4983230072969 + 3 ^ 40 * 3828319 * 2
def baseEnd_3828319 : Nat := 1965767745739912418006387

theorem tailTrace_3828319 : CollatzResearch.WordTrace tailWord_3828319 prefixEnd_3828319 1965767745739912418006387 := by
  unfold tailWord_3828319
  simp only [CollatzResearch.WordTrace]
  refine ⟨139630265017661562676656011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93086843345107708451104007 139630265017661562676656011)
  ·
    refine ⟨209445397526492344014984017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139630265017661562676656011 209445397526492344014984017)
    ·
      refine ⟨157084048144869258011238013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209445397526492344014984017 157084048144869258011238013)
      ·
        refine ⟨58906518054325971754214255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157084048144869258011238013 58906518054325971754214255)
        ·
          refine ⟨88359777081488957631321383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58906518054325971754214255 88359777081488957631321383)
          ·
            refine ⟨132539665622233436446982075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88359777081488957631321383 132539665622233436446982075)
            ·
              refine ⟨198809498433350154670473113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132539665622233436446982075 198809498433350154670473113)
              ·
                refine ⟨149107123825012616002854835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198809498433350154670473113 149107123825012616002854835)
                ·
                  refine ⟨223660685737518924004282253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149107123825012616002854835 223660685737518924004282253)
                  ·
                    refine ⟨83872757151569596501605845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 223660685737518924004282253 83872757151569596501605845)
                    ·
                      refine ⟨1965767745739912418006387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83872757151569596501605845 1965767745739912418006387)
                      ·
                        rfl

theorem cell23_3828319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_3828319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828319 prefixEnd_3828319 := by exact prefixLift 3828319
  have htrace : WordTrace (prefixWord ++ tailWord_3828319) baseStart_3828319 baseEnd_3828319 := by
    simpa [prefixWord, tailWord_3828319, baseEnd_3828319] using wordTrace_append hprefix tailTrace_3828319
  have hstable : (prefixWord ++ tailWord_3828319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828319).length < 2 ^ (prefixWord ++ tailWord_3828319).sum := by decide
  have hdescent : baseEnd_3828319 < baseStart_3828319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828334 : List Nat := [4, 1, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_3828334 : Nat := 118140960795 + 3828334 * 2 ^ 59
def prefixEnd_3828334 : Nat := 4983230072969 + 3 ^ 40 * 3828334 * 2
def baseEnd_3828334 : Nat := 655258482649909953106273

theorem tailTrace_3828334 : CollatzResearch.WordTrace tailWord_3828334 prefixEnd_3828334 655258482649909953106273 := by
  unfold tailWord_3828334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17453851514075902529806507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93087208075071480158968037 17453851514075902529806507)
  ·
    refine ⟨26180777271113853794709761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17453851514075902529806507 26180777271113853794709761)
    ·
      refine ⟨19635582953335390346032321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26180777271113853794709761 19635582953335390346032321)
      ·
        refine ⟨14726687215001542759524241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19635582953335390346032321 14726687215001542759524241)
        ·
          refine ⟨11045015411251157069643181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14726687215001542759524241 11045015411251157069643181)
          ·
            refine ⟨4141880779219183901116193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11045015411251157069643181 4141880779219183901116193)
            ·
              refine ⟨3106410584414387925837145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4141880779219183901116193 3106410584414387925837145)
              ·
                refine ⟨2329807938310790944377859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106410584414387925837145 2329807938310790944377859)
                ·
                  refine ⟨3494711907466186416566789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329807938310790944377859 3494711907466186416566789)
                  ·
                    refine ⟨655258482649909953106273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3494711907466186416566789 655258482649909953106273)
                    ·
                      rfl

theorem cell23_3828334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_3828334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828334 prefixEnd_3828334 := by exact prefixLift 3828334
  have htrace : WordTrace (prefixWord ++ tailWord_3828334) baseStart_3828334 baseEnd_3828334 := by
    simpa [prefixWord, tailWord_3828334, baseEnd_3828334] using wordTrace_append hprefix tailTrace_3828334
  have hstable : (prefixWord ++ tailWord_3828334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828334).length < 2 ^ (prefixWord ++ tailWord_3828334).sum := by decide
  have hdescent : baseEnd_3828334 < baseStart_3828334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828380 : List Nat := [2, 2, 3, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_3828380 : Nat := 118140960795 + 3828380 * 2 ^ 59
def prefixEnd_3828380 : Nat := 4983230072969 + 3 ^ 40 * 3828380 * 2
def baseEnd_3828380 : Nat := 1965799068059836679343607

theorem tailTrace_3828380 : CollatzResearch.WordTrace tailWord_3828380 prefixEnd_3828380 1965799068059836679343607 := by
  unfold tailWord_3828380
  simp only [CollatzResearch.WordTrace]
  refine ⟨69816244935220285047313297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93088326580293713396417729 69816244935220285047313297)
  ·
    refine ⟨52362183701415213785484973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69816244935220285047313297 52362183701415213785484973)
    ·
      refine ⟨19635818888030705169556865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52362183701415213785484973 19635818888030705169556865)
      ·
        refine ⟨14726864166023028877167649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19635818888030705169556865 14726864166023028877167649)
        ·
          refine ⟨11045148124517271657875737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14726864166023028877167649 11045148124517271657875737)
          ·
            refine ⟨8283861093387953743406803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11045148124517271657875737 8283861093387953743406803)
            ·
              refine ⟨12425791640081930615110205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8283861093387953743406803 12425791640081930615110205)
              ·
                refine ⟨4659671865030723980666327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12425791640081930615110205 4659671865030723980666327)
                ·
                  refine ⟨6989507797546085970999491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4659671865030723980666327 6989507797546085970999491)
                  ·
                    refine ⟨10484261696319128956499237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6989507797546085970999491 10484261696319128956499237)
                    ·
                      refine ⟨1965799068059836679343607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10484261696319128956499237 1965799068059836679343607)
                      ·
                        rfl

theorem cell23_3828380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_3828380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828380 prefixEnd_3828380 := by exact prefixLift 3828380
  have htrace : WordTrace (prefixWord ++ tailWord_3828380) baseStart_3828380 baseEnd_3828380 := by
    simpa [prefixWord, tailWord_3828380, baseEnd_3828380] using wordTrace_append hprefix tailTrace_3828380
  have hstable : (prefixWord ++ tailWord_3828380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828380).length < 2 ^ (prefixWord ++ tailWord_3828380).sum := by decide
  have hdescent : baseEnd_3828380 < baseStart_3828380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828396 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 3]
def baseStart_3828396 : Nat := 118140960795 + 3828396 * 2 ^ 59
def prefixEnd_3828396 : Nat := 4983230072969 + 3 ^ 40 * 3828396 * 2
def baseEnd_3828396 : Nat := 1965807283750308616743533

theorem tailTrace_3828396 : CollatzResearch.WordTrace tailWord_3828396 prefixEnd_3828396 1965807283750308616743533 := by
  unfold tailWord_3828396
  simp only [CollatzResearch.WordTrace]
  refine ⟨69816536719191302413604521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93088715625588403218139361 69816536719191302413604521)
  ·
    refine ⟨52362402539393476810203391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69816536719191302413604521 52362402539393476810203391)
    ·
      refine ⟨78543603809090215215305087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52362402539393476810203391 78543603809090215215305087)
      ·
        refine ⟨117815405713635322822957631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78543603809090215215305087 117815405713635322822957631)
        ·
          refine ⟨176723108570452984234436447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117815405713635322822957631 176723108570452984234436447)
          ·
            refine ⟨265084662855679476351654671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176723108570452984234436447 265084662855679476351654671)
            ·
              refine ⟨397626994283519214527482007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265084662855679476351654671 397626994283519214527482007)
              ·
                refine ⟨596440491425278821791223011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397626994283519214527482007 596440491425278821791223011)
                ·
                  refine ⟨894660737137918232686834517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596440491425278821791223011 894660737137918232686834517)
                  ·
                    refine ⟨5242152756667489644649421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 894660737137918232686834517 5242152756667489644649421)
                    ·
                      refine ⟨1965807283750308616743533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5242152756667489644649421 1965807283750308616743533)
                      ·
                        rfl

theorem cell23_3828396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_3828396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828396 prefixEnd_3828396 := by exact prefixLift 3828396
  have htrace : WordTrace (prefixWord ++ tailWord_3828396) baseStart_3828396 baseEnd_3828396 := by
    simpa [prefixWord, tailWord_3828396, baseEnd_3828396] using wordTrace_append hprefix tailTrace_3828396
  have hstable : (prefixWord ++ tailWord_3828396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828396).length < 2 ^ (prefixWord ++ tailWord_3828396).sum := by decide
  have hdescent : baseEnd_3828396 < baseStart_3828396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828397 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_3828397 : Nat := 118140960795 + 3828397 * 2 ^ 59
def prefixEnd_3828397 : Nat := 4983230072969 + 3 ^ 40 * 3828397 * 2
def baseEnd_3828397 : Nat := 1965807797230963112831029

theorem tailTrace_3828397 : CollatzResearch.WordTrace tailWord_3828397 prefixEnd_3828397 1965807797230963112831029 := by
  unfold tailWord_3828397
  simp only [CollatzResearch.WordTrace]
  refine ⟨139633109911378981997995445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93088739940919321331996963 139633109911378981997995445)
  ·
    refine ⟨13090604054191779562312073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139633109911378981997995445 13090604054191779562312073)
    ·
      refine ⟨9817953040643834671734055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13090604054191779562312073 9817953040643834671734055)
      ·
        refine ⟨14726929560965752007601083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9817953040643834671734055 14726929560965752007601083)
        ·
          refine ⟨22090394341448628011401625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14726929560965752007601083 22090394341448628011401625)
          ·
            refine ⟨16567795756086471008551219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22090394341448628011401625 16567795756086471008551219)
            ·
              refine ⟨24851693634129706512826829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16567795756086471008551219 24851693634129706512826829)
              ·
                refine ⟨9319385112798639942310061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24851693634129706512826829 9319385112798639942310061)
                ·
                  refine ⟨3494769417299489978366273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9319385112798639942310061 3494769417299489978366273)
                  ·
                    refine ⟨2621077062974617483774705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3494769417299489978366273 2621077062974617483774705)
                    ·
                      refine ⟨1965807797230963112831029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621077062974617483774705 1965807797230963112831029)
                      ·
                        rfl

theorem cell23_3828397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_3828397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828397 prefixEnd_3828397 := by exact prefixLift 3828397
  have htrace : WordTrace (prefixWord ++ tailWord_3828397) baseStart_3828397 baseEnd_3828397 := by
    simpa [prefixWord, tailWord_3828397, baseEnd_3828397] using wordTrace_append hprefix tailTrace_3828397
  have hstable : (prefixWord ++ tailWord_3828397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828397).length < 2 ^ (prefixWord ++ tailWord_3828397).sum := by decide
  have hdescent : baseEnd_3828397 < baseStart_3828397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828407 : List Nat := [1, 1, 3, 1, 6, 1, 3, 1, 2, 4]
def baseStart_3828407 : Nat := 118140960795 + 3828407 * 2 ^ 59
def prefixEnd_3828407 : Nat := 4983230072969 + 3 ^ 40 * 3828407 * 2
def baseEnd_3828407 : Nat := 655270977345836024568661

theorem tailTrace_3828407 : CollatzResearch.WordTrace tailWord_3828407 prefixEnd_3828407 655270977345836024568661 := by
  unfold tailWord_3828407
  simp only [CollatzResearch.WordTrace]
  refine ⟨139633474641342753705859475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93088983094228502470572983 139633474641342753705859475)
  ·
    refine ⟨209450211962014130558789213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139633474641342753705859475 209450211962014130558789213)
    ·
      refine ⟨78543829485755298959545955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209450211962014130558789213 78543829485755298959545955)
      ·
        refine ⟨117815744228632948439318933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78543829485755298959545955 117815744228632948439318933)
        ·
          refine ⟨5522613010717169458093075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117815744228632948439318933 5522613010717169458093075)
          ·
            refine ⟨8283919516075754187139613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522613010717169458093075 8283919516075754187139613)
            ·
              refine ⟨3106469818528407820177355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8283919516075754187139613 3106469818528407820177355)
              ·
                refine ⟨4659704727792611730266033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106469818528407820177355 4659704727792611730266033)
                ·
                  refine ⟨3494778545844458797699525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4659704727792611730266033 3494778545844458797699525)
                  ·
                    refine ⟨655270977345836024568661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3494778545844458797699525 655270977345836024568661)
                    ·
                      rfl

theorem cell23_3828407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_3828407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828407 prefixEnd_3828407 := by exact prefixLift 3828407
  have htrace : WordTrace (prefixWord ++ tailWord_3828407) baseStart_3828407 baseEnd_3828407 := by
    simpa [prefixWord, tailWord_3828407, baseEnd_3828407] using wordTrace_append hprefix tailTrace_3828407
  have hstable : (prefixWord ++ tailWord_3828407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828407).length < 2 ^ (prefixWord ++ tailWord_3828407).sum := by decide
  have hdescent : baseEnd_3828407 < baseStart_3828407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828420 : List Nat := [2, 3, 3, 1, 1, 4, 2, 7]
def baseStart_3828420 : Nat := 118140960795 + 3828420 * 2 ^ 59
def prefixEnd_3828420 : Nat := 4983230072969 + 3 ^ 40 * 3828420 * 2
def baseEnd_3828420 : Nat := 72808133603185797142349

theorem tailTrace_3828420 : CollatzResearch.WordTrace tailWord_3828420 prefixEnd_3828420 72808133603185797142349 := by
  unfold tailWord_3828420
  simp only [CollatzResearch.WordTrace]
  refine ⟨69816974395147828463041357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93089299193530437950721809 69816974395147828463041357)
  ·
    refine ⟨26181365398180435673640509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69816974395147828463041357 26181365398180435673640509)
    ·
      refine ⟨9818012024317663377615191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26181365398180435673640509 9818012024317663377615191)
      ·
        refine ⟨14727018036476495066422787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9818012024317663377615191 14727018036476495066422787)
        ·
          refine ⟨22090527054714742599634181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14727018036476495066422787 22090527054714742599634181)
          ·
            refine ⟨4141973822759014237431409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22090527054714742599634181 4141973822759014237431409)
            ·
              refine ⟨3106480367069260678073557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4141973822759014237431409 3106480367069260678073557)
              ·
                refine ⟨72808133603185797142349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3106480367069260678073557 72808133603185797142349)
                ·
                  rfl

theorem cell23_3828420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 7].length) (baseStart_3828420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828420 prefixEnd_3828420 := by exact prefixLift 3828420
  have htrace : WordTrace (prefixWord ++ tailWord_3828420) baseStart_3828420 baseEnd_3828420 := by
    simpa [prefixWord, tailWord_3828420, baseEnd_3828420] using wordTrace_append hprefix tailTrace_3828420
  have hstable : (prefixWord ++ tailWord_3828420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828420).length < 2 ^ (prefixWord ++ tailWord_3828420).sum := by decide
  have hdescent : baseEnd_3828420 < baseStart_3828420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828430 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_3828430 : Nat := 118140960795 + 3828430 * 2 ^ 59
def prefixEnd_3828430 : Nat := 4983230072969 + 3 ^ 40 * 3828430 * 2
def baseEnd_3828430 : Nat := 1965824742092561483718377

theorem tailTrace_3828430 : CollatzResearch.WordTrace tailWord_3828430 prefixEnd_3828430 1965824742092561483718377 := by
  unfold tailWord_3828430
  simp only [CollatzResearch.WordTrace]
  refine ⟨17454289190032428579243343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93089542346839619089297829 17454289190032428579243343)
  ·
    refine ⟨26181433785048642868865015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17454289190032428579243343 26181433785048642868865015)
    ·
      refine ⟨39272150677572964303297523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26181433785048642868865015 39272150677572964303297523)
      ·
        refine ⟨58908226016359446454946285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39272150677572964303297523 58908226016359446454946285)
        ·
          refine ⟨22090584756134792420604857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58908226016359446454946285 22090584756134792420604857)
          ·
            refine ⟨16567938567101094315453643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22090584756134792420604857 16567938567101094315453643)
            ·
              refine ⟨24851907850651641473180465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16567938567101094315453643 24851907850651641473180465)
              ·
                refine ⟨18638930887988731104885349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24851907850651641473180465 18638930887988731104885349)
                ·
                  refine ⟨3494799541497887082166003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18638930887988731104885349 3494799541497887082166003)
                  ·
                    refine ⟨5242199312246830623249005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3494799541497887082166003 5242199312246830623249005)
                    ·
                      refine ⟨1965824742092561483718377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5242199312246830623249005 1965824742092561483718377)
                      ·
                        rfl

theorem cell23_3828430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_3828430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828430 prefixEnd_3828430 := by exact prefixLift 3828430
  have htrace : WordTrace (prefixWord ++ tailWord_3828430) baseStart_3828430 baseEnd_3828430 := by
    simpa [prefixWord, tailWord_3828430, baseEnd_3828430] using wordTrace_append hprefix tailTrace_3828430
  have hstable : (prefixWord ++ tailWord_3828430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828430).length < 2 ^ (prefixWord ++ tailWord_3828430).sum := by decide
  have hdescent : baseEnd_3828430 < baseStart_3828430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828468 : List Nat := [2, 6, 1, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_3828468 : Nat := 118140960795 + 3828468 * 2 ^ 59
def prefixEnd_3828468 : Nat := 4983230072969 + 3 ^ 40 * 3828468 * 2
def baseEnd_3828468 : Nat := 1965844254357432335043203

theorem tailTrace_3828468 : CollatzResearch.WordTrace tailWord_3828468 prefixEnd_3828468 1965844254357432335043203 := by
  unfold tailWord_3828468
  simp only [CollatzResearch.WordTrace]
  refine ⟨69817849747060880561915029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93090466329414507415886705 69817849747060880561915029)
  ·
    refine ⟨3272711706893478776339767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69817849747060880561915029 3272711706893478776339767)
    ·
      refine ⟨4909067560340218164509651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3272711706893478776339767 4909067560340218164509651)
      ·
        refine ⟨7363601340510327246764477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4909067560340218164509651 7363601340510327246764477)
        ·
          refine ⟨2761350502691372717536679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7363601340510327246764477 2761350502691372717536679)
          ·
            refine ⟨4142025754037059076305019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761350502691372717536679 4142025754037059076305019)
            ·
              refine ⟨6213038631055588614457529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4142025754037059076305019 6213038631055588614457529)
              ·
                refine ⟨4659778973291691460843147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6213038631055588614457529 4659778973291691460843147)
                ·
                  refine ⟨6989668459937537191264721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4659778973291691460843147 6989668459937537191264721)
                  ·
                    refine ⟨5242251344953152893448541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6989668459937537191264721 5242251344953152893448541)
                    ·
                      refine ⟨1965844254357432335043203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5242251344953152893448541 1965844254357432335043203)
                      ·
                        rfl

theorem cell23_3828468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_3828468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828468 prefixEnd_3828468 := by exact prefixLift 3828468
  have htrace : WordTrace (prefixWord ++ tailWord_3828468) baseStart_3828468 baseEnd_3828468 := by
    simpa [prefixWord, tailWord_3828468, baseEnd_3828468] using wordTrace_append hprefix tailTrace_3828468
  have hstable : (prefixWord ++ tailWord_3828468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828468).length < 2 ^ (prefixWord ++ tailWord_3828468).sum := by decide
  have hdescent : baseEnd_3828468 < baseStart_3828468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828487 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3828487 : Nat := 118140960795 + 3828487 * 2 ^ 59
def prefixEnd_3828487 : Nat := 4983230072969 + 3 ^ 40 * 3828487 * 2
def baseEnd_3828487 : Nat := 1965854010489867760705615

theorem tailTrace_3828487 : CollatzResearch.WordTrace tailWord_3828487 prefixEnd_3828487 1965854010489867760705615 := by
  unfold tailWord_3828487
  simp only [CollatzResearch.WordTrace]
  refine ⟨139636392481052927368771715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93090928320701951579181143 139636392481052927368771715)
  ·
    refine ⟨209454588721579391053157573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139636392481052927368771715 209454588721579391053157573)
    ·
      refine ⟨39272735385296135822467045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209454588721579391053157573 39272735385296135822467045)
      ·
        refine ⟨7363637884743025466712571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39272735385296135822467045 7363637884743025466712571)
        ·
          refine ⟨11045456827114538200068857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7363637884743025466712571 11045456827114538200068857)
          ·
            refine ⟨8284092620335903650051643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11045456827114538200068857 8284092620335903650051643)
            ·
              refine ⟨12426138930503855475077465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284092620335903650051643 12426138930503855475077465)
              ·
                refine ⟨9319604197877891606308099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12426138930503855475077465 9319604197877891606308099)
                ·
                  refine ⟨13979406296816837409462149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9319604197877891606308099 13979406296816837409462149)
                  ·
                    refine ⟨2621138680653157014274153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13979406296816837409462149 2621138680653157014274153)
                    ·
                      refine ⟨1965854010489867760705615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621138680653157014274153 1965854010489867760705615)
                      ·
                        rfl

theorem cell23_3828487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3828487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828487 prefixEnd_3828487 := by exact prefixLift 3828487
  have htrace : WordTrace (prefixWord ++ tailWord_3828487) baseStart_3828487 baseEnd_3828487 := by
    simpa [prefixWord, tailWord_3828487, baseEnd_3828487] using wordTrace_append hprefix tailTrace_3828487
  have hstable : (prefixWord ++ tailWord_3828487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828487).length < 2 ^ (prefixWord ++ tailWord_3828487).sum := by decide
  have hdescent : baseEnd_3828487 < baseStart_3828487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828520 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3828520 : Nat := 118140960795 + 3828520 * 2 ^ 59
def prefixEnd_3828520 : Nat := 4983230072969 + 3 ^ 40 * 3828520 * 2
def baseEnd_3828520 : Nat := 1965870955351466131592963

theorem tailTrace_3828520 : CollatzResearch.WordTrace tailWord_3828520 prefixEnd_3828520 1965870955351466131592963 := by
  unfold tailWord_3828520
  simp only [CollatzResearch.WordTrace]
  refine ⟨69818798044966687002361507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93091730726622249336482009 69818798044966687002361507)
  ·
    refine ⟨104728197067450030503542261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69818798044966687002361507 104728197067450030503542261)
    ·
      refine ⟨9818268475073440359707087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104728197067450030503542261 9818268475073440359707087)
      ·
        refine ⟨14727402712610160539560631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9818268475073440359707087 14727402712610160539560631)
        ·
          refine ⟨22091104068915240809340947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14727402712610160539560631 22091104068915240809340947)
          ·
            refine ⟨33136656103372861214011421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22091104068915240809340947 33136656103372861214011421)
            ·
              refine ⟨12426246038764822955254283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33136656103372861214011421 12426246038764822955254283)
              ·
                refine ⟨18639369058147234432881425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12426246038764822955254283 18639369058147234432881425)
                ·
                  refine ⟨13979526793610425824661069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18639369058147234432881425 13979526793610425824661069)
                  ·
                    refine ⟨5242322547603909684247901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13979526793610425824661069 5242322547603909684247901)
                    ·
                      refine ⟨1965870955351466131592963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5242322547603909684247901 1965870955351466131592963)
                      ·
                        rfl

theorem cell23_3828520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3828520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828520 prefixEnd_3828520 := by exact prefixLift 3828520
  have htrace : WordTrace (prefixWord ++ tailWord_3828520) baseStart_3828520 baseEnd_3828520 := by
    simpa [prefixWord, tailWord_3828520, baseEnd_3828520] using wordTrace_append hprefix tailTrace_3828520
  have hstable : (prefixWord ++ tailWord_3828520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828520).length < 2 ^ (prefixWord ++ tailWord_3828520).sum := by decide
  have hdescent : baseEnd_3828520 < baseStart_3828520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828530 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2]
def baseStart_3828530 : Nat := 118140960795 + 3828530 * 2 ^ 59
def prefixEnd_3828530 : Nat := 4983230072969 + 3 ^ 40 * 3828530 * 2
def baseEnd_3828530 : Nat := 1965876090158011092467917

theorem tailTrace_3828530 : CollatzResearch.WordTrace tailWord_3828530 prefixEnd_3828530 1965876090158011092467917 := by
  unfold tailWord_3828530
  simp only [CollatzResearch.WordTrace]
  refine ⟨34909490204974286428146761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93091973879931430475058029 34909490204974286428146761)
  ·
    refine ⟨26182117653730714821110071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34909490204974286428146761 26182117653730714821110071)
    ·
      refine ⟨39273176480596072231665107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26182117653730714821110071 39273176480596072231665107)
      ·
        refine ⟨58909764720894108347497661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39273176480596072231665107 58909764720894108347497661)
        ·
          refine ⟨22091161770335290630311623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58909764720894108347497661 22091161770335290630311623)
          ·
            refine ⟨33136742655502935945467435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22091161770335290630311623 33136742655502935945467435)
            ·
              refine ⟨49705113983254403918201153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33136742655502935945467435 49705113983254403918201153)
              ·
                refine ⟨37278835487440802938650865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49705113983254403918201153 37278835487440802938650865)
                ·
                  refine ⟨27959126615580602203988149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37278835487440802938650865 27959126615580602203988149)
                  ·
                    refine ⟨2621168120210681456623889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27959126615580602203988149 2621168120210681456623889)
                    ·
                      refine ⟨1965876090158011092467917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621168120210681456623889 1965876090158011092467917)
                      ·
                        rfl

theorem cell23_3828530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_3828530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828530 prefixEnd_3828530 := by exact prefixLift 3828530
  have htrace : WordTrace (prefixWord ++ tailWord_3828530) baseStart_3828530 baseEnd_3828530 := by
    simpa [prefixWord, tailWord_3828530, baseEnd_3828530] using wordTrace_append hprefix tailTrace_3828530
  have hstable : (prefixWord ++ tailWord_3828530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828530).length < 2 ^ (prefixWord ++ tailWord_3828530).sum := by decide
  have hdescent : baseEnd_3828530 < baseStart_3828530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828560 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 2, 4, 2]
def baseStart_3828560 : Nat := 118140960795 + 3828560 * 2 ^ 59
def prefixEnd_3828560 : Nat := 4983230072969 + 3 ^ 40 * 3828560 * 2
def baseEnd_3828560 : Nat := 1965891494577645975092779

theorem tailTrace_3828560 : CollatzResearch.WordTrace tailWord_3828560 prefixEnd_3828560 1965891494577645975092779 := by
  unfold tailWord_3828560
  simp only [CollatzResearch.WordTrace]
  refine ⟨69819527504894230418089567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93092703339858973890786089 69819527504894230418089567)
  ·
    refine ⟨104729291257341345627134351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69819527504894230418089567 104729291257341345627134351)
    ·
      refine ⟨157093936886012018440701527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104729291257341345627134351 157093936886012018440701527)
      ·
        refine ⟨235640905329018027661052291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157093936886012018440701527 235640905329018027661052291)
        ·
          refine ⟨353461357993527041491578437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235640905329018027661052291 353461357993527041491578437)
          ·
            refine ⟨66274004623786320279670957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353461357993527041491578437 66274004623786320279670957)
            ·
              refine ⟨24852751733919870104876609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66274004623786320279670957 24852751733919870104876609)
              ·
                refine ⟨18639563800439902578657457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24852751733919870104876609 18639563800439902578657457)
                ·
                  refine ⟨13979672850329926933993093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18639563800439902578657457 13979672850329926933993093)
                  ·
                    refine ⟨2621188659436861300123705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13979672850329926933993093 2621188659436861300123705)
                    ·
                      refine ⟨1965891494577645975092779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621188659436861300123705 1965891494577645975092779)
                      ·
                        rfl

theorem cell23_3828560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 4, 2].length) (baseStart_3828560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828560 prefixEnd_3828560 := by exact prefixLift 3828560
  have htrace : WordTrace (prefixWord ++ tailWord_3828560) baseStart_3828560 baseEnd_3828560 := by
    simpa [prefixWord, tailWord_3828560, baseEnd_3828560] using wordTrace_append hprefix tailTrace_3828560
  have hstable : (prefixWord ++ tailWord_3828560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828560).length < 2 ^ (prefixWord ++ tailWord_3828560).sum := by decide
  have hdescent : baseEnd_3828560 < baseStart_3828560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828570 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 3, 4]
def baseStart_3828570 : Nat := 118140960795 + 3828570 * 2 ^ 59
def prefixEnd_3828570 : Nat := 4983230072969 + 3 ^ 40 * 3828570 * 2
def baseEnd_3828570 : Nat := 655298876461396978655911

theorem tailTrace_3828570 : CollatzResearch.WordTrace tailWord_3828570 prefixEnd_3828570 655298876461396978655911 := by
  unfold tailWord_3828570
  simp only [CollatzResearch.WordTrace]
  refine ⟨34909854934938058136010791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93092946493168155029362109 34909854934938058136010791)
  ·
    refine ⟨52364782402407087204016187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34909854934938058136010791 52364782402407087204016187)
    ·
      refine ⟨78547173603610630806024281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52364782402407087204016187 78547173603610630806024281)
      ·
        refine ⟨58910380202707973104518211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78547173603610630806024281 58910380202707973104518211)
        ·
          refine ⟨88365570304061959656777317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58910380202707973104518211 88365570304061959656777317)
          ·
            refine ⟨16568544432011617435645747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88365570304061959656777317 16568544432011617435645747)
            ·
              refine ⟨24852816648017426153468621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16568544432011617435645747 24852816648017426153468621)
              ·
                refine ⟨9319806243006534807550733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24852816648017426153468621 9319806243006534807550733)
                ·
                  refine ⟨3494927341127450552831525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9319806243006534807550733 3494927341127450552831525)
                  ·
                    refine ⟨655298876461396978655911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3494927341127450552831525 655298876461396978655911)
                    ·
                      rfl

theorem cell23_3828570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_3828570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828570 prefixEnd_3828570 := by exact prefixLift 3828570
  have htrace : WordTrace (prefixWord ++ tailWord_3828570) baseStart_3828570 baseEnd_3828570 := by
    simpa [prefixWord, tailWord_3828570, baseEnd_3828570] using wordTrace_append hprefix tailTrace_3828570
  have hstable : (prefixWord ++ tailWord_3828570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828570).length < 2 ^ (prefixWord ++ tailWord_3828570).sum := by decide
  have hdescent : baseEnd_3828570 < baseStart_3828570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828580 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_3828580 : Nat := 118140960795 + 3828580 * 2 ^ 59
def prefixEnd_3828580 : Nat := 4983230072969 + 3 ^ 40 * 3828580 * 2
def baseEnd_3828580 : Nat := 1965901764190735896842687

theorem tailTrace_3828580 : CollatzResearch.WordTrace tailWord_3828580 prefixEnd_3828580 1965901764190735896842687 := by
  unfold tailWord_3828580
  simp only [CollatzResearch.WordTrace]
  refine ⟨69819892234858002125953597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93093189646477336167938129 69819892234858002125953597)
  ·
    refine ⟨26182459588071750797232599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69819892234858002125953597 26182459588071750797232599)
    ·
      refine ⟨39273689382107626195848899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26182459588071750797232599 39273689382107626195848899)
      ·
        refine ⟨58910534073161439293773349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39273689382107626195848899 58910534073161439293773349)
        ·
          refine ⟨11045725138717769867582503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58910534073161439293773349 11045725138717769867582503)
          ·
            refine ⟨16568587708076654801373755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11045725138717769867582503 16568587708076654801373755)
            ·
              refine ⟨24852881562114982202060633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16568587708076654801373755 24852881562114982202060633)
              ·
                refine ⟨18639661171586236651545475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24852881562114982202060633 18639661171586236651545475)
                ·
                  refine ⟨27959491757379354977318213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18639661171586236651545475 27959491757379354977318213)
                  ·
                    refine ⟨5242404704508629058247165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27959491757379354977318213 5242404704508629058247165)
                    ·
                      refine ⟨1965901764190735896842687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5242404704508629058247165 1965901764190735896842687)
                      ·
                        rfl

theorem cell23_3828580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_3828580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828580 prefixEnd_3828580 := by exact prefixLift 3828580
  have htrace : WordTrace (prefixWord ++ tailWord_3828580) baseStart_3828580 baseEnd_3828580 := by
    simpa [prefixWord, tailWord_3828580, baseEnd_3828580] using wordTrace_append hprefix tailTrace_3828580
  have hstable : (prefixWord ++ tailWord_3828580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828580).length < 2 ^ (prefixWord ++ tailWord_3828580).sum := by decide
  have hdescent : baseEnd_3828580 < baseStart_3828580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828633 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 2, 5, 4]
def baseStart_3828633 : Nat := 118140960795 + 3828633 * 2 ^ 59
def prefixEnd_3828633 : Nat := 4983230072969 + 3 ^ 40 * 3828633 * 2
def baseEnd_3828633 : Nat := 1965928978665424189479943

theorem tailTrace_3828633 : CollatzResearch.WordTrace tailWord_3828633 prefixEnd_3828633 1965928978665424189479943 := by
  unfold tailWord_3828633
  simp only [CollatzResearch.WordTrace]
  refine ⟨139641717538523994303586553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93094478359015996202391035 139641717538523994303586553)
  ·
    refine ⟨104731288153892995727689915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139641717538523994303586553 104731288153892995727689915)
    ·
      refine ⟨157096932230839493591534873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104731288153892995727689915 157096932230839493591534873)
      ·
        refine ⟨117822699173129620193651155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157096932230839493591534873 117822699173129620193651155)
        ·
          refine ⟨176734048759694430290476733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117822699173129620193651155 176734048759694430290476733)
          ·
            refine ⟨66275268284885411358928775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176734048759694430290476733 66275268284885411358928775)
            ·
              refine ⟨99412902427328117038393163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66275268284885411358928775 99412902427328117038393163)
              ·
                refine ⟨149119353640992175557589745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99412902427328117038393163 149119353640992175557589745)
                ·
                  refine ⟨111839515230744131668192309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149119353640992175557589745 111839515230744131668192309)
                  ·
                    refine ⟨10484954552882262343893029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111839515230744131668192309 10484954552882262343893029)
                    ·
                      refine ⟨1965928978665424189479943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10484954552882262343893029 1965928978665424189479943)
                      ·
                        rfl

theorem cell23_3828633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_3828633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828633 prefixEnd_3828633 := by exact prefixLift 3828633
  have htrace : WordTrace (prefixWord ++ tailWord_3828633) baseStart_3828633 baseEnd_3828633 := by
    simpa [prefixWord, tailWord_3828633, baseEnd_3828633] using wordTrace_append hprefix tailTrace_3828633
  have hstable : (prefixWord ++ tailWord_3828633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828633).length < 2 ^ (prefixWord ++ tailWord_3828633).sum := by decide
  have hdescent : baseEnd_3828633 < baseStart_3828633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828634 : List Nat := [3, 1, 1, 4, 3, 2, 2, 1, 6]
def baseStart_3828634 : Nat := 118140960795 + 3828634 * 2 ^ 59
def prefixEnd_3828634 : Nat := 4983230072969 + 3 ^ 40 * 3828634 * 2
def baseEnd_3828634 : Nat := 218436610238453187285271

theorem tailTrace_3828634 : CollatzResearch.WordTrace tailWord_3828634 prefixEnd_3828634 218436610238453187285271 := by
  unfold tailWord_3828634
  simp only [CollatzResearch.WordTrace]
  refine ⟨34910438502880092868593239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93094502674346914316248637 34910438502880092868593239)
  ·
    refine ⟨52365657754320139302889859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34910438502880092868593239 52365657754320139302889859)
    ·
      refine ⟨78548486631480208954334789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52365657754320139302889859 78548486631480208954334789)
      ·
        refine ⟨14727841243402539178937773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78548486631480208954334789 14727841243402539178937773)
        ·
          refine ⟨5522940466275952192101665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14727841243402539178937773 5522940466275952192101665)
          ·
            refine ⟨4142205349706964144076249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5522940466275952192101665 4142205349706964144076249)
            ·
              refine ⟨3106654012280223108057187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142205349706964144076249 3106654012280223108057187)
              ·
                refine ⟨4659981018420334662085781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106654012280223108057187 4659981018420334662085781)
                ·
                  refine ⟨218436610238453187285271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4659981018420334662085781 218436610238453187285271)
                  ·
                    rfl

theorem cell23_3828634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_3828634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828634 prefixEnd_3828634 := by exact prefixLift 3828634
  have htrace : WordTrace (prefixWord ++ tailWord_3828634) baseStart_3828634 baseEnd_3828634 := by
    simpa [prefixWord, tailWord_3828634, baseEnd_3828634] using wordTrace_append hprefix tailTrace_3828634
  have hstable : (prefixWord ++ tailWord_3828634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828634).length < 2 ^ (prefixWord ++ tailWord_3828634).sum := by decide
  have hdescent : baseEnd_3828634 < baseStart_3828634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828637 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_3828637 : Nat := 118140960795 + 3828637 * 2 ^ 59
def prefixEnd_3828637 : Nat := 4983230072969 + 3 ^ 40 * 3828637 * 2
def baseEnd_3828637 : Nat := 1965931032588042173829925

theorem tailTrace_3828637 : CollatzResearch.WordTrace tailWord_3828637 prefixEnd_3828637 1965931032588042173829925 := by
  unfold tailWord_3828637
  simp only [CollatzResearch.WordTrace]
  refine ⟨139641863430509502986732165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93094575620339668657821443 139641863430509502986732165)
  ·
    refine ⟨26182849393220531810012281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139641863430509502986732165 26182849393220531810012281)
    ·
      refine ⟨19637137044915398857509211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26182849393220531810012281 19637137044915398857509211)
      ·
        refine ⟨29455705567373098286263817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19637137044915398857509211 29455705567373098286263817)
        ·
          refine ⟨22091779175529823714697863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29455705567373098286263817 22091779175529823714697863)
          ·
            refine ⟨33137668763294735572046795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22091779175529823714697863 33137668763294735572046795)
            ·
              refine ⟨49706503144942103358070193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33137668763294735572046795 49706503144942103358070193)
              ·
                refine ⟨37279877358706577518552645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49706503144942103358070193 37279877358706577518552645)
                ·
                  refine ⟨6989977004757483284728621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37279877358706577518552645 6989977004757483284728621)
                  ·
                    refine ⟨2621241376784056231773233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6989977004757483284728621 2621241376784056231773233)
                    ·
                      refine ⟨1965931032588042173829925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621241376784056231773233 1965931032588042173829925)
                      ·
                        rfl

theorem cell23_3828637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_3828637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828637 prefixEnd_3828637 := by exact prefixLift 3828637
  have htrace : WordTrace (prefixWord ++ tailWord_3828637) baseStart_3828637 baseEnd_3828637 := by
    simpa [prefixWord, tailWord_3828637, baseEnd_3828637] using wordTrace_append hprefix tailTrace_3828637
  have hstable : (prefixWord ++ tailWord_3828637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828637).length < 2 ^ (prefixWord ++ tailWord_3828637).sum := by decide
  have hdescent : baseEnd_3828637 < baseStart_3828637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828647 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 3, 5]
def baseStart_3828647 : Nat := 118140960795 + 3828647 * 2 ^ 59
def prefixEnd_3828647 : Nat := 4983230072969 + 3 ^ 40 * 3828647 * 2
def baseEnd_3828647 : Nat := 655312055798195711568293

theorem tailTrace_3828647 : CollatzResearch.WordTrace tailWord_3828647 prefixEnd_3828647 655312055798195711568293 := by
  unfold tailWord_3828647
  simp only [CollatzResearch.WordTrace]
  refine ⟨139642228160473274694596195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93094818773648849796397463 139642228160473274694596195)
  ·
    refine ⟨209463342240709912041894293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139642228160473274694596195 209463342240709912041894293)
    ·
      refine ⟨9818594167533277126963795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209463342240709912041894293 9818594167533277126963795)
      ·
        refine ⟨14727891251299915690445693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9818594167533277126963795 14727891251299915690445693)
        ·
          refine ⟨5522959219237468383917135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14727891251299915690445693 5522959219237468383917135)
          ·
            refine ⟨8284438828856202575875703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522959219237468383917135 8284438828856202575875703)
            ·
              refine ⟨12426658243284303863813555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284438828856202575875703 12426658243284303863813555)
              ·
                refine ⟨18639987364926455795720333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12426658243284303863813555 18639987364926455795720333)
                ·
                  refine ⟨6989995261847420923395125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18639987364926455795720333 6989995261847420923395125)
                  ·
                    refine ⟨655312055798195711568293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6989995261847420923395125 655312055798195711568293)
                    ·
                      rfl

theorem cell23_3828647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_3828647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828647 prefixEnd_3828647 := by exact prefixLift 3828647
  have htrace : WordTrace (prefixWord ++ tailWord_3828647) baseStart_3828647 baseEnd_3828647 := by
    simpa [prefixWord, tailWord_3828647, baseEnd_3828647] using wordTrace_append hprefix tailTrace_3828647
  have hstable : (prefixWord ++ tailWord_3828647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828647).length < 2 ^ (prefixWord ++ tailWord_3828647).sum := by decide
  have hdescent : baseEnd_3828647 < baseStart_3828647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828684 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 3, 2, 2]
def baseStart_3828684 : Nat := 118140960795 + 3828684 * 2 ^ 59
def prefixEnd_3828684 : Nat := 4983230072969 + 3 ^ 40 * 3828684 * 2
def baseEnd_3828684 : Nat := 1965955166178803489942209

theorem tailTrace_3828684 : CollatzResearch.WordTrace tailWord_3828684 prefixEnd_3828684 1965955166178803489942209 := by
  unfold tailWord_3828684
  simp only [CollatzResearch.WordTrace]
  refine ⟨69821788830669615006846553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93095718440892820009128737 69821788830669615006846553)
  ·
    refine ⟨52366341623002211255134915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69821788830669615006846553 52366341623002211255134915)
    ·
      refine ⟨78549512434503316882702373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52366341623002211255134915 78549512434503316882702373)
      ·
        refine ⟨14728033581469371915506695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78549512434503316882702373 14728033581469371915506695)
        ·
          refine ⟨22092050372204057873260043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14728033581469371915506695 22092050372204057873260043)
          ·
            refine ⟨33138075558306086809890065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22092050372204057873260043 33138075558306086809890065)
            ·
              refine ⟨24853556668729565107417549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33138075558306086809890065 24853556668729565107417549)
              ·
                refine ⟨9320083750773586915281581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24853556668729565107417549 9320083750773586915281581)
                ·
                  refine ⟨3495031406540095093230593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9320083750773586915281581 3495031406540095093230593)
                  ·
                    refine ⟨2621273554905071319922945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3495031406540095093230593 2621273554905071319922945)
                    ·
                      refine ⟨1965955166178803489942209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621273554905071319922945 1965955166178803489942209)
                      ·
                        rfl

theorem cell23_3828684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_3828684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828684 prefixEnd_3828684 := by exact prefixLift 3828684
  have htrace : WordTrace (prefixWord ++ tailWord_3828684) baseStart_3828684 baseEnd_3828684 := by
    simpa [prefixWord, tailWord_3828684, baseEnd_3828684] using wordTrace_append hprefix tailTrace_3828684
  have hstable : (prefixWord ++ tailWord_3828684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828684).length < 2 ^ (prefixWord ++ tailWord_3828684).sum := by decide
  have hdescent : baseEnd_3828684 < baseStart_3828684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828694 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_3828694 : Nat := 118140960795 + 3828694 * 2 ^ 59
def prefixEnd_3828694 : Nat := 4983230072969 + 3 ^ 40 * 3828694 * 2
def baseEnd_3828694 : Nat := 655320100328449483605721

theorem tailTrace_3828694 : CollatzResearch.WordTrace tailWord_3828694 prefixEnd_3828694 655320100328449483605721 := by
  unfold tailWord_3828694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8727746399456437607597321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93095961594202001147704757 8727746399456437607597321)
  ·
    refine ⟨6545809799592328205697991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8727746399456437607597321 6545809799592328205697991)
    ·
      refine ⟨9818714699388492308546987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6545809799592328205697991 9818714699388492308546987)
      ·
        refine ⟨14728072049082738462820481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9818714699388492308546987 14728072049082738462820481)
        ·
          refine ⟨11046054036812053847115361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14728072049082738462820481 11046054036812053847115361)
          ·
            refine ⟨8284540527609040385336521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11046054036812053847115361 8284540527609040385336521)
            ·
              refine ⟨6213405395706780289002391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8284540527609040385336521 6213405395706780289002391)
              ·
                refine ⟨9320108093560170433503587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6213405395706780289002391 9320108093560170433503587)
                ·
                  refine ⟨13980162140340255650255381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9320108093560170433503587 13980162140340255650255381)
                  ·
                    refine ⟨655320100328449483605721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13980162140340255650255381 655320100328449483605721)
                    ·
                      rfl

theorem cell23_3828694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_3828694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828694 prefixEnd_3828694 := by exact prefixLift 3828694
  have htrace : WordTrace (prefixWord ++ tailWord_3828694) baseStart_3828694 baseEnd_3828694 := by
    simpa [prefixWord, tailWord_3828694, baseEnd_3828694] using wordTrace_append hprefix tailTrace_3828694
  have hstable : (prefixWord ++ tailWord_3828694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828694).length < 2 ^ (prefixWord ++ tailWord_3828694).sum := by decide
  have hdescent : baseEnd_3828694 < baseStart_3828694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828697 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 1, 2, 4]
def baseStart_3828697 : Nat := 118140960795 + 3828697 * 2 ^ 59
def prefixEnd_3828697 : Nat := 4983230072969 + 3 ^ 40 * 3828697 * 2
def baseEnd_3828697 : Nat := 1965961841427311939079649

theorem tailTrace_3828697 : CollatzResearch.WordTrace tailWord_3828697 prefixEnd_3828697 1965961841427311939079649 := by
  unfold tailWord_3828697
  simp only [CollatzResearch.WordTrace]
  refine ⟨139644051810292133233916345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93096034540194755489277563 139644051810292133233916345)
  ·
    refine ⟨104733038857719099925437259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139644051810292133233916345 104733038857719099925437259)
    ·
      refine ⟨157099558286578649888155889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104733038857719099925437259 157099558286578649888155889)
      ·
        refine ⟨117824668714933987416116917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157099558286578649888155889 117824668714933987416116917)
        ·
          refine ⟨11046062692025061320260961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117824668714933987416116917 11046062692025061320260961)
          ·
            refine ⟨8284547019018795990195721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11046062692025061320260961 8284547019018795990195721)
            ·
              refine ⟨6213410264264096992646791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8284547019018795990195721 6213410264264096992646791)
              ·
                refine ⟨9320115396396145488970187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6213410264264096992646791 9320115396396145488970187)
                ·
                  refine ⟨13980173094594218233455281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9320115396396145488970187 13980173094594218233455281)
                  ·
                    refine ⟨10485129820945663675091461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13980173094594218233455281 10485129820945663675091461)
                    ·
                      refine ⟨1965961841427311939079649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10485129820945663675091461 1965961841427311939079649)
                      ·
                        rfl

theorem cell23_3828697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_3828697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828697 prefixEnd_3828697 := by exact prefixLift 3828697
  have htrace : WordTrace (prefixWord ++ tailWord_3828697) baseStart_3828697 baseEnd_3828697 := by
    simpa [prefixWord, tailWord_3828697, baseEnd_3828697] using wordTrace_append hprefix tailTrace_3828697
  have hstable : (prefixWord ++ tailWord_3828697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828697).length < 2 ^ (prefixWord ++ tailWord_3828697).sum := by decide
  have hdescent : baseEnd_3828697 < baseStart_3828697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828701 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_3828701 : Nat := 118140960795 + 3828701 * 2 ^ 59
def prefixEnd_3828701 : Nat := 4983230072969 + 3 ^ 40 * 3828701 * 2
def baseEnd_3828701 : Nat := 1965963895349929923429631

theorem tailTrace_3828701 : CollatzResearch.WordTrace tailWord_3828701 prefixEnd_3828701 1965963895349929923429631 := by
  unfold tailWord_3828701
  simp only [CollatzResearch.WordTrace]
  refine ⟨139644197702277641917061957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93096131801518427944707971 139644197702277641917061957)
  ·
    refine ⟨26183287069177057859449117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139644197702277641917061957 26183287069177057859449117)
    ·
      refine ⟨9818732650941396697293419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26183287069177057859449117 9818732650941396697293419)
      ·
        refine ⟨14728098976412095045940129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9818732650941396697293419 14728098976412095045940129)
        ·
          refine ⟨11046074232309071284455097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14728098976412095045940129 11046074232309071284455097)
          ·
            refine ⟨8284555674231803463341323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11046074232309071284455097 8284555674231803463341323)
            ·
              refine ⟨12426833511347705195011985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284555674231803463341323 12426833511347705195011985)
              ·
                refine ⟨9320125133510778896258989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12426833511347705195011985 9320125133510778896258989)
                ·
                  refine ⟨3495046925066542086097121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9320125133510778896258989 3495046925066542086097121)
                  ·
                    refine ⟨2621285193799906564572841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3495046925066542086097121 2621285193799906564572841)
                    ·
                      refine ⟨1965963895349929923429631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621285193799906564572841 1965963895349929923429631)
                      ·
                        rfl

theorem cell23_3828701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_3828701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828701 prefixEnd_3828701 := by exact prefixLift 3828701
  have htrace : WordTrace (prefixWord ++ tailWord_3828701) baseStart_3828701 baseEnd_3828701 := by
    simpa [prefixWord, tailWord_3828701, baseEnd_3828701] using wordTrace_append hprefix tailTrace_3828701
  have hstable : (prefixWord ++ tailWord_3828701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828701).length < 2 ^ (prefixWord ++ tailWord_3828701).sum := by decide
  have hdescent : baseEnd_3828701 < baseStart_3828701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828718 : List Nat := [4, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_3828718 : Nat := 118140960795 + 3828718 * 2 ^ 59
def prefixEnd_3828718 : Nat := 4983230072969 + 3 ^ 40 * 3828718 * 2
def baseEnd_3828718 : Nat := 1965972624521056356917053

theorem tailTrace_3828718 : CollatzResearch.WordTrace tailWord_3828718 prefixEnd_3828718 1965972624521056356917053 := by
  unfold tailWord_3828718
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455602217902006727553851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93096545162144035880287205 17455602217902006727553851)
  ·
    refine ⟨26183403326853010091330777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17455602217902006727553851 26183403326853010091330777)
    ·
      refine ⟨19637552495139757568498083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26183403326853010091330777 19637552495139757568498083)
      ·
        refine ⟨29456328742709636352747125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19637552495139757568498083 29456328742709636352747125)
        ·
          refine ⟨2761530819629028408070043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29456328742709636352747125 2761530819629028408070043)
          ·
            refine ⟨4142296229443542612105065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761530819629028408070043 4142296229443542612105065)
            ·
              refine ⟨3106722172082656959078799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142296229443542612105065 3106722172082656959078799)
              ·
                refine ⟨4660083258123985438618199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106722172082656959078799 4660083258123985438618199)
                ·
                  refine ⟨6990124887185978157927299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660083258123985438618199 6990124887185978157927299)
                  ·
                    refine ⟨10485187330778967236890949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6990124887185978157927299 10485187330778967236890949)
                    ·
                      refine ⟨1965972624521056356917053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10485187330778967236890949 1965972624521056356917053)
                      ·
                        rfl

theorem cell23_3828718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_3828718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828718 prefixEnd_3828718 := by exact prefixLift 3828718
  have htrace : WordTrace (prefixWord ++ tailWord_3828718) baseStart_3828718 baseEnd_3828718 := by
    simpa [prefixWord, tailWord_3828718, baseEnd_3828718] using wordTrace_append hprefix tailTrace_3828718
  have hstable : (prefixWord ++ tailWord_3828718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828718).length < 2 ^ (prefixWord ++ tailWord_3828718).sum := by decide
  have hdescent : baseEnd_3828718 < baseStart_3828718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828721 : List Nat := [1, 2, 2, 2, 4, 3, 2, 1, 1, 2, 3]
def baseStart_3828721 : Nat := 118140960795 + 3828721 * 2 ^ 59
def prefixEnd_3828721 : Nat := 4983230072969 + 3 ^ 40 * 3828721 * 2
def baseEnd_3828721 : Nat := 1965974164963019845179539

theorem tailTrace_3828721 : CollatzResearch.WordTrace tailWord_3828721 prefixEnd_3828721 1965974164963019845179539 := by
  unfold tailWord_3828721
  simp only [CollatzResearch.WordTrace]
  refine ⟨139644927162205185332790017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93096618108136790221860011 139644927162205185332790017)
  ·
    refine ⟨104733695371653888999592513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139644927162205185332790017 104733695371653888999592513)
    ·
      refine ⟨78550271528740416749694385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104733695371653888999592513 78550271528740416749694385)
      ·
        refine ⟨58912703646555312562270789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78550271528740416749694385 58912703646555312562270789)
        ·
          refine ⟨11046131933729121105425773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58912703646555312562270789 11046131933729121105425773)
          ·
            refine ⟨4142299475148420414534665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11046131933729121105425773 4142299475148420414534665)
            ·
              refine ⟨3106724606361315310900999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142299475148420414534665 3106724606361315310900999)
              ·
                refine ⟨4660086909541972966351499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106724606361315310900999 4660086909541972966351499)
                ·
                  refine ⟨6990130364312959449527249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660086909541972966351499 6990130364312959449527249)
                  ·
                    refine ⟨5242597773234719587145437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6990130364312959449527249 5242597773234719587145437)
                    ·
                      refine ⟨1965974164963019845179539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5242597773234719587145437 1965974164963019845179539)
                      ·
                        rfl

theorem cell23_3828721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_3828721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828721 prefixEnd_3828721 := by exact prefixLift 3828721
  have htrace : WordTrace (prefixWord ++ tailWord_3828721) baseStart_3828721 baseEnd_3828721 := by
    simpa [prefixWord, tailWord_3828721, baseEnd_3828721] using wordTrace_append hprefix tailTrace_3828721
  have hstable : (prefixWord ++ tailWord_3828721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828721).length < 2 ^ (prefixWord ++ tailWord_3828721).sum := by decide
  have hdescent : baseEnd_3828721 < baseStart_3828721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828797 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 7]
def baseStart_3828797 : Nat := 118140960795 + 3828797 * 2 ^ 59
def prefixEnd_3828797 : Nat := 4983230072969 + 3 ^ 40 * 3828797 * 2
def baseEnd_3828797 : Nat := 218445909943640171981021

theorem tailTrace_3828797 : CollatzResearch.WordTrace tailWord_3828797 prefixEnd_3828797 218445909943640171981021 := by
  unfold tailWord_3828797
  simp only [CollatzResearch.WordTrace]
  refine ⟨139647699109929850312556645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93098466073286566875037763 139647699109929850312556645)
  ·
    refine ⟨26183943583111846933604371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139647699109929850312556645 26183943583111846933604371)
    ·
      refine ⟨39275915374667770400406557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26183943583111846933604371 39275915374667770400406557)
      ·
        refine ⟨14728468265500413900152459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39275915374667770400406557 14728468265500413900152459)
        ·
          refine ⟨22092702398250620850228689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14728468265500413900152459 22092702398250620850228689)
          ·
            refine ⟨16569526798687965637671517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22092702398250620850228689 16569526798687965637671517)
            ·
              refine ⟨6213572549507987114126819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16569526798687965637671517 6213572549507987114126819)
              ·
                refine ⟨9320358824261980671190229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6213572549507987114126819 9320358824261980671190229)
                ·
                  refine ⟨218445909943640171981021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9320358824261980671190229 218445909943640171981021)
                  ·
                    rfl

theorem cell23_3828797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_3828797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828797 prefixEnd_3828797 := by exact prefixLift 3828797
  have htrace : WordTrace (prefixWord ++ tailWord_3828797) baseStart_3828797 baseEnd_3828797 := by
    simpa [prefixWord, tailWord_3828797, baseEnd_3828797] using wordTrace_append hprefix tailTrace_3828797
  have hstable : (prefixWord ++ tailWord_3828797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828797).length < 2 ^ (prefixWord ++ tailWord_3828797).sum := by decide
  have hdescent : baseEnd_3828797 < baseStart_3828797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828810 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 3, 7]
def baseStart_3828810 : Nat := 118140960795 + 3828810 * 2 ^ 59
def prefixEnd_3828810 : Nat := 4983230072969 + 3 ^ 40 * 3828810 * 2
def baseEnd_3828810 : Nat := 655339954913756665655543

theorem tailTrace_3828810 : CollatzResearch.WordTrace tailWord_3828810 prefixEnd_3828810 655339954913756665655543 := by
  unfold tailWord_3828810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34912043314720688383194971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93098782172588502355186589 34912043314720688383194971)
  ·
    refine ⟨52368064972081032574792457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34912043314720688383194971 52368064972081032574792457)
    ·
      refine ⟨39276048729060774431094343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52368064972081032574792457 39276048729060774431094343)
      ·
        refine ⟨58914073093591161646641515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39276048729060774431094343 58914073093591161646641515)
        ·
          refine ⟨88371109640386742469962273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58914073093591161646641515 88371109640386742469962273)
          ·
            refine ⟨66278332230290056852471705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88371109640386742469962273 66278332230290056852471705)
            ·
              refine ⟨49708749172717542639353779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66278332230290056852471705 49708749172717542639353779)
              ·
                refine ⟨74563123759076313959030669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49708749172717542639353779 74563123759076313959030669)
                ·
                  refine ⟨27961171409653617734636501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74563123759076313959030669 27961171409653617734636501)
                  ·
                    refine ⟨655339954913756665655543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27961171409653617734636501 655339954913756665655543)
                    ·
                      rfl

theorem cell23_3828810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_3828810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828810 prefixEnd_3828810 := by exact prefixLift 3828810
  have htrace : WordTrace (prefixWord ++ tailWord_3828810) baseStart_3828810 baseEnd_3828810 := by
    simpa [prefixWord, tailWord_3828810, baseEnd_3828810] using wordTrace_append hprefix tailTrace_3828810
  have hstable : (prefixWord ++ tailWord_3828810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828810).length < 2 ^ (prefixWord ++ tailWord_3828810).sum := by decide
  have hdescent : baseEnd_3828810 < baseStart_3828810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828847 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 4]
def baseStart_3828847 : Nat := 118140960795 + 3828847 * 2 ^ 59
def prefixEnd_3828847 : Nat := 4983230072969 + 3 ^ 40 * 3828847 * 2
def baseEnd_3828847 : Nat := 1966038863525486352203959

theorem tailTrace_3828847 : CollatzResearch.WordTrace tailWord_3828847 prefixEnd_3828847 1966038863525486352203959 := by
  unfold tailWord_3828847
  simp only [CollatzResearch.WordTrace]
  refine ⟨139649522759748708851876795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93099681839832472567917863 139649522759748708851876795)
  ·
    refine ⟨209474284139623063277815193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139649522759748708851876795 209474284139623063277815193)
    ·
      refine ⟨157105713104717297458361395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209474284139623063277815193 157105713104717297458361395)
      ·
        refine ⟨235658569657075946187542093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157105713104717297458361395 235658569657075946187542093)
        ·
          refine ⟨88371963621403479820328285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235658569657075946187542093 88371963621403479820328285)
          ·
            refine ⟨33139486358026304932623107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88371963621403479820328285 33139486358026304932623107)
            ·
              refine ⟨49709229537039457398934661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33139486358026304932623107 49709229537039457398934661)
              ·
                refine ⟨9320480538194898262300249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49709229537039457398934661 9320480538194898262300249)
                ·
                  refine ⟨6990360403646173696725187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9320480538194898262300249 6990360403646173696725187)
                  ·
                    refine ⟨10485540605469260545087781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6990360403646173696725187 10485540605469260545087781)
                    ·
                      refine ⟨1966038863525486352203959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10485540605469260545087781 1966038863525486352203959)
                      ·
                        rfl

theorem cell23_3828847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_3828847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828847 prefixEnd_3828847 := by exact prefixLift 3828847
  have htrace : WordTrace (prefixWord ++ tailWord_3828847) baseStart_3828847 baseEnd_3828847 := by
    simpa [prefixWord, tailWord_3828847, baseEnd_3828847] using wordTrace_append hprefix tailTrace_3828847
  have hstable : (prefixWord ++ tailWord_3828847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828847).length < 2 ^ (prefixWord ++ tailWord_3828847).sum := by decide
  have hdescent : baseEnd_3828847 < baseStart_3828847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828867 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 3]
def baseStart_3828867 : Nat := 118140960795 + 3828867 * 2 ^ 59
def prefixEnd_3828867 : Nat := 4983230072969 + 3 ^ 40 * 3828867 * 2
def baseEnd_3828867 : Nat := 1966049133138576273953867

theorem tailTrace_3828867 : CollatzResearch.WordTrace tailWord_3828867 prefixEnd_3828867 1966049133138576273953867 := by
  unfold tailWord_3828867
  simp only [CollatzResearch.WordTrace]
  refine ⟨139650252219676252267604855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93100168146450834845069903 139650252219676252267604855)
  ·
    refine ⟨209475378329514378401407283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139650252219676252267604855 209475378329514378401407283)
    ·
      refine ⟨314213067494271567602110925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209475378329514378401407283 314213067494271567602110925)
      ·
        refine ⟨117829900310351837850791597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314213067494271567602110925 117829900310351837850791597)
        ·
          refine ⟨44186212616381939194046849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117829900310351837850791597 44186212616381939194046849)
          ·
            refine ⟨33139659462286454395535137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44186212616381939194046849 33139659462286454395535137)
            ·
              refine ⟨24854744596714840796651353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33139659462286454395535137 24854744596714840796651353)
              ·
                refine ⟨18641058447536130597488515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24854744596714840796651353 18641058447536130597488515)
                ·
                  refine ⟨27961587671304195896232773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18641058447536130597488515 27961587671304195896232773)
                  ·
                    refine ⟨5242797688369536730543645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27961587671304195896232773 5242797688369536730543645)
                    ·
                      refine ⟨1966049133138576273953867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5242797688369536730543645 1966049133138576273953867)
                      ·
                        rfl

theorem cell23_3828867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_3828867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828867 prefixEnd_3828867 := by exact prefixLift 3828867
  have htrace : WordTrace (prefixWord ++ tailWord_3828867) baseStart_3828867 baseEnd_3828867 := by
    simpa [prefixWord, tailWord_3828867, baseEnd_3828867] using wordTrace_append hprefix tailTrace_3828867
  have hstable : (prefixWord ++ tailWord_3828867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828867).length < 2 ^ (prefixWord ++ tailWord_3828867).sum := by decide
  have hdescent : baseEnd_3828867 < baseStart_3828867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828874 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 3, 4]
def baseStart_3828874 : Nat := 118140960795 + 3828874 * 2 ^ 59
def prefixEnd_3828874 : Nat := 4983230072969 + 3 ^ 40 * 3828874 * 2
def baseEnd_3828874 : Nat := 655350909167719248855445

theorem tailTrace_3828874 : CollatzResearch.WordTrace tailWord_3828874 prefixEnd_3828874 655350909167719248855445 := by
  unfold tailWord_3828874
  simp only [CollatzResearch.WordTrace]
  refine ⟨34912626882662723115777419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93100338353767261642073117 34912626882662723115777419)
  ·
    refine ⟨52368940323994084673666129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34912626882662723115777419 52368940323994084673666129)
    ·
      refine ⟨39276705242995563505249597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52368940323994084673666129 39276705242995563505249597)
      ·
        refine ⟨14728764466123336314468599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39276705242995563505249597 14728764466123336314468599)
        ·
          refine ⟨22093146699185004471702899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14728764466123336314468599 22093146699185004471702899)
          ·
            refine ⟨33139720048777506707554349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22093146699185004471702899 33139720048777506707554349)
            ·
              refine ⟨12427395018291565015332881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33139720048777506707554349 12427395018291565015332881)
              ·
                refine ⟨9320546263718673761499661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12427395018291565015332881 9320546263718673761499661)
                ·
                  refine ⟨3495204848894502660562373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9320546263718673761499661 3495204848894502660562373)
                  ·
                    refine ⟨655350909167719248855445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3495204848894502660562373 655350909167719248855445)
                    ·
                      rfl

theorem cell23_3828874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_3828874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828874 prefixEnd_3828874 := by exact prefixLift 3828874
  have htrace : WordTrace (prefixWord ++ tailWord_3828874) baseStart_3828874 baseEnd_3828874 := by
    simpa [prefixWord, tailWord_3828874, baseEnd_3828874] using wordTrace_append hprefix tailTrace_3828874
  have hstable : (prefixWord ++ tailWord_3828874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828874).length < 2 ^ (prefixWord ++ tailWord_3828874).sum := by decide
  have hdescent : baseEnd_3828874 < baseStart_3828874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828894 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3828894 : Nat := 118140960795 + 3828894 * 2 ^ 59
def prefixEnd_3828894 : Nat := 4983230072969 + 3 ^ 40 * 3828894 * 2
def baseEnd_3828894 : Nat := 1966062997116247668316243

theorem tailTrace_3828894 : CollatzResearch.WordTrace tailWord_3828894 prefixEnd_3828894 1966062997116247668316243 := by
  unfold tailWord_3828894
  simp only [CollatzResearch.WordTrace]
  refine ⟨17456404623822304484854717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93100824660385623919225157 17456404623822304484854717)
  ·
    refine ⟨6546151733933364181820519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17456404623822304484854717 6546151733933364181820519)
    ·
      refine ⟨9819227600900046272730779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6546151733933364181820519 9819227600900046272730779)
      ·
        refine ⟨14728841401350069409096169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9819227600900046272730779 14728841401350069409096169)
        ·
          refine ⟨11046631051012552056822127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14728841401350069409096169 11046631051012552056822127)
          ·
            refine ⟨16569946576518828085233191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11046631051012552056822127 16569946576518828085233191)
            ·
              refine ⟨24854919864778242127849787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16569946576518828085233191 24854919864778242127849787)
              ·
                refine ⟨37282379797167363191774681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24854919864778242127849787 37282379797167363191774681)
                ·
                  refine ⟨27961784847875522393831011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37282379797167363191774681 27961784847875522393831011)
                  ·
                    refine ⟨41942677271813283590746517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27961784847875522393831011 41942677271813283590746517)
                    ·
                      refine ⟨1966062997116247668316243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41942677271813283590746517 1966062997116247668316243)
                      ·
                        rfl

theorem cell23_3828894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3828894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828894 prefixEnd_3828894 := by exact prefixLift 3828894
  have htrace : WordTrace (prefixWord ++ tailWord_3828894) baseStart_3828894 baseEnd_3828894 := by
    simpa [prefixWord, tailWord_3828894, baseEnd_3828894] using wordTrace_append hprefix tailTrace_3828894
  have hstable : (prefixWord ++ tailWord_3828894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828894).length < 2 ^ (prefixWord ++ tailWord_3828894).sum := by decide
  have hdescent : baseEnd_3828894 < baseStart_3828894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828937 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 7, 1, 4]
def baseStart_3828937 : Nat := 118140960795 + 3828937 * 2 ^ 59
def prefixEnd_3828937 : Nat := 4983230072969 + 3 ^ 40 * 3828937 * 2
def baseEnd_3828937 : Nat := 1966085076784391000078545

theorem tailTrace_3828937 : CollatzResearch.WordTrace tailWord_3828937 prefixEnd_3828937 1966085076784391000078545 := by
  unfold tailWord_3828937
  simp only [CollatzResearch.WordTrace]
  refine ⟨139652805329422654222653065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93101870219615102815102043 139652805329422654222653065)
  ·
    refine ⟨104739603997066990666989799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139652805329422654222653065 104739603997066990666989799)
    ·
      refine ⟨157109405995600486000484699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104739603997066990666989799 157109405995600486000484699)
      ·
        refine ⟨235664108993400729000727049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157109405995600486000484699 235664108993400729000727049)
        ·
          refine ⟨176748081745050546750545287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235664108993400729000727049 176748081745050546750545287)
          ·
            refine ⟨265122122617575820125817931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176748081745050546750545287 265122122617575820125817931)
            ·
              refine ⟨397683183926363730188726897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265122122617575820125817931 397683183926363730188726897)
              ·
                refine ⟨298262387944772797641545173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397683183926363730188726897 298262387944772797641545173)
                ·
                  refine ⟨6990524717455612444723715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 298262387944772797641545173 6990524717455612444723715)
                  ·
                    refine ⟨10485787076183418667085573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6990524717455612444723715 10485787076183418667085573)
                    ·
                      refine ⟨1966085076784391000078545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10485787076183418667085573 1966085076784391000078545)
                      ·
                        rfl

theorem cell23_3828937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_3828937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828937 prefixEnd_3828937 := by exact prefixLift 3828937
  have htrace : WordTrace (prefixWord ++ tailWord_3828937) baseStart_3828937 baseEnd_3828937 := by
    simpa [prefixWord, tailWord_3828937, baseEnd_3828937] using wordTrace_append hprefix tailTrace_3828937
  have hstable : (prefixWord ++ tailWord_3828937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828937).length < 2 ^ (prefixWord ++ tailWord_3828937).sum := by decide
  have hdescent : baseEnd_3828937 < baseStart_3828937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828964 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_3828964 : Nat := 118140960795 + 3828964 * 2 ^ 59
def prefixEnd_3828964 : Nat := 4983230072969 + 3 ^ 40 * 3828964 * 2
def baseEnd_3828964 : Nat := 655366313587354131480307

theorem tailTrace_3828964 : CollatzResearch.WordTrace tailWord_3828964 prefixEnd_3828964 655366313587354131480307 := by
  unfold tailWord_3828964
  simp only [CollatzResearch.WordTrace]
  refine ⟨69826895050162418916942973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93102526733549891889257297 69826895050162418916942973)
  ·
    refine ⟨26185085643810907093853615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69826895050162418916942973 26185085643810907093853615)
    ·
      refine ⟨39277628465716360640780423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26185085643810907093853615 39277628465716360640780423)
      ·
        refine ⟨58916442698574540961170635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39277628465716360640780423 58916442698574540961170635)
        ·
          refine ⟨88374664047861811441755953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58916442698574540961170635 88374664047861811441755953)
          ·
            refine ⟨66280998035896358581316965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88374664047861811441755953 66280998035896358581316965)
            ·
              refine ⟨12427687131730567233996931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66280998035896358581316965 12427687131730567233996931)
              ·
                refine ⟨18641530697595850850995397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12427687131730567233996931 18641530697595850850995397)
                ·
                  refine ⟨3495287005799222034561637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18641530697595850850995397 3495287005799222034561637)
                  ·
                    refine ⟨655366313587354131480307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3495287005799222034561637 655366313587354131480307)
                    ·
                      rfl

theorem cell23_3828964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_3828964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828964 prefixEnd_3828964 := by exact prefixLift 3828964
  have htrace : WordTrace (prefixWord ++ tailWord_3828964) baseStart_3828964 baseEnd_3828964 := by
    simpa [prefixWord, tailWord_3828964, baseEnd_3828964] using wordTrace_append hprefix tailTrace_3828964
  have hstable : (prefixWord ++ tailWord_3828964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828964).length < 2 ^ (prefixWord ++ tailWord_3828964).sum := by decide
  have hdescent : baseEnd_3828964 < baseStart_3828964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828965 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 3, 1, 3]
def baseStart_3828965 : Nat := 118140960795 + 3828965 * 2 ^ 59
def prefixEnd_3828965 : Nat := 4983230072969 + 3 ^ 40 * 3828965 * 2
def baseEnd_3828965 : Nat := 1966099454242716890528417

theorem tailTrace_3828965 : CollatzResearch.WordTrace tailWord_3828965 prefixEnd_3828965 1966099454242716890528417 := by
  unfold tailWord_3828965
  simp only [CollatzResearch.WordTrace]
  refine ⟨139653826573321215004672349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93102551048880810003114899 139653826573321215004672349)
  ·
    refine ⟨52370184964995455626752131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139653826573321215004672349 52370184964995455626752131)
    ·
      refine ⟨78555277447493183440128197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52370184964995455626752131 78555277447493183440128197)
      ·
        refine ⟨14729114521404971895024037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78555277447493183440128197 14729114521404971895024037)
        ·
          refine ⟨2761708972763432230317007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14729114521404971895024037 2761708972763432230317007)
          ·
            refine ⟨4142563459145148345475511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761708972763432230317007 4142563459145148345475511)
            ·
              refine ⟨6213845188717722518213267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4142563459145148345475511 6213845188717722518213267)
              ·
                refine ⟨9320767783076583777319901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6213845188717722518213267 9320767783076583777319901)
                ·
                  refine ⟨3495287918653718916494963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9320767783076583777319901 3495287918653718916494963)
                  ·
                    refine ⟨5242931877980578374742445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3495287918653718916494963 5242931877980578374742445)
                    ·
                      refine ⟨1966099454242716890528417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5242931877980578374742445 1966099454242716890528417)
                      ·
                        rfl

theorem cell23_3828965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_3828965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828965 prefixEnd_3828965 := by exact prefixLift 3828965
  have htrace : WordTrace (prefixWord ++ tailWord_3828965) baseStart_3828965 baseEnd_3828965 := by
    simpa [prefixWord, tailWord_3828965, baseEnd_3828965] using wordTrace_append hprefix tailTrace_3828965
  have hstable : (prefixWord ++ tailWord_3828965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828965).length < 2 ^ (prefixWord ++ tailWord_3828965).sum := by decide
  have hdescent : baseEnd_3828965 < baseStart_3828965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828974 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_3828974 : Nat := 118140960795 + 3828974 * 2 ^ 59
def prefixEnd_3828974 : Nat := 4983230072969 + 3 ^ 40 * 3828974 * 2
def baseEnd_3828974 : Nat := 1966104075568607355315875

theorem tailTrace_3828974 : CollatzResearch.WordTrace tailWord_3828974 prefixEnd_3828974 1966104075568607355315875 := by
  unfold tailWord_3828974
  simp only [CollatzResearch.WordTrace]
  refine ⟨17456769353786076192718747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93102769886859073027833317 17456769353786076192718747)
  ·
    refine ⟨26185154030679114289078121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17456769353786076192718747 26185154030679114289078121)
    ·
      refine ⟨19638865523009335716808591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26185154030679114289078121 19638865523009335716808591)
      ·
        refine ⟨29458298284514003575212887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19638865523009335716808591 29458298284514003575212887)
        ·
          refine ⟨44187447426771005362819331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29458298284514003575212887 44187447426771005362819331)
          ·
            refine ⟨66281171140156508044228997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44187447426771005362819331 66281171140156508044228997)
            ·
              refine ⟨12427719588779345258292937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66281171140156508044228997 12427719588779345258292937)
              ·
                refine ⟨9320789691584508943719703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12427719588779345258292937 9320789691584508943719703)
                ·
                  refine ⟨13981184537376763415579555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9320789691584508943719703 13981184537376763415579555)
                  ·
                    refine ⟨20971776806065145123369333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13981184537376763415579555 20971776806065145123369333)
                    ·
                      refine ⟨1966104075568607355315875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20971776806065145123369333 1966104075568607355315875)
                      ·
                        rfl

theorem cell23_3828974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_3828974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828974 prefixEnd_3828974 := by exact prefixLift 3828974
  have htrace : WordTrace (prefixWord ++ tailWord_3828974) baseStart_3828974 baseEnd_3828974 := by
    simpa [prefixWord, tailWord_3828974, baseEnd_3828974] using wordTrace_append hprefix tailTrace_3828974
  have hstable : (prefixWord ++ tailWord_3828974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828974).length < 2 ^ (prefixWord ++ tailWord_3828974).sum := by decide
  have hdescent : baseEnd_3828974 < baseStart_3828974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828988 : List Nat := [2, 2, 2, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_3828988 : Nat := 118140960795 + 3828988 * 2 ^ 59
def prefixEnd_3828988 : Nat := 4983230072969 + 3 ^ 40 * 3828988 * 2
def baseEnd_3828988 : Nat := 1966111264297770300540811

theorem tailTrace_3828988 : CollatzResearch.WordTrace tailWord_3828988 prefixEnd_3828988 1966111264297770300540811 := by
  unfold tailWord_3828988
  simp only [CollatzResearch.WordTrace]
  refine ⟨69827332726118944966379809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93103110301491926621839745 69827332726118944966379809)
  ·
    refine ⟨52370499544589208724784857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69827332726118944966379809 52370499544589208724784857)
    ·
      refine ⟨39277874658441906543588643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52370499544589208724784857 39277874658441906543588643)
      ·
        refine ⟨58916811987662859815382965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39277874658441906543588643 58916811987662859815382965)
        ·
          refine ⟨5523451123843393107692153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58916811987662859815382965 5523451123843393107692153)
          ·
            refine ⟨4142588342882544830769115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5523451123843393107692153 4142588342882544830769115)
            ·
              refine ⟨6213882514323817246153673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4142588342882544830769115 6213882514323817246153673)
              ·
                refine ⟨4660411885742862934615255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6213882514323817246153673 4660411885742862934615255)
                ·
                  refine ⟨6990617828614294401922883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660411885742862934615255 6990617828614294401922883)
                  ·
                    refine ⟨10485926742921441602884325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6990617828614294401922883 10485926742921441602884325)
                    ·
                      refine ⟨1966111264297770300540811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10485926742921441602884325 1966111264297770300540811)
                      ·
                        rfl

theorem cell23_3828988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_3828988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828988 prefixEnd_3828988 := by exact prefixLift 3828988
  have htrace : WordTrace (prefixWord ++ tailWord_3828988) baseStart_3828988 baseEnd_3828988 := by
    simpa [prefixWord, tailWord_3828988, baseEnd_3828988] using wordTrace_append hprefix tailTrace_3828988
  have hstable : (prefixWord ++ tailWord_3828988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828988).length < 2 ^ (prefixWord ++ tailWord_3828988).sum := by decide
  have hdescent : baseEnd_3828988 < baseStart_3828988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828991 : List Nat := [1, 1, 2, 2, 1, 5, 3, 2, 1, 2, 3]
def baseStart_3828991 : Nat := 118140960795 + 3828991 * 2 ^ 59
def prefixEnd_3828991 : Nat := 4983230072969 + 3 ^ 40 * 3828991 * 2
def baseEnd_3828991 : Nat := 1966112804739733788803297

theorem tailTrace_3828991 : CollatzResearch.WordTrace tailWord_3828991 prefixEnd_3828991 1966112804739733788803297 := by
  unfold tailWord_3828991
  simp only [CollatzResearch.WordTrace]
  refine ⟨139654774871227021445118827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93103183247484680963412551 139654774871227021445118827)
  ·
    refine ⟨209482162306840532167678241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139654774871227021445118827 209482162306840532167678241)
    ·
      refine ⟨157111621730130399125758681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209482162306840532167678241 157111621730130399125758681)
      ·
        refine ⟨117833716297597799344319011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157111621730130399125758681 117833716297597799344319011)
        ·
          refine ⟨176750574446396699016478517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117833716297597799344319011 176750574446396699016478517)
          ·
            refine ⟨16570366354349690532794861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176750574446396699016478517 16570366354349690532794861)
            ·
              refine ⟨6213887382881133949798073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16570366354349690532794861 6213887382881133949798073)
              ·
                refine ⟨4660415537160850462348555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6213887382881133949798073 4660415537160850462348555)
                ·
                  refine ⟨6990623305741275693522833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660415537160850462348555 6990623305741275693522833)
                  ·
                    refine ⟨5242967479305956770142125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6990623305741275693522833 5242967479305956770142125)
                    ·
                      refine ⟨1966112804739733788803297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5242967479305956770142125 1966112804739733788803297)
                      ·
                        rfl

theorem cell23_3828991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_3828991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3828991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3828991 prefixEnd_3828991 := by exact prefixLift 3828991
  have htrace : WordTrace (prefixWord ++ tailWord_3828991) baseStart_3828991 baseEnd_3828991 := by
    simpa [prefixWord, tailWord_3828991, baseEnd_3828991] using wordTrace_append hprefix tailTrace_3828991
  have hstable : (prefixWord ++ tailWord_3828991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828991).length < 2 ^ (prefixWord ++ tailWord_3828991).sum := by decide
  have hdescent : baseEnd_3828991 < baseStart_3828991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829004 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 3, 3, 3]
def baseStart_3829004 : Nat := 118140960795 + 3829004 * 2 ^ 59
def prefixEnd_3829004 : Nat := 4983230072969 + 3 ^ 40 * 3829004 * 2
def baseEnd_3829004 : Nat := 1966119479988242237940737

theorem tailTrace_3829004 : CollatzResearch.WordTrace tailWord_3829004 prefixEnd_3829004 1966119479988242237940737 := by
  unfold tailWord_3829004
  simp only [CollatzResearch.WordTrace]
  refine ⟨69827624510089962332671033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93103499346786616443561377 69827624510089962332671033)
  ·
    refine ⟨52370718382567471749503275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69827624510089962332671033 52370718382567471749503275)
    ·
      refine ⟨78556077573851207624254913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52370718382567471749503275 78556077573851207624254913)
      ·
        refine ⟨58917058180388405718191185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78556077573851207624254913 58917058180388405718191185)
        ·
          refine ⟨44187793635291304288643389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58917058180388405718191185 44187793635291304288643389)
          ·
            refine ⟨16570422613234239108241271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44187793635291304288643389 16570422613234239108241271)
            ·
              refine ⟨24855633919851358662361907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16570422613234239108241271 24855633919851358662361907)
              ·
                refine ⟨37283450879777037993542861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24855633919851358662361907 37283450879777037993542861)
                ·
                  refine ⟨13981294079916389247578573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37283450879777037993542861 13981294079916389247578573)
                  ·
                    refine ⟨5242985279968645967841965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13981294079916389247578573 5242985279968645967841965)
                    ·
                      refine ⟨1966119479988242237940737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5242985279968645967841965 1966119479988242237940737)
                      ·
                        rfl

theorem cell23_3829004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_3829004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829004 prefixEnd_3829004 := by exact prefixLift 3829004
  have htrace : WordTrace (prefixWord ++ tailWord_3829004) baseStart_3829004 baseEnd_3829004 := by
    simpa [prefixWord, tailWord_3829004, baseEnd_3829004] using wordTrace_append hprefix tailTrace_3829004
  have hstable : (prefixWord ++ tailWord_3829004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829004).length < 2 ^ (prefixWord ++ tailWord_3829004).sum := by decide
  have hdescent : baseEnd_3829004 < baseStart_3829004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829054 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3829054 : Nat := 118140960795 + 3829054 * 2 ^ 59
def prefixEnd_3829054 : Nat := 4983230072969 + 3 ^ 40 * 3829054 * 2
def baseEnd_3829054 : Nat := 655381718006989014105169

theorem tailTrace_3829054 : CollatzResearch.WordTrace tailWord_3829054 prefixEnd_3829054 655381718006989014105169 := by
  unfold tailWord_3829054
  simp only [CollatzResearch.WordTrace]
  refine ⟨17457134083749847900582777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93104715113332522136441477 17457134083749847900582777)
  ·
    refine ⟨13092850562812385925437083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17457134083749847900582777 13092850562812385925437083)
    ·
      refine ⟨19639275844218578888155625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13092850562812385925437083 19639275844218578888155625)
      ·
        refine ⟨14729456883163934166116719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19639275844218578888155625 14729456883163934166116719)
        ·
          refine ⟨22094185324745901249175079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14729456883163934166116719 22094185324745901249175079)
          ·
            refine ⟨33141277987118851873762619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22094185324745901249175079 33141277987118851873762619)
            ·
              refine ⟨49711916980678277810643929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33141277987118851873762619 49711916980678277810643929)
              ·
                refine ⟨37283937735508708357982947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49711916980678277810643929 37283937735508708357982947)
                ·
                  refine ⟨55925906603263062536974421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37283937735508708357982947 55925906603263062536974421)
                  ·
                    refine ⟨655381718006989014105169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55925906603263062536974421 655381718006989014105169)
                    ·
                      rfl

theorem cell23_3829054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3829054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829054 prefixEnd_3829054 := by exact prefixLift 3829054
  have htrace : WordTrace (prefixWord ++ tailWord_3829054) baseStart_3829054 baseEnd_3829054 := by
    simpa [prefixWord, tailWord_3829054, baseEnd_3829054] using wordTrace_append hprefix tailTrace_3829054
  have hstable : (prefixWord ++ tailWord_3829054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829054).length < 2 ^ (prefixWord ++ tailWord_3829054).sum := by decide
  have hdescent : baseEnd_3829054 < baseStart_3829054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829095 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_3829095 : Nat := 118140960795 + 3829095 * 2 ^ 59
def prefixEnd_3829095 : Nat := 4983230072969 + 3 ^ 40 * 3829095 * 2
def baseEnd_3829095 : Nat := 1966166206727801381902819

theorem tailTrace_3829095 : CollatzResearch.WordTrace tailWord_3829095 prefixEnd_3829095 1966166206727801381902819 := by
  unfold tailWord_3829095
  simp only [CollatzResearch.WordTrace]
  refine ⟨139658568062850247206904739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93105712041900164804603159 139658568062850247206904739)
  ·
    refine ⟨209487852094275370810357109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139658568062850247206904739 209487852094275370810357109)
    ·
      refine ⟨19639486133838316013470979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209487852094275370810357109 19639486133838316013470979)
      ·
        refine ⟨29459229200757474020206469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19639486133838316013470979 29459229200757474020206469)
        ·
          refine ⟨5523605475142026378788713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29459229200757474020206469 5523605475142026378788713)
          ·
            refine ⟨4142704106356519784091535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5523605475142026378788713 4142704106356519784091535)
            ·
              refine ⟨6214056159534779676137303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4142704106356519784091535 6214056159534779676137303)
              ·
                refine ⟨9321084239302169514205955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6214056159534779676137303 9321084239302169514205955)
                ·
                  refine ⟨13981626358953254271308933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9321084239302169514205955 13981626358953254271308933)
                  ·
                    refine ⟨2621554942303735175870425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13981626358953254271308933 2621554942303735175870425)
                    ·
                      refine ⟨1966166206727801381902819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621554942303735175870425 1966166206727801381902819)
                      ·
                        rfl

theorem cell23_3829095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_3829095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829095 prefixEnd_3829095 := by exact prefixLift 3829095
  have htrace : WordTrace (prefixWord ++ tailWord_3829095) baseStart_3829095 baseEnd_3829095 := by
    simpa [prefixWord, tailWord_3829095, baseEnd_3829095] using wordTrace_append hprefix tailTrace_3829095
  have hstable : (prefixWord ++ tailWord_3829095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829095).length < 2 ^ (prefixWord ++ tailWord_3829095).sum := by decide
  have hdescent : baseEnd_3829095 < baseStart_3829095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829164 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_3829164 : Nat := 118140960795 + 3829164 * 2 ^ 59
def prefixEnd_3829164 : Nat := 4983230072969 + 3 ^ 40 * 3829164 * 2
def baseEnd_3829164 : Nat := 1966201636892961611940001

theorem tailTrace_3829164 : CollatzResearch.WordTrace tailWord_3829164 prefixEnd_3829164 1966201636892961611940001 := by
  unfold tailWord_3829164
  simp only [CollatzResearch.WordTrace]
  refine ⟨69830542349800135995583273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93107389799733514660777697 69830542349800135995583273)
  ·
    refine ⟨52372906762350101996687455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69830542349800135995583273 52372906762350101996687455)
    ·
      refine ⟨78559360143525152995031183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52372906762350101996687455 78559360143525152995031183)
      ·
        refine ⟨117839040215287729492546775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78559360143525152995031183 117839040215287729492546775)
        ·
          refine ⟨176758560322931594238820163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117839040215287729492546775 176758560322931594238820163)
          ·
            refine ⟨265137840484397391358230245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176758560322931594238820163 265137840484397391358230245)
            ·
              refine ⟨49713345090824510879668171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265137840484397391358230245 49713345090824510879668171)
              ·
                refine ⟨74570017636236766319502257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49713345090824510879668171 74570017636236766319502257)
                ·
                  refine ⟨55927513227177574739626693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74570017636236766319502257 55927513227177574739626693)
                  ·
                    refine ⟨10486408730095795263680005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55927513227177574739626693 10486408730095795263680005)
                    ·
                      refine ⟨1966201636892961611940001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10486408730095795263680005 1966201636892961611940001)
                      ·
                        rfl

theorem cell23_3829164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_3829164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829164 prefixEnd_3829164 := by exact prefixLift 3829164
  have htrace : WordTrace (prefixWord ++ tailWord_3829164) baseStart_3829164 baseEnd_3829164 := by
    simpa [prefixWord, tailWord_3829164, baseEnd_3829164] using wordTrace_append hprefix tailTrace_3829164
  have hstable : (prefixWord ++ tailWord_3829164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829164).length < 2 ^ (prefixWord ++ tailWord_3829164).sum := by decide
  have hdescent : baseEnd_3829164 < baseStart_3829164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829191 : List Nat := [1, 1, 4, 1, 1, 3, 4, 2, 6]
def baseStart_3829191 : Nat := 118140960795 + 3829191 * 2 ^ 59
def prefixEnd_3829191 : Nat := 4983230072969 + 3 ^ 40 * 3829191 * 2
def baseEnd_3829191 : Nat := 218468388985625889589153

theorem tailTrace_3829191 : CollatzResearch.WordTrace tailWord_3829191 prefixEnd_3829191 218468388985625889589153 := by
  unfold tailWord_3829191
  simp only [CollatzResearch.WordTrace]
  refine ⟨139662069470502455602399427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93108046313668303734932951 139662069470502455602399427)
  ·
    refine ⟨209493104205753683403599141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139662069470502455602399427 209493104205753683403599141)
    ·
      refine ⟨39279957038578815638174839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209493104205753683403599141 39279957038578815638174839)
      ·
        refine ⟨58919935557868223457262259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39279957038578815638174839 58919935557868223457262259)
        ·
          refine ⟨88379903336802335185893389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58919935557868223457262259 88379903336802335185893389)
          ·
            refine ⟨33142463751300875694710021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88379903336802335185893389 33142463751300875694710021)
            ·
              refine ⟨6214211953368914192758129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33142463751300875694710021 6214211953368914192758129)
              ·
                refine ⟨4660658965026685644568597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6214211953368914192758129 4660658965026685644568597)
                ·
                  refine ⟨218468388985625889589153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4660658965026685644568597 218468388985625889589153)
                  ·
                    rfl

theorem cell23_3829191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 6].length) (baseStart_3829191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829191 prefixEnd_3829191 := by exact prefixLift 3829191
  have htrace : WordTrace (prefixWord ++ tailWord_3829191) baseStart_3829191 baseEnd_3829191 := by
    simpa [prefixWord, tailWord_3829191, baseEnd_3829191] using wordTrace_append hprefix tailTrace_3829191
  have hstable : (prefixWord ++ tailWord_3829191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829191).length < 2 ^ (prefixWord ++ tailWord_3829191).sum := by decide
  have hdescent : baseEnd_3829191 < baseStart_3829191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829195 : List Nat := [1, 1, 1, 1, 3, 3, 6, 2, 1, 4]
def baseStart_3829195 : Nat := 118140960795 + 3829195 * 2 ^ 59
def prefixEnd_3829195 : Nat := 4983230072969 + 3 ^ 40 * 3829195 * 2
def baseEnd_3829195 : Nat := 655405851597750330217453

theorem tailTrace_3829195 : CollatzResearch.WordTrace tailWord_3829195 prefixEnd_3829195 655405851597750330217453 := by
  unfold tailWord_3829195
  simp only [CollatzResearch.WordTrace]
  refine ⟨139662215362487964285545039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93108143574991976190363359 139662215362487964285545039)
  ·
    refine ⟨209493323043731946428317559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139662215362487964285545039 209493323043731946428317559)
    ·
      refine ⟨314239984565597919642476339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209493323043731946428317559 314239984565597919642476339)
      ·
        refine ⟨471359976848396879463714509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314239984565597919642476339 471359976848396879463714509)
        ·
          refine ⟨176759991318148829798892941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471359976848396879463714509 176759991318148829798892941)
          ·
            refine ⟨66284996744305811174584853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176759991318148829798892941 66284996744305811174584853)
            ·
              refine ⟨3107109222389334898808665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66284996744305811174584853 3107109222389334898808665)
              ·
                refine ⟨2330331916792001174106499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3107109222389334898808665 2330331916792001174106499)
                ·
                  refine ⟨3495497875188001761159749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330331916792001174106499 3495497875188001761159749)
                  ·
                    refine ⟨655405851597750330217453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3495497875188001761159749 655405851597750330217453)
                    ·
                      rfl

theorem cell23_3829195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 1, 4].length) (baseStart_3829195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829195 prefixEnd_3829195 := by exact prefixLift 3829195
  have htrace : WordTrace (prefixWord ++ tailWord_3829195) baseStart_3829195 baseEnd_3829195 := by
    simpa [prefixWord, tailWord_3829195, baseEnd_3829195] using wordTrace_append hprefix tailTrace_3829195
  have hstable : (prefixWord ++ tailWord_3829195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829195).length < 2 ^ (prefixWord ++ tailWord_3829195).sum := by decide
  have hdescent : baseEnd_3829195 < baseStart_3829195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829211 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 7, 5, 2]
def baseStart_3829211 : Nat := 118140960795 + 3829211 * 2 ^ 59
def prefixEnd_3829211 : Nat := 4983230072969 + 3 ^ 40 * 3829211 * 2
def baseEnd_3829211 : Nat := 1966225770483722928052285

theorem tailTrace_3829211 : CollatzResearch.WordTrace tailWord_3829211 prefixEnd_3829211 1966225770483722928052285 := by
  unfold tailWord_3829211
  simp only [CollatzResearch.WordTrace]
  refine ⟨139662798930429999018127487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93108532620286666012084991 139662798930429999018127487)
  ·
    refine ⟨209494198395644998527191231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139662798930429999018127487 209494198395644998527191231)
    ·
      refine ⟨314241297593467497790786847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209494198395644998527191231 314241297593467497790786847)
      ·
        refine ⟨471361946390201246686180271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314241297593467497790786847 471361946390201246686180271)
        ·
          refine ⟨707042919585301870029270407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471361946390201246686180271 707042919585301870029270407)
          ·
            refine ⟨1060564379377952805043905611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707042919585301870029270407 1060564379377952805043905611)
            ·
              refine ⟨1590846569066929207565858417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060564379377952805043905611 1590846569066929207565858417)
              ·
                refine ⟨1193134926800196905674393813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590846569066929207565858417 1193134926800196905674393813)
                ·
                  refine ⟨27964099846879614976743605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1193134926800196905674393813 27964099846879614976743605)
                  ·
                    refine ⟨2621634360644963904069713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27964099846879614976743605 2621634360644963904069713)
                    ·
                      refine ⟨1966225770483722928052285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621634360644963904069713 1966225770483722928052285)
                      ·
                        rfl

theorem cell23_3829211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 5, 2].length) (baseStart_3829211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829211 prefixEnd_3829211 := by exact prefixLift 3829211
  have htrace : WordTrace (prefixWord ++ tailWord_3829211) baseStart_3829211 baseEnd_3829211 := by
    simpa [prefixWord, tailWord_3829211, baseEnd_3829211] using wordTrace_append hprefix tailTrace_3829211
  have hstable : (prefixWord ++ tailWord_3829211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829211).length < 2 ^ (prefixWord ++ tailWord_3829211).sum := by decide
  have hdescent : baseEnd_3829211 < baseStart_3829211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829228 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 2, 3, 2]
def baseStart_3829228 : Nat := 118140960795 + 3829228 * 2 ^ 59
def prefixEnd_3829228 : Nat := 4983230072969 + 3 ^ 40 * 3829228 * 2
def baseEnd_3829228 : Nat := 1966234499654849361539707

theorem tailTrace_3829228 : CollatzResearch.WordTrace tailWord_3829228 prefixEnd_3829228 1966234499654849361539707 := by
  unfold tailWord_3829228
  simp only [CollatzResearch.WordTrace]
  refine ⟨69831709485684205460748169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93108945980912273947664225 69831709485684205460748169)
  ·
    refine ⟨52373782114263154095561127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69831709485684205460748169 52373782114263154095561127)
    ·
      refine ⟨78560673171394731143341691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52373782114263154095561127 78560673171394731143341691)
      ·
        refine ⟨117841009757092096715012537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78560673171394731143341691 117841009757092096715012537)
        ·
          refine ⟨88380757317819072536259403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117841009757092096715012537 88380757317819072536259403)
          ·
            refine ⟨132571135976728608804389105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88380757317819072536259403 132571135976728608804389105)
            ·
              refine ⟨99428351982546456603291829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132571135976728608804389105 99428351982546456603291829)
              ·
                refine ⟨9321407998363730306558609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99428351982546456603291829 9321407998363730306558609)
                ·
                  refine ⟨6991055998772797729918957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9321407998363730306558609 6991055998772797729918957)
                  ·
                    refine ⟨2621645999539799148719609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6991055998772797729918957 2621645999539799148719609)
                    ·
                      refine ⟨1966234499654849361539707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621645999539799148719609 1966234499654849361539707)
                      ·
                        rfl

theorem cell23_3829228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 3, 2].length) (baseStart_3829228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829228 prefixEnd_3829228 := by exact prefixLift 3829228
  have htrace : WordTrace (prefixWord ++ tailWord_3829228) baseStart_3829228 baseEnd_3829228 := by
    simpa [prefixWord, tailWord_3829228, baseEnd_3829228] using wordTrace_append hprefix tailTrace_3829228
  have hstable : (prefixWord ++ tailWord_3829228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829228).length < 2 ^ (prefixWord ++ tailWord_3829228).sum := by decide
  have hdescent : baseEnd_3829228 < baseStart_3829228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829252 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3829252 : Nat := 118140960795 + 3829252 * 2 ^ 59
def prefixEnd_3829252 : Nat := 4983230072969 + 3 ^ 40 * 3829252 * 2
def baseEnd_3829252 : Nat := 1966246823190557267639597

theorem tailTrace_3829252 : CollatzResearch.WordTrace tailWord_3829252 prefixEnd_3829252 1966246823190557267639597 := by
  unfold tailWord_3829252
  simp only [CollatzResearch.WordTrace]
  refine ⟨69832147161640731510185005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93109529548854308680246673 69832147161640731510185005)
  ·
    refine ⟨26187055185615274316319377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69832147161640731510185005 26187055185615274316319377)
    ·
      refine ⟨19640291389211455737239533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26187055185615274316319377 19640291389211455737239533)
      ·
        refine ⟨7365109270954295901464825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19640291389211455737239533 7365109270954295901464825)
        ·
          refine ⟨5523831953215721926098619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7365109270954295901464825 5523831953215721926098619)
          ·
            refine ⟨8285747929823582889147929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5523831953215721926098619 8285747929823582889147929)
            ·
              refine ⟨6214310947367687166860947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8285747929823582889147929 6214310947367687166860947)
              ·
                refine ⟨9321466421051530750291421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6214310947367687166860947 9321466421051530750291421)
                ·
                  refine ⟨3495549907894324031359283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9321466421051530750291421 3495549907894324031359283)
                  ·
                    refine ⟨5243324861841486047038925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3495549907894324031359283 5243324861841486047038925)
                    ·
                      refine ⟨1966246823190557267639597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5243324861841486047038925 1966246823190557267639597)
                      ·
                        rfl

theorem cell23_3829252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3829252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829252 prefixEnd_3829252 := by exact prefixLift 3829252
  have htrace : WordTrace (prefixWord ++ tailWord_3829252) baseStart_3829252 baseEnd_3829252 := by
    simpa [prefixWord, tailWord_3829252, baseEnd_3829252] using wordTrace_append hprefix tailTrace_3829252
  have hstable : (prefixWord ++ tailWord_3829252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829252).length < 2 ^ (prefixWord ++ tailWord_3829252).sum := by decide
  have hdescent : baseEnd_3829252 < baseStart_3829252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829281 : List Nat := [1, 2, 3, 2, 2, 3, 1, 9]
def baseStart_3829281 : Nat := 118140960795 + 3829281 * 2 ^ 59
def prefixEnd_3829281 : Nat := 4983230072969 + 3 ^ 40 * 3829281 * 2
def baseEnd_3829281 : Nat := 72824507930723616821369

theorem tailTrace_3829281 : CollatzResearch.WordTrace tailWord_3829281 prefixEnd_3829281 72824507930723616821369 := by
  unfold tailWord_3829281
  simp only [CollatzResearch.WordTrace]
  refine ⟨139665352040176400973175697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93110234693450933982117131 139665352040176400973175697)
  ·
    refine ⟨104749014030132300729881773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139665352040176400973175697 104749014030132300729881773)
    ·
      refine ⟨39280880261299612773705665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104749014030132300729881773 39280880261299612773705665)
      ·
        refine ⟨29460660195974709580279249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39280880261299612773705665 29460660195974709580279249)
        ·
          refine ⟨22095495146981032185209437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29460660195974709580279249 22095495146981032185209437)
          ·
            refine ⟨8285810680117887069453539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22095495146981032185209437 8285810680117887069453539)
            ·
              refine ⟨12428716020176830604180309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8285810680117887069453539 12428716020176830604180309)
              ·
                refine ⟨72824507930723616821369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12428716020176830604180309 72824507930723616821369)
                ·
                  rfl

theorem cell23_3829281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 9].length) (baseStart_3829281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829281 prefixEnd_3829281 := by exact prefixLift 3829281
  have htrace : WordTrace (prefixWord ++ tailWord_3829281) baseStart_3829281 baseEnd_3829281 := by
    simpa [prefixWord, tailWord_3829281, baseEnd_3829281] using wordTrace_append hprefix tailTrace_3829281
  have hstable : (prefixWord ++ tailWord_3829281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829281).length < 2 ^ (prefixWord ++ tailWord_3829281).sum := by decide
  have hdescent : baseEnd_3829281 < baseStart_3829281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829309 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 3, 2, 2]
def baseStart_3829309 : Nat := 118140960795 + 3829309 * 2 ^ 59
def prefixEnd_3829309 : Nat := 4983230072969 + 3 ^ 40 * 3829309 * 2
def baseEnd_3829309 : Nat := 1966276091587863544626835

theorem tailTrace_3829309 : CollatzResearch.WordTrace tailWord_3829309 prefixEnd_3829309 1966276091587863544626835 := by
  unfold tailWord_3829309
  simp only [CollatzResearch.WordTrace]
  refine ⟨139666373284074961755194981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93110915522716641170129987 139666373284074961755194981)
  ·
    refine ⟨26187444990764055329099059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139666373284074961755194981 26187444990764055329099059)
    ·
      refine ⟨39281167486146082993648589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26187444990764055329099059 39281167486146082993648589)
      ·
        refine ⟨14730437807304781122618221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39281167486146082993648589 14730437807304781122618221)
        ·
          refine ⟨5523914177739292920981833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14730437807304781122618221 5523914177739292920981833)
          ·
            refine ⟨4142935633304469690736375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5523914177739292920981833 4142935633304469690736375)
            ·
              refine ⟨6214403449956704536104563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4142935633304469690736375 6214403449956704536104563)
              ·
                refine ⟨9321605174935056804156845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6214403449956704536104563 9321605174935056804156845)
                ·
                  refine ⟨3495601940600646301558817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9321605174935056804156845 3495601940600646301558817)
                  ·
                    refine ⟨2621701455450484726169113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3495601940600646301558817 2621701455450484726169113)
                    ·
                      refine ⟨1966276091587863544626835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621701455450484726169113 1966276091587863544626835)
                      ·
                        rfl

theorem cell23_3829309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_3829309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829309 prefixEnd_3829309 := by exact prefixLift 3829309
  have htrace : WordTrace (prefixWord ++ tailWord_3829309) baseStart_3829309 baseEnd_3829309 := by
    simpa [prefixWord, tailWord_3829309, baseEnd_3829309] using wordTrace_append hprefix tailTrace_3829309
  have hstable : (prefixWord ++ tailWord_3829309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829309).length < 2 ^ (prefixWord ++ tailWord_3829309).sum := by decide
  have hdescent : baseEnd_3829309 < baseStart_3829309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829319 : List Nat := [1, 1, 4, 1, 6, 1, 2, 1, 2, 4]
def baseStart_3829319 : Nat := 118140960795 + 3829319 * 2 ^ 59
def prefixEnd_3829319 : Nat := 4983230072969 + 3 ^ 40 * 3829319 * 2
def baseEnd_3829319 : Nat := 655427075464802835167263

theorem tailTrace_3829319 : CollatzResearch.WordTrace tailWord_3829319 prefixEnd_3829319 655427075464802835167263 := by
  unfold tailWord_3829319
  simp only [CollatzResearch.WordTrace]
  refine ⟨139666738014038733463059011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93111158676025822308706007 139666738014038733463059011)
  ·
    refine ⟨209500107021058100194588517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139666738014038733463059011 209500107021058100194588517)
    ·
      refine ⟨39281270066448393786485347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209500107021058100194588517 39281270066448393786485347)
      ·
        refine ⟨58921905099672590679728021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39281270066448393786485347 58921905099672590679728021)
        ·
          refine ⟨2761964301547152688112251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58921905099672590679728021 2761964301547152688112251)
          ·
            refine ⟨4142946452320729032168377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761964301547152688112251 4142946452320729032168377)
            ·
              refine ⟨3107209839240546774126283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142946452320729032168377 3107209839240546774126283)
              ·
                refine ⟨4660814758860820161189425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107209839240546774126283 4660814758860820161189425)
                ·
                  refine ⟨3495611069145615120892069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4660814758860820161189425 3495611069145615120892069)
                  ·
                    refine ⟨655427075464802835167263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3495611069145615120892069 655427075464802835167263)
                    ·
                      rfl

theorem cell23_3829319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_3829319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829319 prefixEnd_3829319 := by exact prefixLift 3829319
  have htrace : WordTrace (prefixWord ++ tailWord_3829319) baseStart_3829319 baseEnd_3829319 := by
    simpa [prefixWord, tailWord_3829319, baseEnd_3829319] using wordTrace_append hprefix tailTrace_3829319
  have hstable : (prefixWord ++ tailWord_3829319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829319).length < 2 ^ (prefixWord ++ tailWord_3829319).sum := by decide
  have hdescent : baseEnd_3829319 < baseStart_3829319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829335 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 3, 3, 2]
def baseStart_3829335 : Nat := 118140960795 + 3829335 * 2 ^ 59
def prefixEnd_3829335 : Nat := 4983230072969 + 3 ^ 40 * 3829335 * 2
def baseEnd_3829335 : Nat := 1966289442084880442901715

theorem tailTrace_3829335 : CollatzResearch.WordTrace tailWord_3829335 prefixEnd_3829335 1966289442084880442901715 := by
  unfold tailWord_3829335
  simp only [CollatzResearch.WordTrace]
  refine ⟨139667321581980768195641459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93111547721320512130427639 139667321581980768195641459)
  ·
    refine ⟨209500982372971152293462189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139667321581980768195641459 209500982372971152293462189)
    ·
      refine ⟨78562868389864182110048321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209500982372971152293462189 78562868389864182110048321)
      ·
        refine ⟨58922151292398136582536241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78562868389864182110048321 58922151292398136582536241)
        ·
          refine ⟨44191613469298602436902181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58922151292398136582536241 44191613469298602436902181)
          ·
            refine ⟨8285927525493487956919159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44191613469298602436902181 8285927525493487956919159)
            ·
              refine ⟨12428891288240231935378739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8285927525493487956919159 12428891288240231935378739)
              ·
                refine ⟨18643336932360347903068109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12428891288240231935378739 18643336932360347903068109)
                ·
                  refine ⟨6991251349635130463650541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18643336932360347903068109 6991251349635130463650541)
                  ·
                    refine ⟨2621719256113173923868953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6991251349635130463650541 2621719256113173923868953)
                    ·
                      refine ⟨1966289442084880442901715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621719256113173923868953 1966289442084880442901715)
                      ·
                        rfl

theorem cell23_3829335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_3829335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829335 prefixEnd_3829335 := by exact prefixLift 3829335
  have htrace : WordTrace (prefixWord ++ tailWord_3829335) baseStart_3829335 baseEnd_3829335 := by
    simpa [prefixWord, tailWord_3829335, baseEnd_3829335] using wordTrace_append hprefix tailTrace_3829335
  have hstable : (prefixWord ++ tailWord_3829335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829335).length < 2 ^ (prefixWord ++ tailWord_3829335).sum := by decide
  have hdescent : baseEnd_3829335 < baseStart_3829335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829361 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_3829361 : Nat := 118140960795 + 3829361 * 2 ^ 59
def prefixEnd_3829361 : Nat := 4983230072969 + 3 ^ 40 * 3829361 * 2
def baseEnd_3829361 : Nat := 1966302792581897341176595

theorem tailTrace_3829361 : CollatzResearch.WordTrace tailWord_3829361 prefixEnd_3829361 1966302792581897341176595 := by
  unfold tailWord_3829361
  simp only [CollatzResearch.WordTrace]
  refine ⟨139668269879886574636087937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93112179919924383090725291 139668269879886574636087937)
  ·
    refine ⟨104751202409914930977065953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139668269879886574636087937 104751202409914930977065953)
    ·
      refine ⟨78563401807436198232799465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104751202409914930977065953 78563401807436198232799465)
      ·
        refine ⟨58922551355577148674599599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78563401807436198232799465 58922551355577148674599599)
        ·
          refine ⟨88383827033365723011899399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58922551355577148674599599 88383827033365723011899399)
          ·
            refine ⟨132575740550048584517849099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88383827033365723011899399 132575740550048584517849099)
            ·
              refine ⟨198863610825072876776773649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132575740550048584517849099 198863610825072876776773649)
              ·
                refine ⟨149147708118804657582580237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198863610825072876776773649 149147708118804657582580237)
                ·
                  refine ⟨55930390544551746593467589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149147708118804657582580237 55930390544551746593467589)
                  ·
                    refine ⟨10486948227103452486275173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55930390544551746593467589 10486948227103452486275173)
                    ·
                      refine ⟨1966302792581897341176595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10486948227103452486275173 1966302792581897341176595)
                      ·
                        rfl

theorem cell23_3829361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_3829361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829361 prefixEnd_3829361 := by exact prefixLift 3829361
  have htrace : WordTrace (prefixWord ++ tailWord_3829361) baseStart_3829361 baseEnd_3829361 := by
    simpa [prefixWord, tailWord_3829361, baseEnd_3829361] using wordTrace_append hprefix tailTrace_3829361
  have hstable : (prefixWord ++ tailWord_3829361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829361).length < 2 ^ (prefixWord ++ tailWord_3829361).sum := by decide
  have hdescent : baseEnd_3829361 < baseStart_3829361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829371 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 7]
def baseStart_3829371 : Nat := 118140960795 + 3829371 * 2 ^ 59
def prefixEnd_3829371 : Nat := 4983230072969 + 3 ^ 40 * 3829371 * 2
def baseEnd_3829371 : Nat := 218478658598715811339061

theorem tailTrace_3829371 : CollatzResearch.WordTrace tailWord_3829371 prefixEnd_3829371 218478658598715811339061 := by
  unfold tailWord_3829371
  simp only [CollatzResearch.WordTrace]
  refine ⟨139668634609850346343951967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93112423073233564229301311 139668634609850346343951967)
  ·
    refine ⟨209502951914775519515927951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139668634609850346343951967 209502951914775519515927951)
    ·
      refine ⟨314254427872163279273891927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209502951914775519515927951 314254427872163279273891927)
      ·
        refine ⟨471381641808244918910837891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314254427872163279273891927 471381641808244918910837891)
        ·
          refine ⟨707072462712367378366256837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471381641808244918910837891 707072462712367378366256837)
          ·
            refine ⟨132576086758568883443673157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 707072462712367378366256837 132576086758568883443673157)
            ·
              refine ⟨24858016267231665645688717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132576086758568883443673157 24858016267231665645688717)
              ·
                refine ⟨9321756100211874617133269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24858016267231665645688717 9321756100211874617133269)
                ·
                  refine ⟨218478658598715811339061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9321756100211874617133269 218478658598715811339061)
                  ·
                    rfl

theorem cell23_3829371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 7].length) (baseStart_3829371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829371 prefixEnd_3829371 := by exact prefixLift 3829371
  have htrace : WordTrace (prefixWord ++ tailWord_3829371) baseStart_3829371 baseEnd_3829371 := by
    simpa [prefixWord, tailWord_3829371, baseEnd_3829371] using wordTrace_append hprefix tailTrace_3829371
  have hstable : (prefixWord ++ tailWord_3829371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829371).length < 2 ^ (prefixWord ++ tailWord_3829371).sum := by decide
  have hdescent : baseEnd_3829371 < baseStart_3829371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829422 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 7]
def baseStart_3829422 : Nat := 118140960795 + 3829422 * 2 ^ 59
def prefixEnd_3829422 : Nat := 4983230072969 + 3 ^ 40 * 3829422 * 2
def baseEnd_3829422 : Nat := 218481568322424622501535

theorem tailTrace_3829422 : CollatzResearch.WordTrace tailWord_3829422 prefixEnd_3829422 218481568322424622501535 := by
  unfold tailWord_3829422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17458811841583197756757315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93113663155110388036039013 17458811841583197756757315)
  ·
    refine ⟨26188217762374796635135973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17458811841583197756757315 26188217762374796635135973)
    ·
      refine ⟨4910290830445274369087995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26188217762374796635135973 4910290830445274369087995)
      ·
        refine ⟨7365436245667911553631993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4910290830445274369087995 7365436245667911553631993)
        ·
          refine ⟨5524077184250933665223995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7365436245667911553631993 5524077184250933665223995)
          ·
            refine ⟨8286115776376400497835993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5524077184250933665223995 8286115776376400497835993)
            ·
              refine ⟨6214586832282300373376995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8286115776376400497835993 6214586832282300373376995)
              ·
                refine ⟨9321880248423450560065493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6214586832282300373376995 9321880248423450560065493)
                ·
                  refine ⟨218481568322424622501535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9321880248423450560065493 218481568322424622501535)
                  ·
                    rfl

theorem cell23_3829422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_3829422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829422 prefixEnd_3829422 := by exact prefixLift 3829422
  have htrace : WordTrace (prefixWord ++ tailWord_3829422) baseStart_3829422 baseEnd_3829422 := by
    simpa [prefixWord, tailWord_3829422, baseEnd_3829422] using wordTrace_append hprefix tailTrace_3829422
  have hstable : (prefixWord ++ tailWord_3829422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829422).length < 2 ^ (prefixWord ++ tailWord_3829422).sum := by decide
  have hdescent : baseEnd_3829422 < baseStart_3829422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829482 : List Nat := [3, 1, 3, 1, 1, 1, 2, 6, 1, 4]
def baseStart_3829482 : Nat := 118140960795 + 3829482 * 2 ^ 59
def prefixEnd_3829482 : Nat := 4983230072969 + 3 ^ 40 * 3829482 * 2
def baseEnd_3829482 : Nat := 655454974580363789254513

theorem tailTrace_3829482 : CollatzResearch.WordTrace tailWord_3829482 prefixEnd_3829482 655454974580363789254513 := by
  unfold tailWord_3829482
  simp only [CollatzResearch.WordTrace]
  refine ⟨34918170778112053075310675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93115122074965474867495133 34918170778112053075310675)
  ·
    refine ⟨52377256167168079612966013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34918170778112053075310675 52377256167168079612966013)
    ·
      refine ⟨19641471062688029854862255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52377256167168079612966013 19641471062688029854862255)
      ·
        refine ⟨29462206594032044782293383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19641471062688029854862255 29462206594032044782293383)
        ·
          refine ⟨44193309891048067173440075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29462206594032044782293383 44193309891048067173440075)
          ·
            refine ⟨66289964836572100760160113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44193309891048067173440075 66289964836572100760160113)
            ·
              refine ⟨49717473627429075570120085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66289964836572100760160113 49717473627429075570120085)
              ·
                refine ⟨2330506576285737917349379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49717473627429075570120085 2330506576285737917349379)
                ·
                  refine ⟨3495759864428606876024069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330506576285737917349379 3495759864428606876024069)
                  ·
                    refine ⟨655454974580363789254513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3495759864428606876024069 655454974580363789254513)
                    ·
                      rfl

theorem cell23_3829482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_3829482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829482 prefixEnd_3829482 := by exact prefixLift 3829482
  have htrace : WordTrace (prefixWord ++ tailWord_3829482) baseStart_3829482 baseEnd_3829482 := by
    simpa [prefixWord, tailWord_3829482, baseEnd_3829482] using wordTrace_append hprefix tailTrace_3829482
  have hstable : (prefixWord ++ tailWord_3829482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829482).length < 2 ^ (prefixWord ++ tailWord_3829482).sum := by decide
  have hdescent : baseEnd_3829482 < baseStart_3829482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829488 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 3]
def baseStart_3829488 : Nat := 118140960795 + 3829488 * 2 ^ 59
def prefixEnd_3829488 : Nat := 4983230072969 + 3 ^ 40 * 3829488 * 2
def baseEnd_3829488 : Nat := 1966368004625018344288511

theorem tailTrace_3829488 : CollatzResearch.WordTrace tailWord_3829488 prefixEnd_3829488 1966368004625018344288511 := by
  unfold tailWord_3829488
  simp only [CollatzResearch.WordTrace]
  refine ⟨69836450975213237662980559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93115267966950983550640745 69836450975213237662980559)
  ·
    refine ⟨104754676462819856494470839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69836450975213237662980559 104754676462819856494470839)
    ·
      refine ⟨157132014694229784741706259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104754676462819856494470839 157132014694229784741706259)
      ·
        refine ⟨235698022041344677112559389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157132014694229784741706259 235698022041344677112559389)
        ·
          refine ⟨88386758265504253917209771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235698022041344677112559389 88386758265504253917209771)
          ·
            refine ⟨132580137398256380875814657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88386758265504253917209771 132580137398256380875814657)
            ·
              refine ⟨99435103048692285656860993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132580137398256380875814657 99435103048692285656860993)
              ·
                refine ⟨74576327286519214242645745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99435103048692285656860993 74576327286519214242645745)
                ·
                  refine ⟨55932245464889410681984309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74576327286519214242645745 55932245464889410681984309)
                  ·
                    refine ⟨5243648012333382251436029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55932245464889410681984309 5243648012333382251436029)
                    ·
                      refine ⟨1966368004625018344288511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5243648012333382251436029 1966368004625018344288511)
                      ·
                        rfl

theorem cell23_3829488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 3].length) (baseStart_3829488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829488 prefixEnd_3829488 := by exact prefixLift 3829488
  have htrace : WordTrace (prefixWord ++ tailWord_3829488) baseStart_3829488 baseEnd_3829488 := by
    simpa [prefixWord, tailWord_3829488, baseEnd_3829488] using wordTrace_append hprefix tailTrace_3829488
  have hstable : (prefixWord ++ tailWord_3829488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829488).length < 2 ^ (prefixWord ++ tailWord_3829488).sum := by decide
  have hdescent : baseEnd_3829488 < baseStart_3829488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829495 : List Nat := [1, 1, 3, 1, 1, 1, 8, 1, 6]
def baseStart_3829495 : Nat := 118140960795 + 3829495 * 2 ^ 59
def prefixEnd_3829495 : Nat := 4983230072969 + 3 ^ 40 * 3829495 * 2
def baseEnd_3829495 : Nat := 218485733221066646322331

theorem tailTrace_3829495 : CollatzResearch.WordTrace tailWord_3829495 prefixEnd_3829495 218485733221066646322331 := by
  unfold tailWord_3829495
  simp only [CollatzResearch.WordTrace]
  refine ⟨139673157261401115521465939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93115438174267410347643959 139673157261401115521465939)
  ·
    refine ⟨209509735892101673282198909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139673157261401115521465939 209509735892101673282198909)
    ·
      refine ⟨78566150959538127480824591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209509735892101673282198909 78566150959538127480824591)
      ·
        refine ⟨117849226439307191221236887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78566150959538127480824591 117849226439307191221236887)
        ·
          refine ⟨176773839658960786831855331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117849226439307191221236887 176773839658960786831855331)
          ·
            refine ⟨265160759488441180247782997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176773839658960786831855331 265160759488441180247782997)
            ·
              refine ⟨3107352650255170081028707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 265160759488441180247782997 3107352650255170081028707)
              ·
                refine ⟨4661028975382755121543061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107352650255170081028707 4661028975382755121543061)
                ·
                  refine ⟨218485733221066646322331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4661028975382755121543061 218485733221066646322331)
                  ·
                    rfl

theorem cell23_3829495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 6].length) (baseStart_3829495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829495 prefixEnd_3829495 := by exact prefixLift 3829495
  have htrace : WordTrace (prefixWord ++ tailWord_3829495) baseStart_3829495 baseEnd_3829495 := by
    simpa [prefixWord, tailWord_3829495, baseEnd_3829495] using wordTrace_append hprefix tailTrace_3829495
  have hstable : (prefixWord ++ tailWord_3829495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829495).length < 2 ^ (prefixWord ++ tailWord_3829495).sum := by decide
  have hdescent : baseEnd_3829495 < baseStart_3829495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829515 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 1, 5, 2]
def baseStart_3829515 : Nat := 118140960795 + 3829515 * 2 ^ 59
def prefixEnd_3829515 : Nat := 4983230072969 + 3 ^ 40 * 3829515 * 2
def baseEnd_3829515 : Nat := 1966381868602689738650887

theorem tailTrace_3829515 : CollatzResearch.WordTrace tailWord_3829515 prefixEnd_3829515 1966381868602689738650887 := by
  unfold tailWord_3829515
  simp only [CollatzResearch.WordTrace]
  refine ⟨139673886721328658937193999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93115924480885772624795999 139673886721328658937193999)
  ·
    refine ⟨209510830081992988405790999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139673886721328658937193999 209510830081992988405790999)
    ·
      refine ⟨314266245122989482608686499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209510830081992988405790999 314266245122989482608686499)
      ·
        refine ⟨471399367684484223913029749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314266245122989482608686499 471399367684484223913029749)
        ·
          refine ⟨44193690720420395991846539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 471399367684484223913029749 44193690720420395991846539)
          ·
            refine ⟨66290536080630593987769809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44193690720420395991846539 66290536080630593987769809)
            ·
              refine ⟨49717902060472945490827357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66290536080630593987769809 49717902060472945490827357)
              ·
                refine ⟨18644213272677354559060259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49717902060472945490827357 18644213272677354559060259)
                ·
                  refine ⟨27966319909016031838590389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18644213272677354559060259 27966319909016031838590389)
                  ·
                    refine ⟨2621842491470252984867849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27966319909016031838590389 2621842491470252984867849)
                    ·
                      refine ⟨1966381868602689738650887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621842491470252984867849 1966381868602689738650887)
                      ·
                        rfl

theorem cell23_3829515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 5, 2].length) (baseStart_3829515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829515 prefixEnd_3829515 := by exact prefixLift 3829515
  have htrace : WordTrace (prefixWord ++ tailWord_3829515) baseStart_3829515 baseEnd_3829515 := by
    simpa [prefixWord, tailWord_3829515, baseEnd_3829515] using wordTrace_append hprefix tailTrace_3829515
  have hstable : (prefixWord ++ tailWord_3829515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829515).length < 2 ^ (prefixWord ++ tailWord_3829515).sum := by decide
  have hdescent : baseEnd_3829515 < baseStart_3829515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829532 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_3829532 : Nat := 118140960795 + 3829532 * 2 ^ 59
def prefixEnd_3829532 : Nat := 4983230072969 + 3 ^ 40 * 3829532 * 2
def baseEnd_3829532 : Nat := 1966390597773816172138309

theorem tailTrace_3829532 : CollatzResearch.WordTrace tailWord_3829532 prefixEnd_3829532 1966390597773816172138309 := by
  unfold tailWord_3829532
  simp only [CollatzResearch.WordTrace]
  refine ⟨69837253381133535420281425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93116337841511380560375233 69837253381133535420281425)
  ·
    refine ⟨52377940035850151565211069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69837253381133535420281425 52377940035850151565211069)
    ·
      refine ⟨19641727513443806836954151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52377940035850151565211069 19641727513443806836954151)
      ·
        refine ⟨29462591270165710255431227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19641727513443806836954151 29462591270165710255431227)
        ·
          refine ⟨44193886905248565383146841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29462591270165710255431227 44193886905248565383146841)
          ·
            refine ⟨33145415178936424037360131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44193886905248565383146841 33145415178936424037360131)
            ·
              refine ⟨49718122768404636056040197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33145415178936424037360131 49718122768404636056040197)
              ·
                refine ⟨9322148019075869260507537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49718122768404636056040197 9322148019075869260507537)
                ·
                  refine ⟨6991611014306901945380653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9322148019075869260507537 6991611014306901945380653)
                  ·
                    refine ⟨2621854130365088229517745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6991611014306901945380653 2621854130365088229517745)
                    ·
                      refine ⟨1966390597773816172138309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621854130365088229517745 1966390597773816172138309)
                      ·
                        rfl

theorem cell23_3829532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_3829532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829532 prefixEnd_3829532 := by exact prefixLift 3829532
  have htrace : WordTrace (prefixWord ++ tailWord_3829532) baseStart_3829532 baseEnd_3829532 := by
    simpa [prefixWord, tailWord_3829532, baseEnd_3829532] using wordTrace_append hprefix tailTrace_3829532
  have hstable : (prefixWord ++ tailWord_3829532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829532).length < 2 ^ (prefixWord ++ tailWord_3829532).sum := by decide
  have hdescent : baseEnd_3829532 < baseStart_3829532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829566 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_3829566 : Nat := 118140960795 + 3829566 * 2 ^ 59
def prefixEnd_3829566 : Nat := 4983230072969 + 3 ^ 40 * 3829566 * 2
def baseEnd_3829566 : Nat := 1966408056116069039113153

theorem tailTrace_3829566 : CollatzResearch.WordTrace tailWord_3829566 prefixEnd_3829566 1966408056116069039113153 := by
  unfold tailWord_3829566
  simp only [CollatzResearch.WordTrace]
  refine ⟨17459468355517986830912569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93117164562762596431533701 17459468355517986830912569)
  ·
    refine ⟨13094601266638490123184427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17459468355517986830912569 13094601266638490123184427)
    ·
      refine ⟨19641901899957735184776641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13094601266638490123184427 19641901899957735184776641)
      ·
        refine ⟨14731426424968301388582481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19641901899957735184776641 14731426424968301388582481)
        ·
          refine ⟨11048569818726226041436861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14731426424968301388582481 11048569818726226041436861)
          ·
            refine ⟨4143213682022334765538823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11048569818726226041436861 4143213682022334765538823)
            ·
              refine ⟨6214820523033502148308235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143213682022334765538823 6214820523033502148308235)
              ·
                refine ⟨9322230784550253222462353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6214820523033502148308235 9322230784550253222462353)
                ·
                  refine ⟨6991673088412689916846765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9322230784550253222462353 6991673088412689916846765)
                  ·
                    refine ⟨2621877408154758718817537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6991673088412689916846765 2621877408154758718817537)
                    ·
                      refine ⟨1966408056116069039113153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621877408154758718817537 1966408056116069039113153)
                      ·
                        rfl

theorem cell23_3829566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_3829566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829566 prefixEnd_3829566 := by exact prefixLift 3829566
  have htrace : WordTrace (prefixWord ++ tailWord_3829566) baseStart_3829566 baseEnd_3829566 := by
    simpa [prefixWord, tailWord_3829566, baseEnd_3829566] using wordTrace_append hprefix tailTrace_3829566
  have hstable : (prefixWord ++ tailWord_3829566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829566).length < 2 ^ (prefixWord ++ tailWord_3829566).sum := by decide
  have hdescent : baseEnd_3829566 < baseStart_3829566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829575 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_3829575 : Nat := 118140960795 + 3829575 * 2 ^ 59
def prefixEnd_3829575 : Nat := 4983230072969 + 3 ^ 40 * 3829575 * 2
def baseEnd_3829575 : Nat := 1966412677441959503900611

theorem tailTrace_3829575 : CollatzResearch.WordTrace tailWord_3829575 prefixEnd_3829575 1966412677441959503900611 := by
  unfold tailWord_3829575
  simp only [CollatzResearch.WordTrace]
  refine ⟨139676075101111289184378179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93117383400740859456252119 139676075101111289184378179)
  ·
    refine ⟨209514112651666933776567269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139676075101111289184378179 209514112651666933776567269)
    ·
      refine ⟨39283896122187550083106363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209514112651666933776567269 39283896122187550083106363)
      ·
        refine ⟨58925844183281325124659545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39283896122187550083106363 58925844183281325124659545)
        ·
          refine ⟨44194383137460993843494659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58925844183281325124659545 44194383137460993843494659)
          ·
            refine ⟨66291574706191490765241989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44194383137460993843494659 66291574706191490765241989)
            ·
              refine ⟨12429670257410904518482873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66291574706191490765241989 12429670257410904518482873)
              ·
                refine ⟨9322252693058178388862155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12429670257410904518482873 9322252693058178388862155)
                ·
                  refine ⟨13983379039587267583293233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9322252693058178388862155 13983379039587267583293233)
                  ·
                    refine ⟨10487534279690450687469925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13983379039587267583293233 10487534279690450687469925)
                    ·
                      refine ⟨1966412677441959503900611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10487534279690450687469925 1966412677441959503900611)
                      ·
                        rfl

theorem cell23_3829575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_3829575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829575 prefixEnd_3829575 := by exact prefixLift 3829575
  have htrace : WordTrace (prefixWord ++ tailWord_3829575) baseStart_3829575 baseEnd_3829575 := by
    simpa [prefixWord, tailWord_3829575, baseEnd_3829575] using wordTrace_append hprefix tailTrace_3829575
  have hstable : (prefixWord ++ tailWord_3829575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829575).length < 2 ^ (prefixWord ++ tailWord_3829575).sum := by decide
  have hdescent : baseEnd_3829575 < baseStart_3829575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829589 : List Nat := [1, 3, 2, 2, 2, 4, 1, 2, 2, 4]
def baseStart_3829589 : Nat := 118140960795 + 3829589 * 2 ^ 59
def prefixEnd_3829589 : Nat := 4983230072969 + 3 ^ 40 * 3829589 * 2
def baseEnd_3829589 : Nat := 655473288723707483041849

theorem tailTrace_3829589 : CollatzResearch.WordTrace tailWord_3829589 prefixEnd_3829589 655473288723707483041849 := by
  unfold tailWord_3829589
  simp only [CollatzResearch.WordTrace]
  refine ⟨139676585723060569575387821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93117723815373713050258547 139676585723060569575387821)
  ·
    refine ⟨52378719646147713590770433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139676585723060569575387821 52378719646147713590770433)
    ·
      refine ⟨39284039734610785193077825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52378719646147713590770433 39284039734610785193077825)
      ·
        refine ⟨29463029800958088894808369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39284039734610785193077825 29463029800958088894808369)
        ·
          refine ⟨22097272350718566671106277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29463029800958088894808369 22097272350718566671106277)
          ·
            refine ⟨4143238565759731250832427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22097272350718566671106277 4143238565759731250832427)
            ·
              refine ⟨6214857848639596876248641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143238565759731250832427 6214857848639596876248641)
              ·
                refine ⟨4661143386479697657186481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6214857848639596876248641 4661143386479697657186481)
                ·
                  refine ⟨3495857539859773242889861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4661143386479697657186481 3495857539859773242889861)
                  ·
                    refine ⟨655473288723707483041849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3495857539859773242889861 655473288723707483041849)
                    ·
                      rfl

theorem cell23_3829589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_3829589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829589 prefixEnd_3829589 := by exact prefixLift 3829589
  have htrace : WordTrace (prefixWord ++ tailWord_3829589) baseStart_3829589 baseEnd_3829589 := by
    simpa [prefixWord, tailWord_3829589, baseEnd_3829589] using wordTrace_append hprefix tailTrace_3829589
  have hstable : (prefixWord ++ tailWord_3829589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829589).length < 2 ^ (prefixWord ++ tailWord_3829589).sum := by decide
  have hdescent : baseEnd_3829589 < baseStart_3829589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829612 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 3]
def baseStart_3829612 : Nat := 118140960795 + 3829612 * 2 ^ 59
def prefixEnd_3829612 : Nat := 4983230072969 + 3 ^ 40 * 3829612 * 2
def baseEnd_3829612 : Nat := 1966431676226175859137941

theorem tailTrace_3829612 : CollatzResearch.WordTrace tailWord_3829612 prefixEnd_3829612 1966431676226175859137941 := by
  unfold tailWord_3829612
  simp only [CollatzResearch.WordTrace]
  refine ⟨69838712300988622251737545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93118283067984829668983393 69838712300988622251737545)
  ·
    refine ⟨52379034225741466688803159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69838712300988622251737545 52379034225741466688803159)
    ·
      refine ⟨78568551338612200033204739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52379034225741466688803159 78568551338612200033204739)
      ·
        refine ⟨117852827007918300049807109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78568551338612200033204739 117852827007918300049807109)
        ·
          refine ⟨22097405063984681259338833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117852827007918300049807109 22097405063984681259338833)
          ·
            refine ⟨16573053797988510944504125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22097405063984681259338833 16573053797988510944504125)
            ·
              refine ⟨6214895174245691604189047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16573053797988510944504125 6214895174245691604189047)
              ·
                refine ⟨9322342761368537406283571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6214895174245691604189047 9322342761368537406283571)
                ·
                  refine ⟨13983514142052806109425357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9322342761368537406283571 13983514142052806109425357)
                  ·
                    refine ⟨5243817803269802291034509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13983514142052806109425357 5243817803269802291034509)
                    ·
                      refine ⟨1966431676226175859137941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5243817803269802291034509 1966431676226175859137941)
                      ·
                        rfl

theorem cell23_3829612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_3829612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829612 prefixEnd_3829612 := by exact prefixLift 3829612
  have htrace : WordTrace (prefixWord ++ tailWord_3829612) baseStart_3829612 baseEnd_3829612 := by
    simpa [prefixWord, tailWord_3829612, baseEnd_3829612] using wordTrace_append hprefix tailTrace_3829612
  have hstable : (prefixWord ++ tailWord_3829612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829612).length < 2 ^ (prefixWord ++ tailWord_3829612).sum := by decide
  have hdescent : baseEnd_3829612 < baseStart_3829612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829630 : List Nat := [4, 2, 3, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3829630 : Nat := 118140960795 + 3829630 * 2 ^ 59
def prefixEnd_3829630 : Nat := 4983230072969 + 3 ^ 40 * 3829630 * 2
def baseEnd_3829630 : Nat := 1966440918877956788712859

theorem tailTrace_3829630 : CollatzResearch.WordTrace tailWord_3829630 prefixEnd_3829630 1966440918877956788712859 := by
  unfold tailWord_3829630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17459760139489004197203793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93118720743941355718420229 17459760139489004197203793)
  ·
    refine ⟨13094820104616753147902845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17459760139489004197203793 13094820104616753147902845)
    ·
      refine ⟨4910557539231282430463567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13094820104616753147902845 4910557539231282430463567)
      ·
        refine ⟨7365836308846923645695351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4910557539231282430463567 7365836308846923645695351)
        ·
          refine ⟨11048754463270385468543027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7365836308846923645695351 11048754463270385468543027)
          ·
            refine ⟨16573131694905578202814541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11048754463270385468543027 16573131694905578202814541)
            ·
              refine ⟨6214924385589591826055453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16573131694905578202814541 6214924385589591826055453)
              ·
                refine ⟨2330596644596096934770795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6214924385589591826055453 2330596644596096934770795)
                ·
                  refine ⟨3495894966894145402156193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330596644596096934770795 3495894966894145402156193)
                  ·
                    refine ⟨2621921225170609051617145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3495894966894145402156193 2621921225170609051617145)
                    ·
                      refine ⟨1966440918877956788712859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621921225170609051617145 1966440918877956788712859)
                      ·
                        rfl

theorem cell23_3829630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3829630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829630 prefixEnd_3829630 := by exact prefixLift 3829630
  have htrace : WordTrace (prefixWord ++ tailWord_3829630) baseStart_3829630 baseEnd_3829630 := by
    simpa [prefixWord, tailWord_3829630, baseEnd_3829630] using wordTrace_append hprefix tailTrace_3829630
  have hstable : (prefixWord ++ tailWord_3829630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829630).length < 2 ^ (prefixWord ++ tailWord_3829630).sum := by decide
  have hdescent : baseEnd_3829630 < baseStart_3829630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829663 : List Nat := [1, 1, 2, 5, 3, 2, 2, 1, 2, 1, 3]
def baseStart_3829663 : Nat := 118140960795 + 3829663 * 2 ^ 59
def prefixEnd_3829663 : Nat := 4983230072969 + 3 ^ 40 * 3829663 * 2
def baseEnd_3829663 : Nat := 1966457863739555159600207

theorem tailTrace_3829663 : CollatzResearch.WordTrace tailWord_3829663 prefixEnd_3829663 1966457863739555159600207 := by
  unfold tailWord_3829663
  simp only [CollatzResearch.WordTrace]
  refine ⟨139679284724792480213581643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93119523149861653475721095 139679284724792480213581643)
  ·
    refine ⟨209518927087188720320372465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139679284724792480213581643 209518927087188720320372465)
    ·
      refine ⟨157139195315391540240279349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209518927087188720320372465 157139195315391540240279349)
      ·
        refine ⟨14731799560817956897526189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157139195315391540240279349 14731799560817956897526189)
        ·
          refine ⟨5524424835306733836572321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14731799560817956897526189 5524424835306733836572321)
          ·
            refine ⟨4143318626480050377429241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5524424835306733836572321 4143318626480050377429241)
            ·
              refine ⟨3107488969860037783071931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4143318626480050377429241 3107488969860037783071931)
              ·
                refine ⟨4661233454790056674607897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107488969860037783071931 4661233454790056674607897)
                ·
                  refine ⟨3495925091092542505955923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4661233454790056674607897 3495925091092542505955923)
                  ·
                    refine ⟨5243887636638813758933885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3495925091092542505955923 5243887636638813758933885)
                    ·
                      refine ⟨1966457863739555159600207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5243887636638813758933885 1966457863739555159600207)
                      ·
                        rfl

theorem cell23_3829663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_3829663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829663 prefixEnd_3829663 := by exact prefixLift 3829663
  have htrace : WordTrace (prefixWord ++ tailWord_3829663) baseStart_3829663 baseEnd_3829663 := by
    simpa [prefixWord, tailWord_3829663, baseEnd_3829663] using wordTrace_append hprefix tailTrace_3829663
  have hstable : (prefixWord ++ tailWord_3829663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829663).length < 2 ^ (prefixWord ++ tailWord_3829663).sum := by decide
  have hdescent : baseEnd_3829663 < baseStart_3829663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829712 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 2, 5, 2]
def baseStart_3829712 : Nat := 118140960795 + 3829712 * 2 ^ 59
def prefixEnd_3829712 : Nat := 4983230072969 + 3 ^ 40 * 3829712 * 2
def baseEnd_3829712 : Nat := 1966483024291625467887481

theorem tailTrace_3829712 : CollatzResearch.WordTrace tailWord_3829712 prefixEnd_3829712 1966483024291625467887481 := by
  unfold tailWord_3829712
  simp only [CollatzResearch.WordTrace]
  refine ⟨69840535950807480791057695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93120714601076641054743593 69840535950807480791057695)
  ·
    refine ⟨104760803926211221186586543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69840535950807480791057695 104760803926211221186586543)
    ·
      refine ⟨157141205889316831779879815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104760803926211221186586543 157141205889316831779879815)
      ·
        refine ⟨235711808833975247669819723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157141205889316831779879815 235711808833975247669819723)
        ·
          refine ⟨353567713250962871504729585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235711808833975247669819723 353567713250962871504729585)
          ·
            refine ⟨265175784938222153628547189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353567713250962871504729585 265175784938222153628547189)
            ·
              refine ⟨24860229837958326902676299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265175784938222153628547189 24860229837958326902676299)
              ·
                refine ⟨37290344756937490354014449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24860229837958326902676299 37290344756937490354014449)
                ·
                  refine ⟨27967758567703117765510837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37290344756937490354014449 27967758567703117765510837)
                  ·
                    refine ⟨2621977365722167290516641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27967758567703117765510837 2621977365722167290516641)
                    ·
                      refine ⟨1966483024291625467887481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2621977365722167290516641 1966483024291625467887481)
                      ·
                        rfl

theorem cell23_3829712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 5, 2].length) (baseStart_3829712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829712 prefixEnd_3829712 := by exact prefixLift 3829712
  have htrace : WordTrace (prefixWord ++ tailWord_3829712) baseStart_3829712 baseEnd_3829712 := by
    simpa [prefixWord, tailWord_3829712, baseEnd_3829712] using wordTrace_append hprefix tailTrace_3829712
  have hstable : (prefixWord ++ tailWord_3829712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829712).length < 2 ^ (prefixWord ++ tailWord_3829712).sum := by decide
  have hdescent : baseEnd_3829712 < baseStart_3829712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829755 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 6]
def baseStart_3829755 : Nat := 118140960795 + 3829755 * 2 ^ 59
def prefixEnd_3829755 : Nat := 4983230072969 + 3 ^ 40 * 3829755 * 2
def baseEnd_3829755 : Nat := 1966505103959768799649783

theorem tailTrace_3829755 : CollatzResearch.WordTrace tailWord_3829755 prefixEnd_3829755 1966505103959768799649783 := by
  unfold tailWord_3829755
  simp only [CollatzResearch.WordTrace]
  refine ⟨139682640240459179925930719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93121760160306119950620479 139682640240459179925930719)
  ·
    refine ⟨209523960360688769888896079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139682640240459179925930719 209523960360688769888896079)
    ·
      refine ⟨314285940541033154833344119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209523960360688769888896079 314285940541033154833344119)
      ·
        refine ⟨471428910811549732250016179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314285940541033154833344119 471428910811549732250016179)
        ·
          refine ⟨707143366217324598375024269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471428910811549732250016179 707143366217324598375024269)
          ·
            refine ⟨265178762331496724390634101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 707143366217324598375024269 265178762331496724390634101)
            ·
              refine ⟨24860508968577817911621947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265178762331496724390634101 24860508968577817911621947)
              ·
                refine ⟨37290763452866726867432921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24860508968577817911621947 37290763452866726867432921)
                ·
                  refine ⟨27968072589650045150574691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37290763452866726867432921 27968072589650045150574691)
                  ·
                    refine ⟨41952108884475067725862037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27968072589650045150574691 41952108884475067725862037)
                    ·
                      refine ⟨1966505103959768799649783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41952108884475067725862037 1966505103959768799649783)
                      ·
                        rfl

theorem cell23_3829755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_3829755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829755 prefixEnd_3829755 := by exact prefixLift 3829755
  have htrace : WordTrace (prefixWord ++ tailWord_3829755) baseStart_3829755 baseEnd_3829755 := by
    simpa [prefixWord, tailWord_3829755, baseEnd_3829755] using wordTrace_append hprefix tailTrace_3829755
  have hstable : (prefixWord ++ tailWord_3829755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829755).length < 2 ^ (prefixWord ++ tailWord_3829755).sum := by decide
  have hdescent : baseEnd_3829755 < baseStart_3829755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829785 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 6]
def baseStart_3829785 : Nat := 118140960795 + 3829785 * 2 ^ 59
def prefixEnd_3829785 : Nat := 4983230072969 + 3 ^ 40 * 3829785 * 2
def baseEnd_3829785 : Nat := 1966520508379403682274645

theorem tailTrace_3829785 : CollatzResearch.WordTrace tailWord_3829785 prefixEnd_3829785 1966520508379403682274645 := by
  unfold tailWord_3829785
  simp only [CollatzResearch.WordTrace]
  refine ⟨139683734430350495049522809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93122489620233663366348539 139683734430350495049522809)
  ·
    refine ⟨104762800822762871287142107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139683734430350495049522809 104762800822762871287142107)
    ·
      refine ⟨157144201234144306930713161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104762800822762871287142107 157144201234144306930713161)
      ·
        refine ⟨117858150925608230198034871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157144201234144306930713161 117858150925608230198034871)
        ·
          refine ⟨176787226388412345297052307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117858150925608230198034871 176787226388412345297052307)
          ·
            refine ⟨265180839582618517945578461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176787226388412345297052307 265180839582618517945578461)
            ·
              refine ⟨99442814843481944229591923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265180839582618517945578461 99442814843481944229591923)
              ·
                refine ⟨149164222265222916344387885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99442814843481944229591923 149164222265222916344387885)
                ·
                  refine ⟨55936583349458593629145457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149164222265222916344387885 55936583349458593629145457)
                  ·
                    refine ⟨41952437512093945221859093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55936583349458593629145457 41952437512093945221859093)
                    ·
                      refine ⟨1966520508379403682274645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41952437512093945221859093 1966520508379403682274645)
                      ·
                        rfl

theorem cell23_3829785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_3829785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829785 prefixEnd_3829785 := by exact prefixLift 3829785
  have htrace : WordTrace (prefixWord ++ tailWord_3829785) baseStart_3829785 baseEnd_3829785 := by
    simpa [prefixWord, tailWord_3829785, baseEnd_3829785] using wordTrace_append hprefix tailTrace_3829785
  have hstable : (prefixWord ++ tailWord_3829785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829785).length < 2 ^ (prefixWord ++ tailWord_3829785).sum := by decide
  have hdescent : baseEnd_3829785 < baseStart_3829785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829819 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 2, 3, 2]
def baseStart_3829819 : Nat := 118140960795 + 3829819 * 2 ^ 59
def prefixEnd_3829819 : Nat := 4983230072969 + 3 ^ 40 * 3829819 * 2
def baseEnd_3829819 : Nat := 1966537966721656549249489

theorem tailTrace_3829819 : CollatzResearch.WordTrace tailWord_3829819 prefixEnd_3829819 1966537966721656549249489 := by
  unfold tailWord_3829819
  simp only [CollatzResearch.WordTrace]
  refine ⟨139684974512227318856260511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93123316341484879237507007 139684974512227318856260511)
  ·
    refine ⟨209527461768340978284390767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139684974512227318856260511 209527461768340978284390767)
    ·
      refine ⟨314291192652511467426586151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209527461768340978284390767 314291192652511467426586151)
      ·
        refine ⟨471436788978767201139879227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314291192652511467426586151 471436788978767201139879227)
        ·
          refine ⟨707155183468150801709818841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471436788978767201139879227 707155183468150801709818841)
          ·
            refine ⟨530366387601113101282364131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707155183468150801709818841 530366387601113101282364131)
            ·
              refine ⟨795549581401669651923546197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530366387601113101282364131 795549581401669651923546197)
              ·
                refine ⟨9322846657050816233479057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 795549581401669651923546197 9322846657050816233479057)
                ·
                  refine ⟨6992134992788112175109293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9322846657050816233479057 6992134992788112175109293)
                  ·
                    refine ⟨2622050622295542065665985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6992134992788112175109293 2622050622295542065665985)
                    ·
                      refine ⟨1966537966721656549249489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2622050622295542065665985 1966537966721656549249489)
                      ·
                        rfl

theorem cell23_3829819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 3, 2].length) (baseStart_3829819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829819 prefixEnd_3829819 := by exact prefixLift 3829819
  have htrace : WordTrace (prefixWord ++ tailWord_3829819) baseStart_3829819 baseEnd_3829819 := by
    simpa [prefixWord, tailWord_3829819, baseEnd_3829819] using wordTrace_append hprefix tailTrace_3829819
  have hstable : (prefixWord ++ tailWord_3829819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829819).length < 2 ^ (prefixWord ++ tailWord_3829819).sum := by decide
  have hdescent : baseEnd_3829819 < baseStart_3829819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829853 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_3829853 : Nat := 118140960795 + 3829853 * 2 ^ 59
def prefixEnd_3829853 : Nat := 4983230072969 + 3 ^ 40 * 3829853 * 2
def baseEnd_3829853 : Nat := 1966555425063909416224333

theorem tailTrace_3829853 : CollatzResearch.WordTrace tailWord_3829853 prefixEnd_3829853 1966555425063909416224333 := by
  unfold tailWord_3829853
  simp only [CollatzResearch.WordTrace]
  refine ⟨139686214594104142662998213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93124143062736095108665475 139686214594104142662998213)
  ·
    refine ⟨26191165236394526749312165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139686214594104142662998213 26191165236394526749312165)
    ·
      refine ⟨4910843481823973765496031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26191165236394526749312165 4910843481823973765496031)
      ·
        refine ⟨7366265222735960648244047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4910843481823973765496031 7366265222735960648244047)
        ·
          refine ⟨11049397834103940972366071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7366265222735960648244047 11049397834103940972366071)
          ·
            refine ⟨16574096751155911458549107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11049397834103940972366071 16574096751155911458549107)
            ·
              refine ⟨24861145126733867187823661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16574096751155911458549107 24861145126733867187823661)
              ·
                refine ⟨9322929422525200195433873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24861145126733867187823661 9322929422525200195433873)
                ·
                  refine ⟨6992197066893900146575405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9322929422525200195433873 6992197066893900146575405)
                  ·
                    refine ⟨2622073900085212554965777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6992197066893900146575405 2622073900085212554965777)
                    ·
                      refine ⟨1966555425063909416224333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2622073900085212554965777 1966555425063909416224333)
                      ·
                        rfl

theorem cell23_3829853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_3829853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829853 prefixEnd_3829853 := by exact prefixLift 3829853
  have htrace : WordTrace (prefixWord ++ tailWord_3829853) baseStart_3829853 baseEnd_3829853 := by
    simpa [prefixWord, tailWord_3829853, baseEnd_3829853] using wordTrace_append hprefix tailTrace_3829853
  have hstable : (prefixWord ++ tailWord_3829853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829853).length < 2 ^ (prefixWord ++ tailWord_3829853).sum := by decide
  have hdescent : baseEnd_3829853 < baseStart_3829853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829896 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3829896 : Nat := 118140960795 + 3829896 * 2 ^ 59
def prefixEnd_3829896 : Nat := 4983230072969 + 3 ^ 40 * 3829896 * 2
def baseEnd_3829896 : Nat := 1966577504732052747986635

theorem tailTrace_3829896 : CollatzResearch.WordTrace tailWord_3829896 prefixEnd_3829896 1966577504732052747986635 := by
  unfold tailWord_3829896
  simp only [CollatzResearch.WordTrace]
  refine ⟨69843891466474180503406771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93125188621965574004542361 69843891466474180503406771)
  ·
    refine ⟨104765837199711270755110157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69843891466474180503406771 104765837199711270755110157)
    ·
      refine ⟨39287188949891726533166309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104765837199711270755110157 39287188949891726533166309)
      ·
        refine ⟨7366347928104698724968683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39287188949891726533166309 7366347928104698724968683)
        ·
          refine ⟨11049521892157048087453025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7366347928104698724968683 11049521892157048087453025)
          ·
            refine ⟨8287141419117786065589769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11049521892157048087453025 8287141419117786065589769)
            ·
              refine ⟨6215356064338339549192327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8287141419117786065589769 6215356064338339549192327)
              ·
                refine ⟨9323034096507509323788491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215356064338339549192327 9323034096507509323788491)
                ·
                  refine ⟨13984551144761263985682737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9323034096507509323788491 13984551144761263985682737)
                  ·
                    refine ⟨10488413358570947989262053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13984551144761263985682737 10488413358570947989262053)
                    ·
                      refine ⟨1966577504732052747986635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10488413358570947989262053 1966577504732052747986635)
                      ·
                        rfl

theorem cell23_3829896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3829896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829896 prefixEnd_3829896 := by exact prefixLift 3829896
  have htrace : WordTrace (prefixWord ++ tailWord_3829896) baseStart_3829896 baseEnd_3829896 := by
    simpa [prefixWord, tailWord_3829896, baseEnd_3829896] using wordTrace_append hprefix tailTrace_3829896
  have hstable : (prefixWord ++ tailWord_3829896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829896).length < 2 ^ (prefixWord ++ tailWord_3829896).sum := by decide
  have hdescent : baseEnd_3829896 < baseStart_3829896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829899 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 8, 1, 3]
def baseStart_3829899 : Nat := 118140960795 + 3829899 * 2 ^ 59
def prefixEnd_3829899 : Nat := 4983230072969 + 3 ^ 40 * 3829899 * 2
def baseEnd_3829899 : Nat := 1966579045174016236249121

theorem tailTrace_3829899 : CollatzResearch.WordTrace tailWord_3829899 prefixEnd_3829899 1966579045174016236249121 := by
  unfold tailWord_3829899
  simp only [CollatzResearch.WordTrace]
  refine ⟨139687892351937492519172751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93125261567958328346115167 139687892351937492519172751)
  ·
    refine ⟨209531838527906238778759127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139687892351937492519172751 209531838527906238778759127)
    ·
      refine ⟨314297757791859358168138691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209531838527906238778759127 314297757791859358168138691)
      ·
        refine ⟨471446636687789037252208037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314297757791859358168138691 471446636687789037252208037)
        ·
          refine ⟨88396244378960444484789007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471446636687789037252208037 88396244378960444484789007)
          ·
            refine ⟨132594366568440666727183511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88396244378960444484789007 132594366568440666727183511)
            ·
              refine ⟨198891549852661000090775267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132594366568440666727183511 198891549852661000090775267)
              ·
                refine ⟨298337324778991500136162901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198891549852661000090775267 298337324778991500136162901)
                ·
                  refine ⟨3496140524753806642220659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 298337324778991500136162901 3496140524753806642220659)
                  ·
                    refine ⟨5244210787130709963330989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3496140524753806642220659 5244210787130709963330989)
                    ·
                      refine ⟨1966579045174016236249121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5244210787130709963330989 1966579045174016236249121)
                      ·
                        rfl

theorem cell23_3829899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 1, 3].length) (baseStart_3829899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829899 prefixEnd_3829899 := by exact prefixLift 3829899
  have htrace : WordTrace (prefixWord ++ tailWord_3829899) baseStart_3829899 baseEnd_3829899 := by
    simpa [prefixWord, tailWord_3829899, baseEnd_3829899] using wordTrace_append hprefix tailTrace_3829899
  have hstable : (prefixWord ++ tailWord_3829899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829899).length < 2 ^ (prefixWord ++ tailWord_3829899).sum := by decide
  have hdescent : baseEnd_3829899 < baseStart_3829899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829916 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_3829916 : Nat := 118140960795 + 3829916 * 2 ^ 59
def prefixEnd_3829916 : Nat := 4983230072969 + 3 ^ 40 * 3829916 * 2
def baseEnd_3829916 : Nat := 1966587774345142669736543

theorem tailTrace_3829916 : CollatzResearch.WordTrace tailWord_3829916 prefixEnd_3829916 1966587774345142669736543 := by
  unfold tailWord_3829916
  simp only [CollatzResearch.WordTrace]
  refine ⟨69844256196437952211270801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93125674928583936281694401 69844256196437952211270801)
  ·
    refine ⟨52383192147328464158453101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69844256196437952211270801 52383192147328464158453101)
    ·
      refine ⟨19643697055248174059419913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52383192147328464158453101 19643697055248174059419913)
      ·
        refine ⟨14732772791436130544564935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19643697055248174059419913 14732772791436130544564935)
        ·
          refine ⟨22099159187154195816847403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14732772791436130544564935 22099159187154195816847403)
          ·
            refine ⟨33148738780731293725271105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22099159187154195816847403 33148738780731293725271105)
            ·
              refine ⟨24861554085548470293953329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33148738780731293725271105 24861554085548470293953329)
              ·
                refine ⟨18646165564161352720464997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24861554085548470293953329 18646165564161352720464997)
                ·
                  refine ⟨3496156043280253635087187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18646165564161352720464997 3496156043280253635087187)
                  ·
                    refine ⟨5244234064920380452630781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3496156043280253635087187 5244234064920380452630781)
                    ·
                      refine ⟨1966587774345142669736543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5244234064920380452630781 1966587774345142669736543)
                      ·
                        rfl

theorem cell23_3829916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_3829916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829916 prefixEnd_3829916 := by exact prefixLift 3829916
  have htrace : WordTrace (prefixWord ++ tailWord_3829916) baseStart_3829916 baseEnd_3829916 := by
    simpa [prefixWord, tailWord_3829916, baseEnd_3829916] using wordTrace_append hprefix tailTrace_3829916
  have hstable : (prefixWord ++ tailWord_3829916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829916).length < 2 ^ (prefixWord ++ tailWord_3829916).sum := by decide
  have hdescent : baseEnd_3829916 < baseStart_3829916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829933 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_3829933 : Nat := 118140960795 + 3829933 * 2 ^ 59
def prefixEnd_3829933 : Nat := 4983230072969 + 3 ^ 40 * 3829933 * 2
def baseEnd_3829933 : Nat := 1966596503516269103223965

theorem tailTrace_3829933 : CollatzResearch.WordTrace tailWord_3829933 prefixEnd_3829933 1966596503516269103223965 := by
  unfold tailWord_3829933
  simp only [CollatzResearch.WordTrace]
  refine ⟨139689132433814316325910453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93126088289209544217273635 139689132433814316325910453)
  ·
    refine ⟨13095856165670092155554105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139689132433814316325910453 13095856165670092155554105)
    ·
      refine ⟨9821892124252569116665579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13095856165670092155554105 9821892124252569116665579)
      ·
        refine ⟨14732838186378853674998369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9821892124252569116665579 14732838186378853674998369)
        ·
          refine ⟨11049628639784140256248777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14732838186378853674998369 11049628639784140256248777)
          ·
            refine ⟨8287221479838105192186583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11049628639784140256248777 8287221479838105192186583)
            ·
              refine ⟨12430832219757157788279875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8287221479838105192186583 12430832219757157788279875)
              ·
                refine ⟨18646248329635736682419813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12430832219757157788279875 18646248329635736682419813)
                ·
                  refine ⟨3496171561806700627953715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18646248329635736682419813 3496171561806700627953715)
                  ·
                    refine ⟨5244257342710050941930573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3496171561806700627953715 5244257342710050941930573)
                    ·
                      refine ⟨1966596503516269103223965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5244257342710050941930573 1966596503516269103223965)
                      ·
                        rfl

theorem cell23_3829933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_3829933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829933 prefixEnd_3829933 := by exact prefixLift 3829933
  have htrace : WordTrace (prefixWord ++ tailWord_3829933) baseStart_3829933 baseEnd_3829933 := by
    simpa [prefixWord, tailWord_3829933, baseEnd_3829933] using wordTrace_append hprefix tailTrace_3829933
  have hstable : (prefixWord ++ tailWord_3829933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829933).length < 2 ^ (prefixWord ++ tailWord_3829933).sum := by decide
  have hdescent : baseEnd_3829933 < baseStart_3829933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829950 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_3829950 : Nat := 118140960795 + 3829950 * 2 ^ 59
def prefixEnd_3829950 : Nat := 4983230072969 + 3 ^ 40 * 3829950 * 2
def baseEnd_3829950 : Nat := 1966605232687395536711387

theorem tailTrace_3829950 : CollatzResearch.WordTrace tailWord_3829950 prefixEnd_3829950 1966605232687395536711387 := by
  unfold tailWord_3829950
  simp only [CollatzResearch.WordTrace]
  refine ⟨17461219059344091028659913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93126501649835152152852869 17461219059344091028659913)
  ·
    refine ⟨13095914294508068271494935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17461219059344091028659913 13095914294508068271494935)
    ·
      refine ⟨19643871441762102407242403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13095914294508068271494935 19643871441762102407242403)
      ·
        refine ⟨29465807162643153610863605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19643871441762102407242403 29465807162643153610863605)
        ·
          refine ⟨2762419421497795651018463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29465807162643153610863605 2762419421497795651018463)
          ·
            refine ⟨4143629132246693476527695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762419421497795651018463 4143629132246693476527695)
            ·
              refine ⟨6215443698370040214791543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143629132246693476527695 6215443698370040214791543)
              ·
                refine ⟨9323165547555060322187315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215443698370040214791543 9323165547555060322187315)
                ·
                  refine ⟨13984748321332590483280973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9323165547555060322187315 13984748321332590483280973)
                  ·
                    refine ⟨5244280620499721431230365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13984748321332590483280973 5244280620499721431230365)
                    ·
                      refine ⟨1966605232687395536711387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5244280620499721431230365 1966605232687395536711387)
                      ·
                        rfl

theorem cell23_3829950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_3829950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3829950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3829950 prefixEnd_3829950 := by exact prefixLift 3829950
  have htrace : WordTrace (prefixWord ++ tailWord_3829950) baseStart_3829950 baseEnd_3829950 := by
    simpa [prefixWord, tailWord_3829950, baseEnd_3829950] using wordTrace_append hprefix tailTrace_3829950
  have hstable : (prefixWord ++ tailWord_3829950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829950).length < 2 ^ (prefixWord ++ tailWord_3829950).sum := by decide
  have hdescent : baseEnd_3829950 < baseStart_3829950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830006 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_3830006 : Nat := 118140960795 + 3830006 * 2 ^ 59
def prefixEnd_3830006 : Nat := 4983230072969 + 3 ^ 40 * 3830006 * 2
def baseEnd_3830006 : Nat := 1966633987604047317611129

theorem tailTrace_3830006 : CollatzResearch.WordTrace tailWord_3830006 prefixEnd_3830006 1966633987604047317611129 := by
  unfold tailWord_3830006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8730737185159365612082367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93127863308366566528878581 8730737185159365612082367)
  ·
    refine ⟨13096105777739048418123551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8730737185159365612082367 13096105777739048418123551)
    ·
      refine ⟨19644158666608572627185327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13096105777739048418123551 19644158666608572627185327)
      ·
        refine ⟨29466237999912858940777991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19644158666608572627185327 29466237999912858940777991)
        ·
          refine ⟨44199356999869288411166987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29466237999912858940777991 44199356999869288411166987)
          ·
            refine ⟨66299035499803932616750481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44199356999869288411166987 66299035499803932616750481)
            ·
              refine ⟨49724276624852949462562861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66299035499803932616750481 49724276624852949462562861)
              ·
                refine ⟨18646603734319856048461073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49724276624852949462562861 18646603734319856048461073)
                ·
                  refine ⟨13984952800739892036345805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18646603734319856048461073 13984952800739892036345805)
                  ·
                    refine ⟨5244357300277459513629677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13984952800739892036345805 5244357300277459513629677)
                    ·
                      refine ⟨1966633987604047317611129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5244357300277459513629677 1966633987604047317611129)
                      ·
                        rfl

theorem cell23_3830006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_3830006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830006 prefixEnd_3830006 := by exact prefixLift 3830006
  have htrace : WordTrace (prefixWord ++ tailWord_3830006) baseStart_3830006 baseEnd_3830006 := by
    simpa [prefixWord, tailWord_3830006, baseEnd_3830006] using wordTrace_append hprefix tailTrace_3830006
  have hstable : (prefixWord ++ tailWord_3830006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830006).length < 2 ^ (prefixWord ++ tailWord_3830006).sum := by decide
  have hdescent : baseEnd_3830006 < baseStart_3830006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830073 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 3, 4]
def baseStart_3830073 : Nat := 118140960795 + 3830073 * 2 ^ 59
def prefixEnd_3830073 : Nat := 4983230072969 + 3 ^ 40 * 3830073 * 2
def baseEnd_3830073 : Nat := 655556130269299518491107

theorem tailTrace_3830073 : CollatzResearch.WordTrace tailWord_3830073 prefixEnd_3830073 655556130269299518491107 := by
  unfold tailWord_3830073
  simp only [CollatzResearch.WordTrace]
  refine ⟨139694238653307120236006873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93129492435538080157337915 139694238653307120236006873)
  ·
    refine ⟨104770678989980340177005155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139694238653307120236006873 104770678989980340177005155)
    ·
      refine ⟨157156018484970510265507733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104770678989980340177005155 157156018484970510265507733)
      ·
        refine ⟨7366688366482992668695675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157156018484970510265507733 7366688366482992668695675)
        ·
          refine ⟨11050032549724489003043513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7366688366482992668695675 11050032549724489003043513)
          ·
            refine ⟨8287524412293366752282635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11050032549724489003043513 8287524412293366752282635)
            ·
              refine ⟨12431286618440050128423953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8287524412293366752282635 12431286618440050128423953)
              ·
                refine ⟨9323464963830037596317965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12431286618440050128423953 9323464963830037596317965)
                ·
                  refine ⟨3496299361436264098619237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9323464963830037596317965 3496299361436264098619237)
                  ·
                    refine ⟨655556130269299518491107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3496299361436264098619237 655556130269299518491107)
                    ·
                      rfl

theorem cell23_3830073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 4].length) (baseStart_3830073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830073 prefixEnd_3830073 := by exact prefixLift 3830073
  have htrace : WordTrace (prefixWord ++ tailWord_3830073) baseStart_3830073 baseEnd_3830073 := by
    simpa [prefixWord, tailWord_3830073, baseEnd_3830073] using wordTrace_append hprefix tailTrace_3830073
  have hstable : (prefixWord ++ tailWord_3830073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830073).length < 2 ^ (prefixWord ++ tailWord_3830073).sum := by decide
  have hdescent : baseEnd_3830073 < baseStart_3830073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830099 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 5, 5]
def baseStart_3830099 : Nat := 118140960795 + 3830099 * 2 ^ 59
def prefixEnd_3830099 : Nat := 4983230072969 + 3 ^ 40 * 3830099 * 2
def baseEnd_3830099 : Nat := 655560580434971817916067

theorem tailTrace_3830099 : CollatzResearch.WordTrace tailWord_3830099 prefixEnd_3830099 655560580434971817916067 := by
  unfold tailWord_3830099
  simp only [CollatzResearch.WordTrace]
  refine ⟨139695186951212926676453351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93130124634141951117635567 139695186951212926676453351)
  ·
    refine ⟨209542780426819390014680027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139695186951212926676453351 209542780426819390014680027)
    ·
      refine ⟨314314170640229085022020041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209542780426819390014680027 314314170640229085022020041)
      ·
        refine ⟨235735627980171813766515031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314314170640229085022020041 235735627980171813766515031)
        ·
          refine ⟨353603441970257720649772547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235735627980171813766515031 353603441970257720649772547)
          ·
            refine ⟨530405162955386580974658821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353603441970257720649772547 530405162955386580974658821)
            ·
              refine ⟨99450968054134983932748529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530405162955386580974658821 99450968054134983932748529)
              ·
                refine ⟨74588226040601237949561397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99450968054134983932748529 74588226040601237949561397)
                ·
                  refine ⟨6992646191306366057771381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74588226040601237949561397 6992646191306366057771381)
                  ·
                    refine ⟨655560580434971817916067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6992646191306366057771381 655560580434971817916067)
                    ·
                      rfl

theorem cell23_3830099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 5].length) (baseStart_3830099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830099 prefixEnd_3830099 := by exact prefixLift 3830099
  have htrace : WordTrace (prefixWord ++ tailWord_3830099) baseStart_3830099 baseEnd_3830099 := by
    simpa [prefixWord, tailWord_3830099, baseEnd_3830099] using wordTrace_append hprefix tailTrace_3830099
  have hstable : (prefixWord ++ tailWord_3830099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830099).length < 2 ^ (prefixWord ++ tailWord_3830099).sum := by decide
  have hdescent : baseEnd_3830099 < baseStart_3830099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830133 : List Nat := [1, 3, 4, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3830133 : Nat := 118140960795 + 3830133 * 2 ^ 59
def prefixEnd_3830133 : Nat := 4983230072969 + 3 ^ 40 * 3830133 * 2
def baseEnd_3830133 : Nat := 655566399882389440241015

theorem tailTrace_3830133 : CollatzResearch.WordTrace tailWord_3830133 prefixEnd_3830133 655566399882389440241015 := by
  unfold tailWord_3830133
  simp only [CollatzResearch.WordTrace]
  refine ⟨139696427033089750483191053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93130951355393166988794035 139696427033089750483191053)
  ·
    refine ⟨52386160137408656431196645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139696427033089750483191053 52386160137408656431196645)
    ·
      refine ⟨9822405025764123080849371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52386160137408656431196645 9822405025764123080849371)
      ·
        refine ⟨14733607538646184621274057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9822405025764123080849371 14733607538646184621274057)
        ·
          refine ⟨11050205653984638465955543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14733607538646184621274057 11050205653984638465955543)
          ·
            refine ⟨16575308480976957698933315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11050205653984638465955543 16575308480976957698933315)
            ·
              refine ⟨24862962721465436548399973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16575308480976957698933315 24862962721465436548399973)
              ·
                refine ⟨4661805510274769352824995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24862962721465436548399973 4661805510274769352824995)
                ·
                  refine ⟨6992708265412154029237493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4661805510274769352824995 6992708265412154029237493)
                  ·
                    refine ⟨655566399882389440241015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6992708265412154029237493 655566399882389440241015)
                    ·
                      rfl

theorem cell23_3830133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3830133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830133 prefixEnd_3830133 := by exact prefixLift 3830133
  have htrace : WordTrace (prefixWord ++ tailWord_3830133) baseStart_3830133 baseEnd_3830133 := by
    simpa [prefixWord, tailWord_3830133, baseEnd_3830133] using wordTrace_append hprefix tailTrace_3830133
  have hstable : (prefixWord ++ tailWord_3830133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830133).length < 2 ^ (prefixWord ++ tailWord_3830133).sum := by decide
  have hdescent : baseEnd_3830133 < baseStart_3830133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830153 : List Nat := [1, 2, 1, 1, 6, 1, 2, 3, 1, 1, 4]
def baseStart_3830153 : Nat := 118140960795 + 3830153 * 2 ^ 59
def prefixEnd_3830153 : Nat := 4983230072969 + 3 ^ 40 * 3830153 * 2
def baseEnd_3830153 : Nat := 1966709469260258242472953

theorem tailTrace_3830153 : CollatzResearch.WordTrace tailWord_3830153 prefixEnd_3830153 1966709469260258242472953 := by
  unfold tailWord_3830153
  simp only [CollatzResearch.WordTrace]
  refine ⟨139697156493017293898919113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93131437662011529265946075 139697156493017293898919113)
  ·
    refine ⟨104772867369762970424189335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139697156493017293898919113 104772867369762970424189335)
    ·
      refine ⟨157159301054644455636284003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104772867369762970424189335 157159301054644455636284003)
      ·
        refine ⟨235738951581966683454426005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157159301054644455636284003 235738951581966683454426005)
        ·
          refine ⟨11050263355404688286926219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235738951581966683454426005 11050263355404688286926219)
          ·
            refine ⟨16575395033107032430389329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11050263355404688286926219 16575395033107032430389329)
            ·
              refine ⟨12431546274830274322791997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16575395033107032430389329 12431546274830274322791997)
              ·
                refine ⟨4661829853061352871046999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12431546274830274322791997 4661829853061352871046999)
                ·
                  refine ⟨6992744779592029306570499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4661829853061352871046999 6992744779592029306570499)
                  ·
                    refine ⟨10489117169388043959855749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6992744779592029306570499 10489117169388043959855749)
                    ·
                      refine ⟨1966709469260258242472953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10489117169388043959855749 1966709469260258242472953)
                      ·
                        rfl

theorem cell23_3830153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 1, 4].length) (baseStart_3830153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830153 prefixEnd_3830153 := by exact prefixLift 3830153
  have htrace : WordTrace (prefixWord ++ tailWord_3830153) baseStart_3830153 baseEnd_3830153 := by
    simpa [prefixWord, tailWord_3830153, baseEnd_3830153] using wordTrace_append hprefix tailTrace_3830153
  have hstable : (prefixWord ++ tailWord_3830153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830153).length < 2 ^ (prefixWord ++ tailWord_3830153).sum := by decide
  have hdescent : baseEnd_3830153 < baseStart_3830153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830156 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_3830156 : Nat := 118140960795 + 3830156 * 2 ^ 59
def prefixEnd_3830156 : Nat := 4983230072969 + 3 ^ 40 * 3830156 * 2
def baseEnd_3830156 : Nat := 1966711009702221730735439

theorem tailTrace_3830156 : CollatzResearch.WordTrace tailWord_3830156 prefixEnd_3830156 1966711009702221730735439 := by
  unfold tailWord_3830156
  simp only [CollatzResearch.WordTrace]
  refine ⟨69848632956003212705639161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93131510608004283607518881 69848632956003212705639161)
  ·
    refine ⟨52386474717002409529229371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69848632956003212705639161 52386474717002409529229371)
    ·
      refine ⟨78579712075503614293844057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52386474717002409529229371 78579712075503614293844057)
      ·
        refine ⟨58934784056627710720383043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78579712075503614293844057 58934784056627710720383043)
        ·
          refine ⟨88402176084941566080574565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58934784056627710720383043 88402176084941566080574565)
          ·
            refine ⟨16575408015926543640107731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88402176084941566080574565 16575408015926543640107731)
            ·
              refine ⟨24863112023889815460161597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16575408015926543640107731 24863112023889815460161597)
              ·
                refine ⟨9323667008958680797560599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24863112023889815460161597 9323667008958680797560599)
                ·
                  refine ⟨13985500513438021196340899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9323667008958680797560599 13985500513438021196340899)
                  ·
                    refine ⟨20978250770157031794511349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13985500513438021196340899 20978250770157031794511349)
                    ·
                      refine ⟨1966711009702221730735439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20978250770157031794511349 1966711009702221730735439)
                      ·
                        rfl

theorem cell23_3830156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_3830156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830156 prefixEnd_3830156 := by exact prefixLift 3830156
  have htrace : WordTrace (prefixWord ++ tailWord_3830156) baseStart_3830156 baseEnd_3830156 := by
    simpa [prefixWord, tailWord_3830156, baseEnd_3830156] using wordTrace_append hprefix tailTrace_3830156
  have hstable : (prefixWord ++ tailWord_3830156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830156).length < 2 ^ (prefixWord ++ tailWord_3830156).sum := by decide
  have hdescent : baseEnd_3830156 < baseStart_3830156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830164 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_3830164 : Nat := 118140960795 + 3830164 * 2 ^ 59
def prefixEnd_3830164 : Nat := 4983230072969 + 3 ^ 40 * 3830164 * 2
def baseEnd_3830164 : Nat := 1966715117547457699435403

theorem tailTrace_3830164 : CollatzResearch.WordTrace tailWord_3830164 prefixEnd_3830164 1966715117547457699435403 := by
  unfold tailWord_3830164
  simp only [CollatzResearch.WordTrace]
  refine ⟨69848778847988721388784773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93131705130651628518379697 69848778847988721388784773)
  ·
    refine ⟨13096646033997885260397145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69848778847988721388784773 13096646033997885260397145)
    ·
      refine ⟨9822484525498413945297859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13096646033997885260397145 9822484525498413945297859)
      ·
        refine ⟨14733726788247620917946789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9822484525498413945297859 14733726788247620917946789)
        ·
          refine ⟨2762573772796428922115023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14733726788247620917946789 2762573772796428922115023)
          ·
            refine ⟨4143860659194643383172535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762573772796428922115023 4143860659194643383172535)
            ·
              refine ⟨6215790988791965074758803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143860659194643383172535 6215790988791965074758803)
              ·
                refine ⟨9323686483187947612138205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215790988791965074758803 9323686483187947612138205)
                ·
                  refine ⟨3496382431195480354551827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9323686483187947612138205 3496382431195480354551827)
                  ·
                    refine ⟨5244573646793220531827741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3496382431195480354551827 5244573646793220531827741)
                    ·
                      refine ⟨1966715117547457699435403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5244573646793220531827741 1966715117547457699435403)
                      ·
                        rfl

theorem cell23_3830164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_3830164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830164 prefixEnd_3830164 := by exact prefixLift 3830164
  have htrace : WordTrace (prefixWord ++ tailWord_3830164) baseStart_3830164 baseEnd_3830164 := by
    simpa [prefixWord, tailWord_3830164, baseEnd_3830164] using wordTrace_append hprefix tailTrace_3830164
  have hstable : (prefixWord ++ tailWord_3830164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830164).length < 2 ^ (prefixWord ++ tailWord_3830164).sum := by decide
  have hdescent : baseEnd_3830164 < baseStart_3830164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830176 : List Nat := [2, 1, 1, 4, 1, 4, 2, 8]
def baseStart_3830176 : Nat := 118140960795 + 3830176 * 2 ^ 59
def prefixEnd_3830176 : Nat := 4983230072969 + 3 ^ 40 * 3830176 * 2
def baseEnd_3830176 : Nat := 72841528863530061203161

theorem tailTrace_3830176 : CollatzResearch.WordTrace tailWord_3830176 prefixEnd_3830176 72841528863530061203161 := by
  unfold tailWord_3830176
  simp only [CollatzResearch.WordTrace]
  refine ⟨69848997685966984413503191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93131996914622645884670921 69848997685966984413503191)
  ·
    refine ⟨104773496528950476620254787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69848997685966984413503191 104773496528950476620254787)
    ·
      refine ⟨157160244793425714930382181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104773496528950476620254787 157160244793425714930382181)
      ·
        refine ⟨29467545898767321549446659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157160244793425714930382181 29467545898767321549446659)
        ·
          refine ⟨44201318848150982324169989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29467545898767321549446659 44201318848150982324169989)
          ·
            refine ⟨8287747284028309185781873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44201318848150982324169989 8287747284028309185781873)
            ·
              refine ⟨6215810463021231889336405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8287747284028309185781873 6215810463021231889336405)
              ·
                refine ⟨72841528863530061203161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6215810463021231889336405 72841528863530061203161)
                ·
                  rfl

theorem cell23_3830176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 8].length) (baseStart_3830176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830176 prefixEnd_3830176 := by exact prefixLift 3830176
  have htrace : WordTrace (prefixWord ++ tailWord_3830176) baseStart_3830176 baseEnd_3830176 := by
    simpa [prefixWord, tailWord_3830176, baseEnd_3830176] using wordTrace_append hprefix tailTrace_3830176
  have hstable : (prefixWord ++ tailWord_3830176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830176).length < 2 ^ (prefixWord ++ tailWord_3830176).sum := by decide
  have hdescent : baseEnd_3830176 < baseStart_3830176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830180 : List Nat := [2, 3, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_3830180 : Nat := 118140960795 + 3830180 * 2 ^ 59
def prefixEnd_3830180 : Nat := 4983230072969 + 3 ^ 40 * 3830180 * 2
def baseEnd_3830180 : Nat := 655574444412643212278443

theorem tailTrace_3830180 : CollatzResearch.WordTrace tailWord_3830180 prefixEnd_3830180 655574444412643212278443 := by
  unfold tailWord_3830180
  simp only [CollatzResearch.WordTrace]
  refine ⟨69849070631959738755075997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93132094175946318340101329 69849070631959738755075997)
  ·
    refine ⟨26193401486984902033153499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69849070631959738755075997 26193401486984902033153499)
    ·
      refine ⟨39290102230477353049730249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26193401486984902033153499 39290102230477353049730249)
      ·
        refine ⟨29467576672858014787297687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39290102230477353049730249 29467576672858014787297687)
        ·
          refine ⟨44201365009287022180946531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29467576672858014787297687 44201365009287022180946531)
          ·
            refine ⟨66302047513930533271419797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44201365009287022180946531 66302047513930533271419797)
            ·
              refine ⟨3107908477215493747097803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66302047513930533271419797 3107908477215493747097803)
              ·
                refine ⟨4661862715823240620646705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107908477215493747097803 4661862715823240620646705)
                ·
                  refine ⟨3496397036867430465485029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4661862715823240620646705 3496397036867430465485029)
                  ·
                    refine ⟨655574444412643212278443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3496397036867430465485029 655574444412643212278443)
                    ·
                      rfl

theorem cell23_3830180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_3830180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830180 prefixEnd_3830180 := by exact prefixLift 3830180
  have htrace : WordTrace (prefixWord ++ tailWord_3830180) baseStart_3830180 baseEnd_3830180 := by
    simpa [prefixWord, tailWord_3830180, baseEnd_3830180] using wordTrace_append hprefix tailTrace_3830180
  have hstable : (prefixWord ++ tailWord_3830180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830180).length < 2 ^ (prefixWord ++ tailWord_3830180).sum := by decide
  have hdescent : baseEnd_3830180 < baseStart_3830180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830256 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 4]
def baseStart_3830256 : Nat := 118140960795 + 3830256 * 2 ^ 59
def prefixEnd_3830256 : Nat := 4983230072969 + 3 ^ 40 * 3830256 * 2
def baseEnd_3830256 : Nat := 1966762357767671339484979

theorem tailTrace_3830256 : CollatzResearch.WordTrace tailWord_3830256 prefixEnd_3830256 1966762357767671339484979 := by
  unfold tailWord_3830256
  simp only [CollatzResearch.WordTrace]
  refine ⟨69850456605822071244959311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93133942141096094993279081 69850456605822071244959311)
  ·
    refine ⟨104775684908733106867438967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69850456605822071244959311 104775684908733106867438967)
    ·
      refine ⟨157163527363099660301158451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104775684908733106867438967 157163527363099660301158451)
      ·
        refine ⟨235745291044649490451737677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157163527363099660301158451 235745291044649490451737677)
        ·
          refine ⟨88404484141743558919401629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235745291044649490451737677 88404484141743558919401629)
          ·
            refine ⟨33151681553153834594775611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88404484141743558919401629 33151681553153834594775611)
            ·
              refine ⟨49727522329730751892163417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33151681553153834594775611 49727522329730751892163417)
              ·
                refine ⟨37295641747298063919122563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49727522329730751892163417 37295641747298063919122563)
                ·
                  refine ⟨55943462620947095878683845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37295641747298063919122563 55943462620947095878683845)
                  ·
                    refine ⟨10489399241427580477253221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55943462620947095878683845 10489399241427580477253221)
                    ·
                      refine ⟨1966762357767671339484979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10489399241427580477253221 1966762357767671339484979)
                      ·
                        rfl

theorem cell23_3830256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_3830256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830256 prefixEnd_3830256 := by exact prefixLift 3830256
  have htrace : WordTrace (prefixWord ++ tailWord_3830256) baseStart_3830256 baseEnd_3830256 := by
    simpa [prefixWord, tailWord_3830256, baseEnd_3830256] using wordTrace_append hprefix tailTrace_3830256
  have hstable : (prefixWord ++ tailWord_3830256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830256).length < 2 ^ (prefixWord ++ tailWord_3830256).sum := by decide
  have hdescent : baseEnd_3830256 < baseStart_3830256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830273 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_3830273 : Nat := 118140960795 + 3830273 * 2 ^ 59
def prefixEnd_3830273 : Nat := 4983230072969 + 3 ^ 40 * 3830273 * 2
def baseEnd_3830273 : Nat := 1966771086938797772972401

theorem tailTrace_3830273 : CollatzResearch.WordTrace tailWord_3830273 prefixEnd_3830273 1966771086938797772972401 := by
  unfold tailWord_3830273
  simp only [CollatzResearch.WordTrace]
  refine ⟨139701533252582554393287473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93134355501721702928858315 139701533252582554393287473)
  ·
    refine ⟨104776149939436915794965605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139701533252582554393287473 104776149939436915794965605)
    ·
      refine ⟨19645528113644421711556051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104776149939436915794965605 19645528113644421711556051)
      ·
        refine ⟨29468292170466632567334077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19645528113644421711556051 29468292170466632567334077)
        ·
          refine ⟨11050609563924987212750279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29468292170466632567334077 11050609563924987212750279)
          ·
            refine ⟨16575914345887480819125419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11050609563924987212750279 16575914345887480819125419)
            ·
              refine ⟨24863871518831221228688129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16575914345887480819125419 24863871518831221228688129)
              ·
                refine ⟨18647903639123415921516097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24863871518831221228688129 18647903639123415921516097)
                ·
                  refine ⟨13985927729342561941137073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18647903639123415921516097 13985927729342561941137073)
                  ·
                    refine ⟨10489445797006921455852805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13985927729342561941137073 10489445797006921455852805)
                    ·
                      refine ⟨1966771086938797772972401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10489445797006921455852805 1966771086938797772972401)
                      ·
                        rfl

theorem cell23_3830273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_3830273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830273 prefixEnd_3830273 := by exact prefixLift 3830273
  have htrace : WordTrace (prefixWord ++ tailWord_3830273) baseStart_3830273 baseEnd_3830273 := by
    simpa [prefixWord, tailWord_3830273, baseEnd_3830273] using wordTrace_append hprefix tailTrace_3830273
  have hstable : (prefixWord ++ tailWord_3830273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830273).length < 2 ^ (prefixWord ++ tailWord_3830273).sum := by decide
  have hdescent : baseEnd_3830273 < baseStart_3830273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830277 : List Nat := [1, 3, 1, 1, 2, 2, 5, 2, 2, 2, 2]
def baseStart_3830277 : Nat := 118140960795 + 3830277 * 2 ^ 59
def prefixEnd_3830277 : Nat := 4983230072969 + 3 ^ 40 * 3830277 * 2
def baseEnd_3830277 : Nat := 1966773140861415757322383

theorem tailTrace_3830277 : CollatzResearch.WordTrace tailWord_3830277 prefixEnd_3830277 1966773140861415757322383 := by
  unfold tailWord_3830277
  simp only [CollatzResearch.WordTrace]
  refine ⟨139701679144568063076433085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93134452763045375384288723 139701679144568063076433085)
  ·
    refine ⟨52388129679213023653662407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139701679144568063076433085 52388129679213023653662407)
    ·
      refine ⟨78582194518819535480493611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52388129679213023653662407 78582194518819535480493611)
      ·
        refine ⟨117873291778229303220740417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78582194518819535480493611 117873291778229303220740417)
        ·
          refine ⟨88404968833671977415555313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117873291778229303220740417 88404968833671977415555313)
          ·
            refine ⟨66303726625253983061666485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88404968833671977415555313 66303726625253983061666485)
            ·
              refine ⟨6215974371117560912031233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66303726625253983061666485 6215974371117560912031233)
              ·
                refine ⟨4661980778338170684023425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6215974371117560912031233 4661980778338170684023425)
                ·
                  refine ⟨3496485583753628013017569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4661980778338170684023425 3496485583753628013017569)
                  ·
                    refine ⟨2622364187815221009763177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3496485583753628013017569 2622364187815221009763177)
                    ·
                      refine ⟨1966773140861415757322383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2622364187815221009763177 1966773140861415757322383)
                      ·
                        rfl

theorem cell23_3830277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 2, 2].length) (baseStart_3830277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830277 prefixEnd_3830277 := by exact prefixLift 3830277
  have htrace : WordTrace (prefixWord ++ tailWord_3830277) baseStart_3830277 baseEnd_3830277 := by
    simpa [prefixWord, tailWord_3830277, baseEnd_3830277] using wordTrace_append hprefix tailTrace_3830277
  have hstable : (prefixWord ++ tailWord_3830277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830277).length < 2 ^ (prefixWord ++ tailWord_3830277).sum := by decide
  have hdescent : baseEnd_3830277 < baseStart_3830277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830283 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 7]
def baseStart_3830283 : Nat := 118140960795 + 3830283 * 2 ^ 59
def prefixEnd_3830283 : Nat := 4983230072969 + 3 ^ 40 * 3830283 * 2
def baseEnd_3830283 : Nat := 218530691305038081538595

theorem tailTrace_3830283 : CollatzResearch.WordTrace tailWord_3830283 prefixEnd_3830283 218530691305038081538595 := by
  unfold tailWord_3830283
  simp only [CollatzResearch.WordTrace]
  refine ⟨139701897982546326101151503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93134598655030884067434335 139701897982546326101151503)
  ·
    refine ⟨209552846973819489151727255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139701897982546326101151503 209552846973819489151727255)
    ·
      refine ⟨314329270460729233727590883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209552846973819489151727255 314329270460729233727590883)
      ·
        refine ⟨471493905691093850591386325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314329270460729233727590883 471493905691093850591386325)
        ·
          refine ⟨11050638414635012123235617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 471493905691093850591386325 11050638414635012123235617)
          ·
            refine ⟨8287978810976259092426713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11050638414635012123235617 8287978810976259092426713)
            ·
              refine ⟨6215984108232194319320035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8287978810976259092426713 6215984108232194319320035)
              ·
                refine ⟨9323976162348291478980053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215984108232194319320035 9323976162348291478980053)
                ·
                  refine ⟨218530691305038081538595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9323976162348291478980053 218530691305038081538595)
                  ·
                    rfl

theorem cell23_3830283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 7].length) (baseStart_3830283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830283 prefixEnd_3830283 := by exact prefixLift 3830283
  have htrace : WordTrace (prefixWord ++ tailWord_3830283) baseStart_3830283 baseEnd_3830283 := by
    simpa [prefixWord, tailWord_3830283, baseEnd_3830283] using wordTrace_append hprefix tailTrace_3830283
  have hstable : (prefixWord ++ tailWord_3830283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830283).length < 2 ^ (prefixWord ++ tailWord_3830283).sum := by decide
  have hdescent : baseEnd_3830283 < baseStart_3830283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830293 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_3830293 : Nat := 118140960795 + 3830293 * 2 ^ 59
def prefixEnd_3830293 : Nat := 4983230072969 + 3 ^ 40 * 3830293 * 2
def baseEnd_3830293 : Nat := 1966781356551887694722309

theorem tailTrace_3830293 : CollatzResearch.WordTrace tailWord_3830293 prefixEnd_3830293 1966781356551887694722309 := by
  unfold tailWord_3830293
  simp only [CollatzResearch.WordTrace]
  refine ⟨139702262712510097809015533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93134841808340065206010355 139702262712510097809015533)
  ·
    refine ⟨52388348517191286678380825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139702262712510097809015533 52388348517191286678380825)
    ·
      refine ⟨39291261387893465008785619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52388348517191286678380825 39291261387893465008785619)
      ·
        refine ⟨58936892081840197513178429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39291261387893465008785619 58936892081840197513178429)
        ·
          refine ⟨22101334530690074067441911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58936892081840197513178429 22101334530690074067441911)
          ·
            refine ⟨33152001796035111101162867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22101334530690074067441911 33152001796035111101162867)
            ·
              refine ⟨49728002694052666651744301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33152001796035111101162867 49728002694052666651744301)
              ·
                refine ⟨18648001010269749994404113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49728002694052666651744301 18648001010269749994404113)
                ·
                  refine ⟨13986000757702312495803085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18648001010269749994404113 13986000757702312495803085)
                  ·
                    refine ⟨5244750284138367185926157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13986000757702312495803085 5244750284138367185926157)
                    ·
                      refine ⟨1966781356551887694722309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5244750284138367185926157 1966781356551887694722309)
                      ·
                        rfl

theorem cell23_3830293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_3830293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830293 prefixEnd_3830293 := by exact prefixLift 3830293
  have htrace : WordTrace (prefixWord ++ tailWord_3830293) baseStart_3830293 baseEnd_3830293 := by
    simpa [prefixWord, tailWord_3830293, baseEnd_3830293] using wordTrace_append hprefix tailTrace_3830293
  have hstable : (prefixWord ++ tailWord_3830293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830293).length < 2 ^ (prefixWord ++ tailWord_3830293).sum := by decide
  have hdescent : baseEnd_3830293 < baseStart_3830293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830334 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 7]
def baseStart_3830334 : Nat := 118140960795 + 3830334 * 2 ^ 59
def prefixEnd_3830334 : Nat := 4983230072969 + 3 ^ 40 * 3830334 * 2
def baseEnd_3830334 : Nat := 218533601028746892701069

theorem tailTrace_3830334 : CollatzResearch.WordTrace tailWord_3830334 prefixEnd_3830334 218533601028746892701069 := by
  unfold tailWord_3830334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17462969763170195226407257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93135838736907707874172037 17462969763170195226407257)
  ·
    refine ⟨13097227322377646419805443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17462969763170195226407257 13097227322377646419805443)
    ·
      refine ⟨19645840983566469629708165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13097227322377646419805443 19645840983566469629708165)
      ·
        refine ⟨3683595184418713055570281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19645840983566469629708165 3683595184418713055570281)
        ·
          refine ⟨2762696388314034791677711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3683595184418713055570281 2762696388314034791677711)
          ·
            refine ⟨4144044582471052187516567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762696388314034791677711 4144044582471052187516567)
            ·
              refine ⟨6216066873706578281274851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4144044582471052187516567 6216066873706578281274851)
              ·
                refine ⟨9324100310559867421912277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6216066873706578281274851 9324100310559867421912277)
                ·
                  refine ⟨218533601028746892701069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9324100310559867421912277 218533601028746892701069)
                  ·
                    rfl

theorem cell23_3830334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_3830334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830334 prefixEnd_3830334 := by exact prefixLift 3830334
  have htrace : WordTrace (prefixWord ++ tailWord_3830334) baseStart_3830334 baseEnd_3830334 := by
    simpa [prefixWord, tailWord_3830334, baseEnd_3830334] using wordTrace_append hprefix tailTrace_3830334
  have hstable : (prefixWord ++ tailWord_3830334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830334).length < 2 ^ (prefixWord ++ tailWord_3830334).sum := by decide
  have hdescent : baseEnd_3830334 < baseStart_3830334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830350 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2]
def baseStart_3830350 : Nat := 118140960795 + 3830350 * 2 ^ 59
def prefixEnd_3830350 : Nat := 4983230072969 + 3 ^ 40 * 3830350 * 2
def baseEnd_3830350 : Nat := 1966810624949193971709547

theorem tailTrace_3830350 : CollatzResearch.WordTrace tailWord_3830350 prefixEnd_3830350 1966810624949193971709547 := by
  unfold tailWord_3830350
  simp only [CollatzResearch.WordTrace]
  refine ⟨17463042709162949567980063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93136227782202397695893669 17463042709162949567980063)
  ·
    refine ⟨26194564063744424351970095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17463042709162949567980063 26194564063744424351970095)
    ·
      refine ⟨39291846095616636527955143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26194564063744424351970095 39291846095616636527955143)
      ·
        refine ⟨58937769143424954791932715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39291846095616636527955143 58937769143424954791932715)
        ·
          refine ⟨88406653715137432187899073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58937769143424954791932715 88406653715137432187899073)
          ·
            refine ⟨66304990286353074140924305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88406653715137432187899073 66304990286353074140924305)
            ·
              refine ⟨49728742714764805605693229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66304990286353074140924305 49728742714764805605693229)
              ·
                refine ⟨18648278518036802102134961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49728742714764805605693229 18648278518036802102134961)
                ·
                  refine ⟨13986208888527601576601221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18648278518036802102134961 13986208888527601576601221)
                  ·
                    refine ⟨2622414166598925295612729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13986208888527601576601221 2622414166598925295612729)
                    ·
                      refine ⟨1966810624949193971709547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2622414166598925295612729 1966810624949193971709547)
                      ·
                        rfl

theorem cell23_3830350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_3830350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830350 prefixEnd_3830350 := by exact prefixLift 3830350
  have htrace : WordTrace (prefixWord ++ tailWord_3830350) baseStart_3830350 baseEnd_3830350 := by
    simpa [prefixWord, tailWord_3830350, baseEnd_3830350] using wordTrace_append hprefix tailTrace_3830350
  have hstable : (prefixWord ++ tailWord_3830350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830350).length < 2 ^ (prefixWord ++ tailWord_3830350).sum := by decide
  have hdescent : baseEnd_3830350 < baseStart_3830350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830403 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 3, 5]
def baseStart_3830403 : Nat := 118140960795 + 3830403 * 2 ^ 59
def prefixEnd_3830403 : Nat := 4983230072969 + 3 ^ 40 * 3830403 * 2
def baseEnd_3830403 : Nat := 655612613141294088115601

theorem tailTrace_3830403 : CollatzResearch.WordTrace tailWord_3830403 prefixEnd_3830403 655612613141294088115601 := by
  unfold tailWord_3830403
  simp only [CollatzResearch.WordTrace]
  refine ⟨139706274742111586595519863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93137516494741057730346575 139706274742111586595519863)
  ·
    refine ⟨209559412113167379893279795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139706274742111586595519863 209559412113167379893279795)
    ·
      refine ⟨314339118169751069839919693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209559412113167379893279795 314339118169751069839919693)
      ·
        refine ⟨117877169313656651189969885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314339118169751069839919693 117877169313656651189969885)
        ·
          refine ⟨44203938492621244196238707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117877169313656651189969885 44203938492621244196238707)
          ·
            refine ⟨66305907738931866294358061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44203938492621244196238707 66305907738931866294358061)
            ·
              refine ⟨24864715402099449860384273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66305907738931866294358061 24864715402099449860384273)
              ·
                refine ⟨18648536551574587395288205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24864715402099449860384273 18648536551574587395288205)
                ·
                  refine ⟨6993201206840470273233077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18648536551574587395288205 6993201206840470273233077)
                  ·
                    refine ⟨655612613141294088115601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6993201206840470273233077 655612613141294088115601)
                    ·
                      rfl

theorem cell23_3830403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 5].length) (baseStart_3830403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830403 prefixEnd_3830403 := by exact prefixLift 3830403
  have htrace : WordTrace (prefixWord ++ tailWord_3830403) baseStart_3830403 baseEnd_3830403 := by
    simpa [prefixWord, tailWord_3830403, baseEnd_3830403] using wordTrace_append hprefix tailTrace_3830403
  have hstable : (prefixWord ++ tailWord_3830403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830403).length < 2 ^ (prefixWord ++ tailWord_3830403).sum := by decide
  have hdescent : baseEnd_3830403 < baseStart_3830403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830460 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3830460 : Nat := 118140960795 + 3830460 * 2 ^ 59
def prefixEnd_3830460 : Nat := 4983230072969 + 3 ^ 40 * 3830460 * 2
def baseEnd_3830460 : Nat := 1966867107821188541334041

theorem tailTrace_3830460 : CollatzResearch.WordTrace tailWord_3830460 prefixEnd_3830460 1966867107821188541334041 := by
  unfold tailWord_3830460
  simp only [CollatzResearch.WordTrace]
  refine ⟨69854176851452542665172417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93138902468603390220229889 69854176851452542665172417)
  ·
    refine ⟨52390632638589406998879313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69854176851452542665172417 52390632638589406998879313)
    ·
      refine ⟨39292974478942055249159485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52390632638589406998879313 39292974478942055249159485)
      ·
        refine ⟨14734865429603270718434807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39292974478942055249159485 14734865429603270718434807)
        ·
          refine ⟨22102298144404906077652211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14734865429603270718434807 22102298144404906077652211)
          ·
            refine ⟨33153447216607359116478317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22102298144404906077652211 33153447216607359116478317)
            ·
              refine ⟨12432542706227759668679369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33153447216607359116478317 12432542706227759668679369)
              ·
                refine ⟨9324407029670819751509527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12432542706227759668679369 9324407029670819751509527)
                ·
                  refine ⟨13986610544506229627264291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9324407029670819751509527 13986610544506229627264291)
                  ·
                    refine ⟨20979915816759344440896437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13986610544506229627264291 20979915816759344440896437)
                    ·
                      refine ⟨1966867107821188541334041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20979915816759344440896437 1966867107821188541334041)
                      ·
                        rfl

theorem cell23_3830460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3830460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830460 prefixEnd_3830460 := by exact prefixLift 3830460
  have htrace : WordTrace (prefixWord ++ tailWord_3830460) baseStart_3830460 baseEnd_3830460 := by
    simpa [prefixWord, tailWord_3830460, baseEnd_3830460] using wordTrace_append hprefix tailTrace_3830460
  have hstable : (prefixWord ++ tailWord_3830460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830460).length < 2 ^ (prefixWord ++ tailWord_3830460).sum := by decide
  have hdescent : baseEnd_3830460 < baseStart_3830460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830474 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 3, 2, 2]
def baseStart_3830474 : Nat := 118140960795 + 3830474 * 2 ^ 59
def prefixEnd_3830474 : Nat := 4983230072969 + 3 ^ 40 * 3830474 * 2
def baseEnd_3830474 : Nat := 1966874296550351486558977

theorem tailTrace_3830474 : CollatzResearch.WordTrace tailWord_3830474 prefixEnd_3830474 1966874296550351486558977 := by
  unfold tailWord_3830474
  simp only [CollatzResearch.WordTrace]
  refine ⟨34927216081213591430338619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93139242883236243814236317 34927216081213591430338619)
  ·
    refine ⟨52390824121820387145507929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34927216081213591430338619 52390824121820387145507929)
    ·
      refine ⟨39293118091365290359130947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52390824121820387145507929 39293118091365290359130947)
      ·
        refine ⟨58939677137047935538696421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39293118091365290359130947 58939677137047935538696421)
        ·
          refine ⟨11051189463196487913505579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58939677137047935538696421 11051189463196487913505579)
          ·
            refine ⟨16576784194794731870258369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11051189463196487913505579 16576784194794731870258369)
            ·
              refine ⟨12432588146096048902693777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16576784194794731870258369 12432588146096048902693777)
              ·
                refine ⟨9324441109572036677020333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12432588146096048902693777 9324441109572036677020333)
                ·
                  refine ⟨3496665416089513753882625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9324441109572036677020333 3496665416089513753882625)
                  ·
                    refine ⟨2622499062067135315411969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3496665416089513753882625 2622499062067135315411969)
                    ·
                      refine ⟨1966874296550351486558977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2622499062067135315411969 1966874296550351486558977)
                      ·
                        rfl

theorem cell23_3830474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_3830474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830474 prefixEnd_3830474 := by exact prefixLift 3830474
  have htrace : WordTrace (prefixWord ++ tailWord_3830474) baseStart_3830474 baseEnd_3830474 := by
    simpa [prefixWord, tailWord_3830474, baseEnd_3830474] using wordTrace_append hprefix tailTrace_3830474
  have hstable : (prefixWord ++ tailWord_3830474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830474).length < 2 ^ (prefixWord ++ tailWord_3830474).sum := by decide
  have hdescent : baseEnd_3830474 < baseStart_3830474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830485 : List Nat := [1, 3, 2, 5, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3830485 : Nat := 118140960795 + 3830485 * 2 ^ 59
def prefixEnd_3830485 : Nat := 4983230072969 + 3 ^ 40 * 3830485 * 2
def baseEnd_3830485 : Nat := 1966879944837550943521427

theorem tailTrace_3830485 : CollatzResearch.WordTrace tailWord_3830485 prefixEnd_3830485 1966879944837550943521427 := by
  unfold tailWord_3830485
  simp only [CollatzResearch.WordTrace]
  refine ⟨139709265527814514600004909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93139510351876343066669939 139709265527814514600004909)
  ·
    refine ⟨52390974572930442975001841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139709265527814514600004909 52390974572930442975001841)
    ·
      refine ⟨39293230929697832231251381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52390974572930442975001841 39293230929697832231251381)
      ·
        refine ⟨3683740399659171771679817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39293230929697832231251381 3683740399659171771679817)
        ·
          refine ⟨2762805299744378828759863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3683740399659171771679817 2762805299744378828759863)
          ·
            refine ⟨4144207949616568243139795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762805299744378828759863 4144207949616568243139795)
            ·
              refine ⟨6216311924424852364709693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4144207949616568243139795 6216311924424852364709693)
              ·
                refine ⟨2331116971659319636766135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6216311924424852364709693 2331116971659319636766135)
                ·
                  refine ⟨3496675457488979455149203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331116971659319636766135 3496675457488979455149203)
                  ·
                    refine ⟨5245013186233469182723805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3496675457488979455149203 5245013186233469182723805)
                    ·
                      refine ⟨1966879944837550943521427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5245013186233469182723805 1966879944837550943521427)
                      ·
                        rfl

theorem cell23_3830485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3830485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830485 prefixEnd_3830485 := by exact prefixLift 3830485
  have htrace : WordTrace (prefixWord ++ tailWord_3830485) baseStart_3830485 baseEnd_3830485 := by
    simpa [prefixWord, tailWord_3830485, baseEnd_3830485] using wordTrace_append hprefix tailTrace_3830485
  have hstable : (prefixWord ++ tailWord_3830485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830485).length < 2 ^ (prefixWord ++ tailWord_3830485).sum := by decide
  have hdescent : baseEnd_3830485 < baseStart_3830485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830490 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3]
def baseStart_3830490 : Nat := 118140960795 + 3830490 * 2 ^ 59
def prefixEnd_3830490 : Nat := 4983230072969 + 3 ^ 40 * 3830490 * 2
def baseEnd_3830490 : Nat := 1966882512240823423958903

theorem tailTrace_3830490 : CollatzResearch.WordTrace tailWord_3830490 prefixEnd_3830490 1966882512240823423958903 := by
  unfold tailWord_3830490
  simp only [CollatzResearch.WordTrace]
  refine ⟨34927361973199100113484231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93139631928530933635957949 34927361973199100113484231)
  ·
    refine ⟨52391042959798650170226347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34927361973199100113484231 52391042959798650170226347)
    ·
      refine ⟨78586564439697975255339521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52391042959798650170226347 78586564439697975255339521)
      ·
        refine ⟨58939923329773481441504641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78586564439697975255339521 58939923329773481441504641)
        ·
          refine ⟨44204942497330111081128481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58939923329773481441504641 44204942497330111081128481)
          ·
            refine ⟨33153706872997583310846361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44204942497330111081128481 33153706872997583310846361)
            ·
              refine ⟨24865280154748187483134771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33153706872997583310846361 24865280154748187483134771)
              ·
                refine ⟨37297920232122281224702157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24865280154748187483134771 37297920232122281224702157)
                ·
                  refine ⟨13986720087045855459263309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37297920232122281224702157 13986720087045855459263309)
                  ·
                    refine ⟨5245020032642195797223741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13986720087045855459263309 5245020032642195797223741)
                    ·
                      refine ⟨1966882512240823423958903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5245020032642195797223741 1966882512240823423958903)
                      ·
                        rfl

theorem cell23_3830490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_3830490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830490 prefixEnd_3830490 := by exact prefixLift 3830490
  have htrace : WordTrace (prefixWord ++ tailWord_3830490) baseStart_3830490 baseEnd_3830490 := by
    simpa [prefixWord, tailWord_3830490, baseEnd_3830490] using wordTrace_append hprefix tailTrace_3830490
  have hstable : (prefixWord ++ tailWord_3830490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830490).length < 2 ^ (prefixWord ++ tailWord_3830490).sum := by decide
  have hdescent : baseEnd_3830490 < baseStart_3830490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830507 : List Nat := [1, 1, 1, 1, 2, 4, 1, 6, 2, 1, 3]
def baseStart_3830507 : Nat := 118140960795 + 3830507 * 2 ^ 59
def prefixEnd_3830507 : Nat := 4983230072969 + 3 ^ 40 * 3830507 * 2
def baseEnd_3830507 : Nat := 1966891241411949857446325

theorem tailTrace_3830507 : CollatzResearch.WordTrace tailWord_3830507 prefixEnd_3830507 1966891241411949857446325 := by
  unfold tailWord_3830507
  simp only [CollatzResearch.WordTrace]
  refine ⟨139710067933734812357305775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93140045289156541571537183 139710067933734812357305775)
  ·
    refine ⟨209565101900602218535958663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139710067933734812357305775 209565101900602218535958663)
    ·
      refine ⟨314347652850903327803937995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209565101900602218535958663 314347652850903327803937995)
      ·
        refine ⟨471521479276354991705906993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314347652850903327803937995 471521479276354991705906993)
        ·
          refine ⟨353641109457266243779430245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471521479276354991705906993 353641109457266243779430245)
          ·
            refine ⟨66307708023237420708643171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353641109457266243779430245 66307708023237420708643171)
            ·
              refine ⟨99461562034856131062964757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66307708023237420708643171 99461562034856131062964757)
              ·
                refine ⟨4662260720383881143576473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99461562034856131062964757 4662260720383881143576473)
                ·
                  refine ⟨3496695540287910857682355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4662260720383881143576473 3496695540287910857682355)
                  ·
                    refine ⟨5245043310431866286523533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3496695540287910857682355 5245043310431866286523533)
                    ·
                      refine ⟨1966891241411949857446325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5245043310431866286523533 1966891241411949857446325)
                      ·
                        rfl

theorem cell23_3830507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 1, 3].length) (baseStart_3830507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830507 prefixEnd_3830507 := by exact prefixLift 3830507
  have htrace : WordTrace (prefixWord ++ tailWord_3830507) baseStart_3830507 baseEnd_3830507 := by
    simpa [prefixWord, tailWord_3830507, baseEnd_3830507] using wordTrace_append hprefix tailTrace_3830507
  have hstable : (prefixWord ++ tailWord_3830507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830507).length < 2 ^ (prefixWord ++ tailWord_3830507).sum := by decide
  have hdescent : baseEnd_3830507 < baseStart_3830507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830523 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 6, 6]
def baseStart_3830523 : Nat := 118140960795 + 3830523 * 2 ^ 59
def prefixEnd_3830523 : Nat := 4983230072969 + 3 ^ 40 * 3830523 * 2
def baseEnd_3830523 : Nat := 655633152367473931615417

theorem tailTrace_3830523 : CollatzResearch.WordTrace tailWord_3830523 prefixEnd_3830523 655633152367473931615417 := by
  unfold tailWord_3830523
  simp only [CollatzResearch.WordTrace]
  refine ⟨139710651501676847089888223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93140434334451231393258815 139710651501676847089888223)
  ·
    refine ⟨209565977252515270634832335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139710651501676847089888223 209565977252515270634832335)
    ·
      refine ⟨314348965878772905952248503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209565977252515270634832335 314348965878772905952248503)
      ·
        refine ⟨471523448818159358928372755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314348965878772905952248503 471523448818159358928372755)
        ·
          refine ⟨707285173227239038392559133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471523448818159358928372755 707285173227239038392559133)
          ·
            refine ⟨265231939960214639397209675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 707285173227239038392559133 265231939960214639397209675)
            ·
              refine ⟨397847909940321959095814513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265231939960214639397209675 397847909940321959095814513)
              ·
                refine ⟨298385932455241469321860885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397847909940321959095814513 298385932455241469321860885)
                ·
                  refine ⟨13986840583839443874462229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 298385932455241469321860885 13986840583839443874462229)
                  ·
                    refine ⟨655633152367473931615417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13986840583839443874462229 655633152367473931615417)
                    ·
                      rfl

theorem cell23_3830523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 6].length) (baseStart_3830523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830523 prefixEnd_3830523 := by exact prefixLift 3830523
  have htrace : WordTrace (prefixWord ++ tailWord_3830523) baseStart_3830523 baseEnd_3830523 := by
    simpa [prefixWord, tailWord_3830523, baseEnd_3830523] using wordTrace_append hprefix tailTrace_3830523
  have hstable : (prefixWord ++ tailWord_3830523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830523).length < 2 ^ (prefixWord ++ tailWord_3830523).sum := by decide
  have hdescent : baseEnd_3830523 < baseStart_3830523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830524 : List Nat := [2, 2, 2, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_3830524 : Nat := 118140960795 + 3830524 * 2 ^ 59
def prefixEnd_3830524 : Nat := 4983230072969 + 3 ^ 40 * 3830524 * 2
def baseEnd_3830524 : Nat := 1966899970583076290933747

theorem tailTrace_3830524 : CollatzResearch.WordTrace tailWord_3830524 prefixEnd_3830524 1966899970583076290933747 := by
  unfold tailWord_3830524
  simp only [CollatzResearch.WordTrace]
  refine ⟨69855343987336612130337313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93140458649782149507116417 69855343987336612130337313)
  ·
    refine ⟨52391507990502459097752985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69855343987336612130337313 52391507990502459097752985)
    ·
      refine ⟨39293630992876844323314739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52391507990502459097752985 39293630992876844323314739)
      ·
        refine ⟨58940446489315266484972109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39293630992876844323314739 58940446489315266484972109)
        ·
          refine ⟨22102667433493224931864541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58940446489315266484972109 22102667433493224931864541)
          ·
            refine ⟨8288500287559959349449203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22102667433493224931864541 8288500287559959349449203)
            ·
              refine ⟨12432750431339939024173805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8288500287559959349449203 12432750431339939024173805)
              ·
                refine ⟨4662281411752477134065177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12432750431339939024173805 4662281411752477134065177)
                ·
                  refine ⟨3496711058814357850548883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4662281411752477134065177 3496711058814357850548883)
                  ·
                    refine ⟨5245066588221536775823325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3496711058814357850548883 5245066588221536775823325)
                    ·
                      refine ⟨1966899970583076290933747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5245066588221536775823325 1966899970583076290933747)
                      ·
                        rfl

theorem cell23_3830524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_3830524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830524 prefixEnd_3830524 := by exact prefixLift 3830524
  have htrace : WordTrace (prefixWord ++ tailWord_3830524) baseStart_3830524 baseEnd_3830524 := by
    simpa [prefixWord, tailWord_3830524, baseEnd_3830524] using wordTrace_append hprefix tailTrace_3830524
  have hstable : (prefixWord ++ tailWord_3830524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830524).length < 2 ^ (prefixWord ++ tailWord_3830524).sum := by decide
  have hdescent : baseEnd_3830524 < baseStart_3830524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830547 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 1, 4, 2]
def baseStart_3830547 : Nat := 118140960795 + 3830547 * 2 ^ 59
def prefixEnd_3830547 : Nat := 4983230072969 + 3 ^ 40 * 3830547 * 2
def baseEnd_3830547 : Nat := 1966911780638129700946141

theorem tailTrace_3830547 : CollatzResearch.WordTrace tailWord_3830547 prefixEnd_3830547 1966911780638129700946141 := by
  unfold tailWord_3830547
  simp only [CollatzResearch.WordTrace]
  refine ⟨139711526853589899188761895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93141017902393266125841263 139711526853589899188761895)
  ·
    refine ⟨209567290280384848783142843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139711526853589899188761895 209567290280384848783142843)
    ·
      refine ⟨314350935420577273174714265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209567290280384848783142843 314350935420577273174714265)
      ·
        refine ⟨235763201565432954881035699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314350935420577273174714265 235763201565432954881035699)
        ·
          refine ⟨353644802348149432321553549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235763201565432954881035699 353644802348149432321553549)
          ·
            refine ⟨132616800880556037120582581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353644802348149432321553549 132616800880556037120582581)
            ·
              refine ⟨12432825082552128480054617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132616800880556037120582581 12432825082552128480054617)
              ·
                refine ⟨9324618811914096360040963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12432825082552128480054617 9324618811914096360040963)
                ·
                  refine ⟨13986928217871144540061445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9324618811914096360040963 13986928217871144540061445)
                  ·
                    refine ⟨2622549040850839601261521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13986928217871144540061445 2622549040850839601261521)
                    ·
                      refine ⟨1966911780638129700946141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2622549040850839601261521 1966911780638129700946141)
                      ·
                        rfl

theorem cell23_3830547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 4, 2].length) (baseStart_3830547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830547 prefixEnd_3830547 := by exact prefixLift 3830547
  have htrace : WordTrace (prefixWord ++ tailWord_3830547) baseStart_3830547 baseEnd_3830547 := by
    simpa [prefixWord, tailWord_3830547, baseEnd_3830547] using wordTrace_append hprefix tailTrace_3830547
  have hstable : (prefixWord ++ tailWord_3830547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830547).length < 2 ^ (prefixWord ++ tailWord_3830547).sum := by decide
  have hdescent : baseEnd_3830547 < baseStart_3830547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830553 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 11]
def baseStart_3830553 : Nat := 118140960795 + 3830553 * 2 ^ 59
def prefixEnd_3830553 : Nat := 4983230072969 + 3 ^ 40 * 3830553 * 2
def baseEnd_3830553 : Nat := 218546095724672964163457

theorem tailTrace_3830553 : CollatzResearch.WordTrace tailWord_3830553 prefixEnd_3830553 218546095724672964163457 := by
  unfold tailWord_3830553
  simp only [CollatzResearch.WordTrace]
  refine ⟨139711745691568162213480313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93141163794378774808986875 139711745691568162213480313)
  ·
    refine ⟨104783809268676121660110235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139711745691568162213480313 104783809268676121660110235)
    ·
      refine ⟨157175713903014182490165353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104783809268676121660110235 157175713903014182490165353)
      ·
        refine ⟨117881785427260636867624015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157175713903014182490165353 117881785427260636867624015)
        ·
          refine ⟨176822678140890955301436023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117881785427260636867624015 176822678140890955301436023)
          ·
            refine ⟨265234017211336432952154035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176822678140890955301436023 265234017211336432952154035)
            ·
              refine ⟨397851025817004649428231053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265234017211336432952154035 397851025817004649428231053)
              ·
                refine ⟨149194134681376743535586645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397851025817004649428231053 149194134681376743535586645)
                ·
                  refine ⟨218546095724672964163457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 149194134681376743535586645 218546095724672964163457)
                  ·
                    rfl

theorem cell23_3830553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 11].length) (baseStart_3830553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830553 prefixEnd_3830553 := by exact prefixLift 3830553
  have htrace : WordTrace (prefixWord ++ tailWord_3830553) baseStart_3830553 baseEnd_3830553 := by
    simpa [prefixWord, tailWord_3830553, baseEnd_3830553] using wordTrace_append hprefix tailTrace_3830553
  have hstable : (prefixWord ++ tailWord_3830553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830553).length < 2 ^ (prefixWord ++ tailWord_3830553).sum := by decide
  have hdescent : baseEnd_3830553 < baseStart_3830553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830581 : List Nat := [1, 3, 3, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_3830581 : Nat := 118140960795 + 3830581 * 2 ^ 59
def prefixEnd_3830581 : Nat := 4983230072969 + 3 ^ 40 * 3830581 * 2
def baseEnd_3830581 : Nat := 1966929238980382567920985

theorem tailTrace_3830581 : CollatzResearch.WordTrace tailWord_3830581 prefixEnd_3830581 1966929238980382567920985 := by
  unfold tailWord_3830581
  simp only [CollatzResearch.WordTrace]
  refine ⟨139712766935466722995499597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93141844623644481996999731 139712766935466722995499597)
  ·
    refine ⟨52392287600800021123312349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139712766935466722995499597 52392287600800021123312349)
    ·
      refine ⟨19647107850300007921242131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52392287600800021123312349 19647107850300007921242131)
      ·
        refine ⟨29470661775450011881863197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19647107850300007921242131 29470661775450011881863197)
        ·
          refine ⟨11051498165793754455698699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29470661775450011881863197 11051498165793754455698699)
          ·
            refine ⟨16577247248690631683548049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11051498165793754455698699 16577247248690631683548049)
            ·
              refine ⟨12432935436517973762661037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16577247248690631683548049 12432935436517973762661037)
              ·
                refine ⟨4662350788694240160997889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12432935436517973762661037 4662350788694240160997889)
                ·
                  refine ⟨3496763091520680120748417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4662350788694240160997889 3496763091520680120748417)
                  ·
                    refine ⟨2622572318640510090561313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3496763091520680120748417 2622572318640510090561313)
                    ·
                      refine ⟨1966929238980382567920985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2622572318640510090561313 1966929238980382567920985)
                      ·
                        rfl

theorem cell23_3830581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_3830581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830581 prefixEnd_3830581 := by exact prefixLift 3830581
  have htrace : WordTrace (prefixWord ++ tailWord_3830581) baseStart_3830581 baseEnd_3830581 := by
    simpa [prefixWord, tailWord_3830581, baseEnd_3830581] using wordTrace_append hprefix tailTrace_3830581
  have hstable : (prefixWord ++ tailWord_3830581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830581).length < 2 ^ (prefixWord ++ tailWord_3830581).sum := by decide
  have hdescent : baseEnd_3830581 < baseStart_3830581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830600 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 1, 7]
def baseStart_3830600 : Nat := 118140960795 + 3830600 * 2 ^ 59
def prefixEnd_3830600 : Nat := 4983230072969 + 3 ^ 40 * 3830600 * 2
def baseEnd_3830600 : Nat := 655646331704272664527799

theorem tailTrace_3830600 : CollatzResearch.WordTrace tailWord_3830600 prefixEnd_3830600 655646331704272664527799 := by
  unfold tailWord_3830600
  simp only [CollatzResearch.WordTrace]
  refine ⟨69856729961198944620220627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93142306614931926160294169 69856729961198944620220627)
  ·
    refine ⟨104785094941798416930330941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69856729961198944620220627 104785094941798416930330941)
    ·
      refine ⟨39294410603174406348874103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104785094941798416930330941 39294410603174406348874103)
      ·
        refine ⟨58941615904761609523311155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39294410603174406348874103 58941615904761609523311155)
        ·
          refine ⟨88412423857142414284966733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58941615904761609523311155 88412423857142414284966733)
          ·
            refine ⟨33154658946428405356862525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88412423857142414284966733 33154658946428405356862525)
            ·
              refine ⟨12432997104910652008823447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33154658946428405356862525 12432997104910652008823447)
              ·
                refine ⟨18649495657365978013235171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12432997104910652008823447 18649495657365978013235171)
                ·
                  refine ⟨27974243486048967019852757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18649495657365978013235171 27974243486048967019852757)
                  ·
                    refine ⟨655646331704272664527799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27974243486048967019852757 655646331704272664527799)
                    ·
                      rfl

theorem cell23_3830600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_3830600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830600 prefixEnd_3830600 := by exact prefixLift 3830600
  have htrace : WordTrace (prefixWord ++ tailWord_3830600) baseStart_3830600 baseEnd_3830600 := by
    simpa [prefixWord, tailWord_3830600, baseEnd_3830600] using wordTrace_append hprefix tailTrace_3830600
  have hstable : (prefixWord ++ tailWord_3830600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830600).length < 2 ^ (prefixWord ++ tailWord_3830600).sum := by decide
  have hdescent : baseEnd_3830600 < baseStart_3830600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830604 : List Nat := [2, 2, 1, 3, 3, 2, 2, 3, 5]
def baseStart_3830604 : Nat := 118140960795 + 3830604 * 2 ^ 59
def prefixEnd_3830604 : Nat := 4983230072969 + 3 ^ 40 * 3830604 * 2
def baseEnd_3830604 : Nat := 218549005448381775325931

theorem tailTrace_3830604 : CollatzResearch.WordTrace tailWord_3830604 prefixEnd_3830604 218549005448381775325931 := by
  unfold tailWord_3830604
  simp only [CollatzResearch.WordTrace]
  refine ⟨69856802907191698961793433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93142403876255598615724577 69856802907191698961793433)
  ·
    refine ⟨52392602180393774221345075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69856802907191698961793433 52392602180393774221345075)
    ·
      refine ⟨78588903270590661332017613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52392602180393774221345075 78588903270590661332017613)
      ·
        refine ⟨29470838726471497999506605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78588903270590661332017613 29470838726471497999506605)
        ·
          refine ⟨11051564522426811749814977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29470838726471497999506605 11051564522426811749814977)
          ·
            refine ⟨8288673391820108812361233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11051564522426811749814977 8288673391820108812361233)
            ·
              refine ⟨6216505043865081609270925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8288673391820108812361233 6216505043865081609270925)
              ·
                refine ⟨2331189391449405603476597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6216505043865081609270925 2331189391449405603476597)
                ·
                  refine ⟨218549005448381775325931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2331189391449405603476597 218549005448381775325931)
                  ·
                    rfl

theorem cell23_3830604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_3830604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830604 prefixEnd_3830604 := by exact prefixLift 3830604
  have htrace : WordTrace (prefixWord ++ tailWord_3830604) baseStart_3830604 baseEnd_3830604 := by
    simpa [prefixWord, tailWord_3830604, baseEnd_3830604] using wordTrace_append hprefix tailTrace_3830604
  have hstable : (prefixWord ++ tailWord_3830604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830604).length < 2 ^ (prefixWord ++ tailWord_3830604).sum := by decide
  have hdescent : baseEnd_3830604 < baseStart_3830604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830650 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_3830650 : Nat := 118140960795 + 3830650 * 2 ^ 59
def prefixEnd_3830650 : Nat := 4983230072969 + 3 ^ 40 * 3830650 * 2
def baseEnd_3830650 : Nat := 1966964669145542797958167

theorem tailTrace_3830650 : CollatzResearch.WordTrace tailWord_3830650 prefixEnd_3830650 1966964669145542797958167 := by
  unfold tailWord_3830650
  simp only [CollatzResearch.WordTrace]
  refine ⟨34928820893054186944940351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93143522381477831853174269 34928820893054186944940351)
  ·
    refine ⟨52393231339581280417410527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34928820893054186944940351 52393231339581280417410527)
    ·
      refine ⟨78589847009371920626115791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52393231339581280417410527 78589847009371920626115791)
      ·
        refine ⟨117884770514057880939173687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78589847009371920626115791 117884770514057880939173687)
        ·
          refine ⟨176827155771086821408760531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117884770514057880939173687 176827155771086821408760531)
          ·
            refine ⟨265240733656630232113140797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176827155771086821408760531 265240733656630232113140797)
            ·
              refine ⟨99465275121236337042427799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265240733656630232113140797 99465275121236337042427799)
              ·
                refine ⟨149197912681854505563641699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99465275121236337042427799 149197912681854505563641699)
                ·
                  refine ⟨223796869022781758345462549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149197912681854505563641699 223796869022781758345462549)
                  ·
                    refine ⟨10490478235442894922443557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 223796869022781758345462549 10490478235442894922443557)
                    ·
                      refine ⟨1966964669145542797958167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10490478235442894922443557 1966964669145542797958167)
                      ·
                        rfl

theorem cell23_3830650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_3830650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830650 prefixEnd_3830650 := by exact prefixLift 3830650
  have htrace : WordTrace (prefixWord ++ tailWord_3830650) baseStart_3830650 baseEnd_3830650 := by
    simpa [prefixWord, tailWord_3830650, baseEnd_3830650] using wordTrace_append hprefix tailTrace_3830650
  have hstable : (prefixWord ++ tailWord_3830650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830650).length < 2 ^ (prefixWord ++ tailWord_3830650).sum := by decide
  have hdescent : baseEnd_3830650 < baseStart_3830650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830700 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_3830700 : Nat := 118140960795 + 3830700 * 2 ^ 59
def prefixEnd_3830700 : Nat := 4983230072969 + 3 ^ 40 * 3830700 * 2
def baseEnd_3830700 : Nat := 1966990343178267602332937

theorem tailTrace_3830700 : CollatzResearch.WordTrace tailWord_3830700 prefixEnd_3830700 1966990343178267602332937 := by
  unfold tailWord_3830700
  simp only [CollatzResearch.WordTrace]
  refine ⟨69858553611017803159540777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93144738148023737546054369 69858553611017803159540777)
  ·
    refine ⟨52393915208263352369655583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69858553611017803159540777 52393915208263352369655583)
    ·
      refine ⟨78590872812395028554483375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52393915208263352369655583 78590872812395028554483375)
      ·
        refine ⟨117886309218592542831725063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78590872812395028554483375 117886309218592542831725063)
        ·
          refine ⟨176829463827888814247587595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117886309218592542831725063 176829463827888814247587595)
          ·
            refine ⟨265244195741833221371381393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176829463827888814247587595 265244195741833221371381393)
            ·
              refine ⟨198933146806374916028536045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265244195741833221371381393 198933146806374916028536045)
              ·
                refine ⟨74599930052390593510701017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198933146806374916028536045 74599930052390593510701017)
                ·
                  refine ⟨55949947539292945133025763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74599930052390593510701017 55949947539292945133025763)
                  ·
                    refine ⟨83924921308939417699538645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55949947539292945133025763 83924921308939417699538645)
                    ·
                      refine ⟨1966990343178267602332937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83924921308939417699538645 1966990343178267602332937)
                      ·
                        rfl

theorem cell23_3830700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_3830700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830700 prefixEnd_3830700 := by exact prefixLift 3830700
  have htrace : WordTrace (prefixWord ++ tailWord_3830700) baseStart_3830700 baseEnd_3830700 := by
    simpa [prefixWord, tailWord_3830700, baseEnd_3830700] using wordTrace_append hprefix tailTrace_3830700
  have hstable : (prefixWord ++ tailWord_3830700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830700).length < 2 ^ (prefixWord ++ tailWord_3830700).sum := by decide
  have hdescent : baseEnd_3830700 < baseStart_3830700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830707 : List Nat := [1, 1, 1, 2, 3, 1, 2, 6, 1, 5]
def baseStart_3830707 : Nat := 118140960795 + 3830707 * 2 ^ 59
def prefixEnd_3830707 : Nat := 4983230072969 + 3 ^ 40 * 3830707 * 2
def baseEnd_3830707 : Nat := 655664645847616358315135

theorem tailTrace_3830707 : CollatzResearch.WordTrace tailWord_3830707 prefixEnd_3830707 655664645847616358315135 := by
  unfold tailWord_3830707
  simp only [CollatzResearch.WordTrace]
  refine ⟨139717362533010246514586375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93144908355340164343057583 139717362533010246514586375)
  ·
    refine ⟨209576043799515369771879563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139717362533010246514586375 209576043799515369771879563)
    ·
      refine ⟨314364065699273054657819345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209576043799515369771879563 314364065699273054657819345)
      ·
        refine ⟨235773049274454790993364509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314364065699273054657819345 235773049274454790993364509)
        ·
          refine ⟨88414893477920546622511691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235773049274454790993364509 88414893477920546622511691)
          ·
            refine ⟨132622340216880819933767537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88414893477920546622511691 132622340216880819933767537)
            ·
              refine ⟨99466755162660614950325653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132622340216880819933767537 99466755162660614950325653)
              ·
                refine ⟨4662504148249716325796515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99466755162660614950325653 4662504148249716325796515)
                ·
                  refine ⟨6993756222374574488694773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4662504148249716325796515 6993756222374574488694773)
                  ·
                    refine ⟨655664645847616358315135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6993756222374574488694773 655664645847616358315135)
                    ·
                      rfl

theorem cell23_3830707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 5].length) (baseStart_3830707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830707 prefixEnd_3830707 := by exact prefixLift 3830707
  have htrace : WordTrace (prefixWord ++ tailWord_3830707) baseStart_3830707 baseEnd_3830707 := by
    simpa [prefixWord, tailWord_3830707, baseEnd_3830707] using wordTrace_append hprefix tailTrace_3830707
  have hstable : (prefixWord ++ tailWord_3830707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830707).length < 2 ^ (prefixWord ++ tailWord_3830707).sum := by decide
  have hdescent : baseEnd_3830707 < baseStart_3830707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830708 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3830708 : Nat := 118140960795 + 3830708 * 2 ^ 59
def prefixEnd_3830708 : Nat := 4983230072969 + 3 ^ 40 * 3830708 * 2
def baseEnd_3830708 : Nat := 1966994451023503571032901

theorem tailTrace_3830708 : CollatzResearch.WordTrace tailWord_3830708 prefixEnd_3830708 1966994451023503571032901 := by
  unfold tailWord_3830708
  simp only [CollatzResearch.WordTrace]
  refine ⟨69858699503003311842686389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93144932670671082456915185 69858699503003311842686389)
  ·
    refine ⟨6549253078406560485251849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69858699503003311842686389 6549253078406560485251849)
    ·
      refine ⟨4911939808804920363938887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6549253078406560485251849 4911939808804920363938887)
      ·
        refine ⟨7367909713207380545908331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4911939808804920363938887 7367909713207380545908331)
        ·
          refine ⟨11051864569811070818862497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7367909713207380545908331 11051864569811070818862497)
          ·
            refine ⟨8288898427358303114146873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11051864569811070818862497 8288898427358303114146873)
            ·
              refine ⟨6216673820518727335610155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8288898427358303114146873 6216673820518727335610155)
              ·
                refine ⟨9325010730778091003415233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6216673820518727335610155 9325010730778091003415233)
                ·
                  refine ⟨6993758048083568252561425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9325010730778091003415233 6993758048083568252561425)
                  ·
                    refine ⟨5245318536062676189421069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6993758048083568252561425 5245318536062676189421069)
                    ·
                      refine ⟨1966994451023503571032901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5245318536062676189421069 1966994451023503571032901)
                      ·
                        rfl

theorem cell23_3830708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3830708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830708 prefixEnd_3830708 := by exact prefixLift 3830708
  have htrace : WordTrace (prefixWord ++ tailWord_3830708) baseStart_3830708 baseEnd_3830708 := by
    simpa [prefixWord, tailWord_3830708, baseEnd_3830708] using wordTrace_append hprefix tailTrace_3830708
  have hstable : (prefixWord ++ tailWord_3830708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830708).length < 2 ^ (prefixWord ++ tailWord_3830708).sum := by decide
  have hdescent : baseEnd_3830708 < baseStart_3830708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830851 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 4, 2, 2]
def baseStart_3830851 : Nat := 118140960795 + 3830851 * 2 ^ 59
def prefixEnd_3830851 : Nat := 4983230072969 + 3 ^ 40 * 3830851 * 2
def baseEnd_3830851 : Nat := 1967067878757096511544743

theorem tailTrace_3830851 : CollatzResearch.WordTrace tailWord_3830851 prefixEnd_3830851 1967067878757096511544743 := by
  unfold tailWord_3830851
  simp only [CollatzResearch.WordTrace]
  refine ⟨139722614644488559107828407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93148409762992372738552271 139722614644488559107828407)
  ·
    refine ⟨209583921966732838661742611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139722614644488559107828407 209583921966732838661742611)
    ·
      refine ⟨314375882950099257992613917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209583921966732838661742611 314375882950099257992613917)
      ·
        refine ⟨117890956106287221747230219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314375882950099257992613917 117890956106287221747230219)
        ·
          refine ⟨176836434159430832620845329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117890956106287221747230219 176836434159430832620845329)
          ·
            refine ⟨132627325619573124465633997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176836434159430832620845329 132627325619573124465633997)
            ·
              refine ⟨49735247107339921674612749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132627325619573124465633997 49735247107339921674612749)
              ·
                refine ⟨18650717665252470627979781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49735247107339921674612749 18650717665252470627979781)
                ·
                  refine ⟨3497009562234838242746209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18650717665252470627979781 3497009562234838242746209)
                  ·
                    refine ⟨2622757171676128682059657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3497009562234838242746209 2622757171676128682059657)
                    ·
                      refine ⟨1967067878757096511544743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2622757171676128682059657 1967067878757096511544743)
                      ·
                        rfl

theorem cell23_3830851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 2, 2].length) (baseStart_3830851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830851 prefixEnd_3830851 := by exact prefixLift 3830851
  have htrace : WordTrace (prefixWord ++ tailWord_3830851) baseStart_3830851 baseEnd_3830851 := by
    simpa [prefixWord, tailWord_3830851, baseEnd_3830851] using wordTrace_append hprefix tailTrace_3830851
  have hstable : (prefixWord ++ tailWord_3830851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830851).length < 2 ^ (prefixWord ++ tailWord_3830851).sum := by decide
  have hdescent : baseEnd_3830851 < baseStart_3830851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830857 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 7]
def baseStart_3830857 : Nat := 118140960795 + 3830857 * 2 ^ 59
def prefixEnd_3830857 : Nat := 4983230072969 + 3 ^ 40 * 3830857 * 2
def baseEnd_3830857 : Nat := 218563439960113720896635

theorem tailTrace_3830857 : CollatzResearch.WordTrace tailWord_3830857 prefixEnd_3830857 218563439960113720896635 := by
  unfold tailWord_3830857
  simp only [CollatzResearch.WordTrace]
  refine ⟨139722833482466822132546825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93148555654977881421697883 139722833482466822132546825)
  ·
    refine ⟨104792125111850116599410119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139722833482466822132546825 104792125111850116599410119)
    ·
      refine ⟨157188187667775174899115179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104792125111850116599410119 157188187667775174899115179)
      ·
        refine ⟨235782281501662762348672769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157188187667775174899115179 235782281501662762348672769)
        ·
          refine ⟨176836711126247071761504577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235782281501662762348672769 176836711126247071761504577)
          ·
            refine ⟨132627533344685303821128433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176836711126247071761504577 132627533344685303821128433)
            ·
              refine ⟨99470650008513977865846325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132627533344685303821128433 99470650008513977865846325)
              ·
                refine ⟨9325373438298185424923093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99470650008513977865846325 9325373438298185424923093)
                ·
                  refine ⟨218563439960113720896635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9325373438298185424923093 218563439960113720896635)
                  ·
                    rfl

theorem cell23_3830857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 7].length) (baseStart_3830857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830857 prefixEnd_3830857 := by exact prefixLift 3830857
  have htrace : WordTrace (prefixWord ++ tailWord_3830857) baseStart_3830857 baseEnd_3830857 := by
    simpa [prefixWord, tailWord_3830857, baseEnd_3830857] using wordTrace_append hprefix tailTrace_3830857
  have hstable : (prefixWord ++ tailWord_3830857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830857).length < 2 ^ (prefixWord ++ tailWord_3830857).sum := by decide
  have hdescent : baseEnd_3830857 < baseStart_3830857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830884 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_3830884 : Nat := 118140960795 + 3830884 * 2 ^ 59
def prefixEnd_3830884 : Nat := 4983230072969 + 3 ^ 40 * 3830884 * 2
def baseEnd_3830884 : Nat := 1967084823618694882432091

theorem tailTrace_3830884 : CollatzResearch.WordTrace tailWord_3830884 prefixEnd_3830884 1967084823618694882432091 := by
  unfold tailWord_3830884
  simp only [CollatzResearch.WordTrace]
  refine ⟨69861909126684502871889853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93149212168912670495853137 69861909126684502871889853)
  ·
    refine ⟨26198215922506688576958695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69861909126684502871889853 26198215922506688576958695)
    ·
      refine ⟨39297323883760032865438043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26198215922506688576958695 39297323883760032865438043)
      ·
        refine ⟨58945985825640049298157065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39297323883760032865438043 58945985825640049298157065)
        ·
          refine ⟨44209489369230036973617799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58945985825640049298157065 44209489369230036973617799)
          ·
            refine ⟨66314234053845055460426699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44209489369230036973617799 66314234053845055460426699)
            ·
              refine ⟨99471351080767583190640049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66314234053845055460426699 99471351080767583190640049)
              ·
                refine ⟨74603513310575687392980037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99471351080767583190640049 74603513310575687392980037)
                ·
                  refine ⟨13988158745732941386183757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74603513310575687392980037 13988158745732941386183757)
                  ·
                    refine ⟨5245559529649853019818909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13988158745732941386183757 5245559529649853019818909)
                    ·
                      refine ⟨1967084823618694882432091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5245559529649853019818909 1967084823618694882432091)
                      ·
                        rfl

theorem cell23_3830884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_3830884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830884 prefixEnd_3830884 := by exact prefixLift 3830884
  have htrace : WordTrace (prefixWord ++ tailWord_3830884) baseStart_3830884 baseEnd_3830884 := by
    simpa [prefixWord, tailWord_3830884, baseEnd_3830884] using wordTrace_append hprefix tailTrace_3830884
  have hstable : (prefixWord ++ tailWord_3830884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830884).length < 2 ^ (prefixWord ++ tailWord_3830884).sum := by decide
  have hdescent : baseEnd_3830884 < baseStart_3830884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830904 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 2, 5]
def baseStart_3830904 : Nat := 118140960795 + 3830904 * 2 ^ 59
def prefixEnd_3830904 : Nat := 4983230072969 + 3 ^ 40 * 3830904 * 2
def baseEnd_3830904 : Nat := 655698364410594934727333

theorem tailTrace_3830904 : CollatzResearch.WordTrace tailWord_3830904 prefixEnd_3830904 655698364410594934727333 := by
  unfold tailWord_3830904
  simp only [CollatzResearch.WordTrace]
  refine ⟨69862273856648274579753883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93149698475531032773005177 69862273856648274579753883)
  ·
    refine ⟨104793410784972411869630825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69862273856648274579753883 104793410784972411869630825)
    ·
      refine ⟨78595058088729308902223119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104793410784972411869630825 78595058088729308902223119)
      ·
        refine ⟨117892587133093963353334679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78595058088729308902223119 117892587133093963353334679)
        ·
          refine ⟨176838880699640945030002019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117892587133093963353334679 176838880699640945030002019)
          ·
            refine ⟨265258321049461417545003029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176838880699640945030002019 265258321049461417545003029)
            ·
              refine ⟨12433983799193503947422017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 265258321049461417545003029 12433983799193503947422017)
              ·
                refine ⟨9325487849395127960566513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12433983799193503947422017 9325487849395127960566513)
                ·
                  refine ⟨6994115887046345970424885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9325487849395127960566513 6994115887046345970424885)
                  ·
                    refine ⟨655698364410594934727333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6994115887046345970424885 655698364410594934727333)
                    ·
                      rfl

theorem cell23_3830904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_3830904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830904 prefixEnd_3830904 := by exact prefixLift 3830904
  have htrace : WordTrace (prefixWord ++ tailWord_3830904) baseStart_3830904 baseEnd_3830904 := by
    simpa [prefixWord, tailWord_3830904, baseEnd_3830904] using wordTrace_append hprefix tailTrace_3830904
  have hstable : (prefixWord ++ tailWord_3830904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830904).length < 2 ^ (prefixWord ++ tailWord_3830904).sum := by decide
  have hdescent : baseEnd_3830904 < baseStart_3830904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830924 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_3830924 : Nat := 118140960795 + 3830924 * 2 ^ 59
def prefixEnd_3830924 : Nat := 4983230072969 + 3 ^ 40 * 3830924 * 2
def baseEnd_3830924 : Nat := 1967105362844874725931907

theorem tailTrace_3830924 : CollatzResearch.WordTrace tailWord_3830924 prefixEnd_3830924 1967105362844874725931907 := by
  unfold tailWord_3830924
  simp only [CollatzResearch.WordTrace]
  refine ⟨69862638586612046287617913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93150184782149395050157217 69862638586612046287617913)
  ·
    refine ⟨52396978939959034715713435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69862638586612046287617913 52396978939959034715713435)
    ·
      refine ⟨78595468409938552073570153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52396978939959034715713435 78595468409938552073570153)
      ·
        refine ⟨58946601307453914055177615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78595468409938552073570153 58946601307453914055177615)
        ·
          refine ⟨88419901961180871082766423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58946601307453914055177615 88419901961180871082766423)
          ·
            refine ⟨132629852941771306624149635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88419901961180871082766423 132629852941771306624149635)
            ·
              refine ⟨198944779412656959936224453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132629852941771306624149635 198944779412656959936224453)
              ·
                refine ⟨37302146139873179988042085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198944779412656959936224453 37302146139873179988042085)
                ·
                  refine ⟨6994152401226221247757891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37302146139873179988042085 6994152401226221247757891)
                  ·
                    refine ⟨10491228601839331871636837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6994152401226221247757891 10491228601839331871636837)
                    ·
                      refine ⟨1967105362844874725931907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10491228601839331871636837 1967105362844874725931907)
                      ·
                        rfl

theorem cell23_3830924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_3830924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830924 prefixEnd_3830924 := by exact prefixLift 3830924
  have htrace : WordTrace (prefixWord ++ tailWord_3830924) baseStart_3830924 baseEnd_3830924 := by
    simpa [prefixWord, tailWord_3830924, baseEnd_3830924] using wordTrace_append hprefix tailTrace_3830924
  have hstable : (prefixWord ++ tailWord_3830924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830924).length < 2 ^ (prefixWord ++ tailWord_3830924).sum := by decide
  have hdescent : baseEnd_3830924 < baseStart_3830924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830938 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 2, 5]
def baseStart_3830938 : Nat := 118140960795 + 3830938 * 2 ^ 59
def prefixEnd_3830938 : Nat := 4983230072969 + 3 ^ 40 * 3830938 * 2
def baseEnd_3830938 : Nat := 655704183858012557052281

theorem tailTrace_3830938 : CollatzResearch.WordTrace tailWord_3830938 prefixEnd_3830938 655704183858012557052281 := by
  unfold tailWord_3830938
  simp only [CollatzResearch.WordTrace]
  refine ⟨34931446948793343241561367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93150525196782248644163645 34931446948793343241561367)
  ·
    refine ⟨52397170423190014862342051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34931446948793343241561367 52397170423190014862342051)
    ·
      refine ⟨78595755634785022293513077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52397170423190014862342051 78595755634785022293513077)
      ·
        refine ⟨7368352090761095840016851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78595755634785022293513077 7368352090761095840016851)
        ·
          refine ⟨11052528136141643760025277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7368352090761095840016851 11052528136141643760025277)
          ·
            refine ⟨4144698051053116410009479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11052528136141643760025277 4144698051053116410009479)
            ·
              refine ⟨6217047076579674615014219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4144698051053116410009479 6217047076579674615014219)
              ·
                refine ⟨9325570614869511922521329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6217047076579674615014219 9325570614869511922521329)
                ·
                  refine ⟨6994177961152133941890997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9325570614869511922521329 6994177961152133941890997)
                  ·
                    refine ⟨655704183858012557052281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6994177961152133941890997 655704183858012557052281)
                    ·
                      rfl

theorem cell23_3830938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_3830938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830938 prefixEnd_3830938 := by exact prefixLift 3830938
  have htrace : WordTrace (prefixWord ++ tailWord_3830938) baseStart_3830938 baseEnd_3830938 := by
    simpa [prefixWord, tailWord_3830938, baseEnd_3830938] using wordTrace_append hprefix tailTrace_3830938
  have hstable : (prefixWord ++ tailWord_3830938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830938).length < 2 ^ (prefixWord ++ tailWord_3830938).sum := by decide
  have hdescent : baseEnd_3830938 < baseStart_3830938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830941 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_3830941 : Nat := 118140960795 + 3830941 * 2 ^ 59
def prefixEnd_3830941 : Nat := 4983230072969 + 3 ^ 40 * 3830941 * 2
def baseEnd_3830941 : Nat := 1967114092016001159419329

theorem tailTrace_3830941 : CollatzResearch.WordTrace tailWord_3830941 prefixEnd_3830941 1967114092016001159419329 := by
  unfold tailWord_3830941
  simp only [CollatzResearch.WordTrace]
  refine ⟨139725897214162504478604677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93150598142775002985736451 139725897214162504478604677)
  ·
    refine ⟨26198605727655469589738377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139725897214162504478604677 26198605727655469589738377)
    ·
      refine ⟨19648954295741602192303783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26198605727655469589738377 19648954295741602192303783)
      ·
        refine ⟨29473431443612403288455675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19648954295741602192303783 29473431443612403288455675)
        ·
          refine ⟨44210147165418604932683513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29473431443612403288455675 44210147165418604932683513)
          ·
            refine ⟨33157610374063953699512635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44210147165418604932683513 33157610374063953699512635)
            ·
              refine ⟨49736415561095930549268953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33157610374063953699512635 49736415561095930549268953)
              ·
                refine ⟨37302311670821947911951715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49736415561095930549268953 37302311670821947911951715)
                ·
                  refine ⟨55953467506232921867927573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37302311670821947911951715 55953467506232921867927573)
                  ·
                    refine ⟨2622818789354668212559105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55953467506232921867927573 2622818789354668212559105)
                    ·
                      refine ⟨1967114092016001159419329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2622818789354668212559105 1967114092016001159419329)
                      ·
                        rfl

theorem cell23_3830941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_3830941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830941 prefixEnd_3830941 := by exact prefixLift 3830941
  have htrace : WordTrace (prefixWord ++ tailWord_3830941) baseStart_3830941 baseEnd_3830941 := by
    simpa [prefixWord, tailWord_3830941, baseEnd_3830941] using wordTrace_append hprefix tailTrace_3830941
  have hstable : (prefixWord ++ tailWord_3830941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830941).length < 2 ^ (prefixWord ++ tailWord_3830941).sum := by decide
  have hdescent : baseEnd_3830941 < baseStart_3830941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830991 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 5, 1, 3]
def baseStart_3830991 : Nat := 118140960795 + 3830991 * 2 ^ 59
def prefixEnd_3830991 : Nat := 4983230072969 + 3 ^ 40 * 3830991 * 2
def baseEnd_3830991 : Nat := 1967139766048725963794099

theorem tailTrace_3830991 : CollatzResearch.WordTrace tailWord_3830991 prefixEnd_3830991 1967139766048725963794099 := by
  unfold tailWord_3830991
  simp only [CollatzResearch.WordTrace]
  refine ⟨139727720863981363017924827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93151813909320908678616551 139727720863981363017924827)
  ·
    refine ⟨209591581295972044526887241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139727720863981363017924827 209591581295972044526887241)
    ·
      refine ⟨157193685971979033395165431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209591581295972044526887241 157193685971979033395165431)
      ·
        refine ⟨235790528957968550092748147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157193685971979033395165431 235790528957968550092748147)
        ·
          refine ⟨353685793436952825139122221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235790528957968550092748147 353685793436952825139122221)
          ·
            refine ⟨132632172538857309427170833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353685793436952825139122221 132632172538857309427170833)
            ·
              refine ⟨99474129404142982070378125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132632172538857309427170833 99474129404142982070378125)
              ·
                refine ⟨37302798526553618276391797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99474129404142982070378125 37302798526553618276391797)
                ·
                  refine ⟨3497137361864401713411731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37302798526553618276391797 3497137361864401713411731)
                  ·
                    refine ⟨5245706042796602570117597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3497137361864401713411731 5245706042796602570117597)
                    ·
                      refine ⟨1967139766048725963794099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5245706042796602570117597 1967139766048725963794099)
                      ·
                        rfl

theorem cell23_3830991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 1, 3].length) (baseStart_3830991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3830991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3830991 prefixEnd_3830991 := by exact prefixLift 3830991
  have htrace : WordTrace (prefixWord ++ tailWord_3830991) baseStart_3830991 baseEnd_3830991 := by
    simpa [prefixWord, tailWord_3830991, baseEnd_3830991] using wordTrace_append hprefix tailTrace_3830991
  have hstable : (prefixWord ++ tailWord_3830991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830991).length < 2 ^ (prefixWord ++ tailWord_3830991).sum := by decide
  have hdescent : baseEnd_3830991 < baseStart_3830991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831018 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_3831018 : Nat := 118140960795 + 3831018 * 2 ^ 59
def prefixEnd_3831018 : Nat := 4983230072969 + 3 ^ 40 * 3831018 * 2
def baseEnd_3831018 : Nat := 1967153630026397358156475

theorem tailTrace_3831018 : CollatzResearch.WordTrace tailWord_3831018 prefixEnd_3831018 1967153630026397358156475 := by
  unfold tailWord_3831018
  simp only [CollatzResearch.WordTrace]
  refine ⟨34932176408720886657289427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93152470423255697752771805 34932176408720886657289427)
  ·
    refine ⟨52398264613081329985934141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34932176408720886657289427 52398264613081329985934141)
    ·
      refine ⟨19649349229905498744725303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52398264613081329985934141 19649349229905498744725303)
      ·
        refine ⟨29474023844858248117087955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19649349229905498744725303 29474023844858248117087955)
        ·
          refine ⟨44211035767287372175631933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29474023844858248117087955 44211035767287372175631933)
          ·
            refine ⟨16579138412732764565861975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44211035767287372175631933 16579138412732764565861975)
            ·
              refine ⟨24868707619099146848792963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16579138412732764565861975 24868707619099146848792963)
              ·
                refine ⟨37303061428648720273189445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24868707619099146848792963 37303061428648720273189445)
                ·
                  refine ⟨6994324017871635051223021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37303061428648720273189445 6994324017871635051223021)
                  ·
                    refine ⟨2622871506701863144208633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6994324017871635051223021 2622871506701863144208633)
                    ·
                      refine ⟨1967153630026397358156475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2622871506701863144208633 1967153630026397358156475)
                      ·
                        rfl

theorem cell23_3831018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_3831018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831018 prefixEnd_3831018 := by exact prefixLift 3831018
  have htrace : WordTrace (prefixWord ++ tailWord_3831018) baseStart_3831018 baseEnd_3831018 := by
    simpa [prefixWord, tailWord_3831018, baseEnd_3831018] using wordTrace_append hprefix tailTrace_3831018
  have hstable : (prefixWord ++ tailWord_3831018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831018).length < 2 ^ (prefixWord ++ tailWord_3831018).sum := by decide
  have hdescent : baseEnd_3831018 < baseStart_3831018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
