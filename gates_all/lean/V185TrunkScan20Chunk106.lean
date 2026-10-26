import V185TrunkScan20Chunk105

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_644432 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_644432 : Nat := 118140960795 + 644432 * 2 ^ 59
def prefixEnd_644432 : Nat := 4983230072969 + 3 ^ 40 * 644432 * 2
def baseEnd_644432 : Nat := 294136324567402569365615

theorem tailTrace_644432 : CollatzResearch.WordTrace tailWord_644432 prefixEnd_644432 294136324567402569365615 := by
  unfold tailWord_644432
  simp only [CollatzResearch.WordTrace]
  refine ⟨11752183000670199534183775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15669577334226932712245033 11752183000670199534183775)
  ·
    refine ⟨17628274501005299301275663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11752183000670199534183775 17628274501005299301275663)
    ·
      refine ⟨26442411751507948951913495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17628274501005299301275663 26442411751507948951913495)
      ·
        refine ⟨39663617627261923427870243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26442411751507948951913495 39663617627261923427870243)
        ·
          refine ⟨59495426440892885141805365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39663617627261923427870243 59495426440892885141805365)
          ·
            refine ⟨5577696228833707982044253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59495426440892885141805365 5577696228833707982044253)
            ·
              refine ⟨2091636085812640493266595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5577696228833707982044253 2091636085812640493266595)
              ·
                refine ⟨3137454128718960739899893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2091636085812640493266595 3137454128718960739899893)
                ·
                  refine ⟨294136324567402569365615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3137454128718960739899893 294136324567402569365615)
                  ·
                    rfl

theorem cell20_644432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_644432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644432 prefixEnd_644432 := by exact prefixLift 644432
  have htrace : WordTrace (prefixWord ++ tailWord_644432) baseStart_644432 baseEnd_644432 := by
    simpa [prefixWord, tailWord_644432, baseEnd_644432] using wordTrace_append hprefix tailTrace_644432
  have hstable : (prefixWord ++ tailWord_644432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644432).length < 2 ^ (prefixWord ++ tailWord_644432).sum := by decide
  have hdescent : baseEnd_644432 < baseStart_644432 := by decide
  rcases family_descends (prefixWord ++ tailWord_644432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644469 : List Nat := [1, 3, 4, 1, 3, 2, 1, 3, 2]
def baseStart_644469 : Nat := 118140960795 + 644469 * 2 ^ 59
def prefixEnd_644469 : Nat := 4983230072969 + 3 ^ 40 * 644469 * 2
def baseEnd_644469 : Nat := 294153212375594885132131

theorem tailTrace_644469 : CollatzResearch.WordTrace tailWord_644469 prefixEnd_644469 294153212375594885132131 := by
  unfold tailWord_644469
  simp only [CollatzResearch.WordTrace]
  refine ⟨23505715502206354387464461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15670477001470902924976307 23505715502206354387464461)
  ·
    refine ⟨8814643313327382895299173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23505715502206354387464461 8814643313327382895299173)
    ·
      refine ⟨1652745621248884292868595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8814643313327382895299173 1652745621248884292868595)
      ·
        refine ⟨2479118431873326439302893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1652745621248884292868595 2479118431873326439302893)
        ·
          refine ⟨929669411952497414738585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2479118431873326439302893 929669411952497414738585)
          ·
            refine ⟨697252058964373061053939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929669411952497414738585 697252058964373061053939)
            ·
              refine ⟨1045878088446559591580909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697252058964373061053939 1045878088446559591580909)
              ·
                refine ⟨392204283167459846842841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1045878088446559591580909 392204283167459846842841)
                ·
                  refine ⟨294153212375594885132131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392204283167459846842841 294153212375594885132131)
                  ·
                    rfl

theorem cell20_644469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_644469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644469 prefixEnd_644469 := by exact prefixLift 644469
  have htrace : WordTrace (prefixWord ++ tailWord_644469) baseStart_644469 baseEnd_644469 := by
    simpa [prefixWord, tailWord_644469, baseEnd_644469] using wordTrace_append hprefix tailTrace_644469
  have hstable : (prefixWord ++ tailWord_644469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644469).length < 2 ^ (prefixWord ++ tailWord_644469).sum := by decide
  have hdescent : baseEnd_644469 < baseStart_644469 := by decide
  rcases family_descends (prefixWord ++ tailWord_644469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644473 : List Nat := [1, 2, 1, 3, 2, 1, 5, 3, 2]
def baseStart_644473 : Nat := 118140960795 + 644473 * 2 ^ 59
def prefixEnd_644473 : Nat := 4983230072969 + 3 ^ 40 * 644473 * 2
def baseEnd_644473 : Nat := 294155038084588648998781

theorem tailTrace_644473 : CollatzResearch.WordTrace tailWord_644473 prefixEnd_644473 294155038084588648998781 := by
  unfold tailWord_644473
  simp only [CollatzResearch.WordTrace]
  refine ⟨23505861394191863070610073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15670574262794575380406715 23505861394191863070610073)
  ·
    refine ⟨17629396045643897302957555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23505861394191863070610073 17629396045643897302957555)
    ·
      refine ⟨26444094068465845954436333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17629396045643897302957555 26444094068465845954436333)
      ·
        refine ⟨9916535275674692232913625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26444094068465845954436333 9916535275674692232913625)
        ·
          refine ⟨7437401456756019174685219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9916535275674692232913625 7437401456756019174685219)
          ·
            refine ⟨11156102185134028762027829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7437401456756019174685219 11156102185134028762027829)
            ·
              refine ⟨1045884579856315196440109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11156102185134028762027829 1045884579856315196440109)
              ·
                refine ⟨392206717446118198665041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1045884579856315196440109 392206717446118198665041)
                ·
                  refine ⟨294155038084588648998781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392206717446118198665041 294155038084588648998781)
                  ·
                    rfl

theorem cell20_644473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 2].length) (baseStart_644473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644473 prefixEnd_644473 := by exact prefixLift 644473
  have htrace : WordTrace (prefixWord ++ tailWord_644473) baseStart_644473 baseEnd_644473 := by
    simpa [prefixWord, tailWord_644473, baseEnd_644473] using wordTrace_append hprefix tailTrace_644473
  have hstable : (prefixWord ++ tailWord_644473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644473).length < 2 ^ (prefixWord ++ tailWord_644473).sum := by decide
  have hdescent : baseEnd_644473 < baseStart_644473 := by decide
  rcases family_descends (prefixWord ++ tailWord_644473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644504 : List Nat := [2, 1, 2, 5, 2, 1, 1, 3, 3]
def baseStart_644504 : Nat := 118140960795 + 644504 * 2 ^ 59
def prefixEnd_644504 : Nat := 4983230072969 + 3 ^ 40 * 644504 * 2
def baseEnd_644504 : Nat := 294169187329290318965321

theorem tailTrace_644504 : CollatzResearch.WordTrace tailWord_644504 prefixEnd_644504 294169187329290318965321 := by
  unfold tailWord_644504
  simp only [CollatzResearch.WordTrace]
  refine ⟨11753496028539777682494283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15671328038053036909992377 11753496028539777682494283)
  ·
    refine ⟨17630244042809666523741425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11753496028539777682494283 17630244042809666523741425)
    ·
      refine ⟨13222683032107249892806069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17630244042809666523741425 13222683032107249892806069)
      ·
        refine ⟨1239626534260054677450569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13222683032107249892806069 1239626534260054677450569)
        ·
          refine ⟨929719900695041008087927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1239626534260054677450569 929719900695041008087927)
          ·
            refine ⟨1394579851042561512131891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929719900695041008087927 1394579851042561512131891)
            ·
              refine ⟨2091869776563842268197837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394579851042561512131891 2091869776563842268197837)
              ·
                refine ⟨784451166211440850574189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2091869776563842268197837 784451166211440850574189)
                ·
                  refine ⟨294169187329290318965321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784451166211440850574189 294169187329290318965321)
                  ·
                    rfl

theorem cell20_644504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_644504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644504 prefixEnd_644504 := by exact prefixLift 644504
  have htrace : WordTrace (prefixWord ++ tailWord_644504) baseStart_644504 baseEnd_644504 := by
    simpa [prefixWord, tailWord_644504, baseEnd_644504] using wordTrace_append hprefix tailTrace_644504
  have hstable : (prefixWord ++ tailWord_644504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644504).length < 2 ^ (prefixWord ++ tailWord_644504).sum := by decide
  have hdescent : baseEnd_644504 < baseStart_644504 := by decide
  rcases family_descends (prefixWord ++ tailWord_644504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644515 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 6]
def baseStart_644515 : Nat := 118140960795 + 644515 * 2 ^ 59
def prefixEnd_644515 : Nat := 4983230072969 + 3 ^ 40 * 644515 * 2
def baseEnd_644515 : Nat := 294174208029023169598609

theorem tailTrace_644515 : CollatzResearch.WordTrace tailWord_644515 prefixEnd_644515 294174208029023169598609 := by
  unfold tailWord_644515
  simp only [CollatzResearch.WordTrace]
  refine ⟨23507393260039704243638999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15671595506693136162425999 23507393260039704243638999)
  ·
    refine ⟨35261089890059556365458499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23507393260039704243638999 35261089890059556365458499)
    ·
      refine ⟨52891634835089334548187749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35261089890059556365458499 52891634835089334548187749)
      ·
        refine ⟨9917181531579250227785203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52891634835089334548187749 9917181531579250227785203)
        ·
          refine ⟨14875772297368875341677805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9917181531579250227785203 14875772297368875341677805)
          ·
            refine ⟨5578414611513328253129177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14875772297368875341677805 5578414611513328253129177)
            ·
              refine ⟨4183810958634996189846883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5578414611513328253129177 4183810958634996189846883)
              ·
                refine ⟨6275716437952494284770325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183810958634996189846883 6275716437952494284770325)
                ·
                  refine ⟨294174208029023169598609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6275716437952494284770325 294174208029023169598609)
                  ·
                    rfl

theorem cell20_644515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_644515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644515 prefixEnd_644515 := by exact prefixLift 644515
  have htrace : WordTrace (prefixWord ++ tailWord_644515) baseStart_644515 baseEnd_644515 := by
    simpa [prefixWord, tailWord_644515, baseEnd_644515] using wordTrace_append hprefix tailTrace_644515
  have hstable : (prefixWord ++ tailWord_644515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644515).length < 2 ^ (prefixWord ++ tailWord_644515).sum := by decide
  have hdescent : baseEnd_644515 < baseStart_644515 := by decide
  rcases family_descends (prefixWord ++ tailWord_644515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644553 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 4]
def baseStart_644553 : Nat := 118140960795 + 644553 * 2 ^ 59
def prefixEnd_644553 : Nat := 4983230072969 + 3 ^ 40 * 644553 * 2
def baseEnd_644553 : Nat := 294191552264463926331787

theorem tailTrace_644553 : CollatzResearch.WordTrace tailWord_644553 prefixEnd_644553 294191552264463926331787 := by
  unfold tailWord_644553
  simp only [CollatzResearch.WordTrace]
  refine ⟨23508779233902036733522313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15672519489268024489014875 23508779233902036733522313)
  ·
    refine ⟨17631584425426527550141735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23508779233902036733522313 17631584425426527550141735)
    ·
      refine ⟨26447376638139791325212603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17631584425426527550141735 26447376638139791325212603)
      ·
        refine ⟨39671064957209686987818905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26447376638139791325212603 39671064957209686987818905)
        ·
          refine ⟨29753298717907265240864179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39671064957209686987818905 29753298717907265240864179)
          ·
            refine ⟨44629948076860897861296269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29753298717907265240864179 44629948076860897861296269)
            ·
              refine ⟨16736230528822836697986101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44629948076860897861296269 16736230528822836697986101)
              ·
                refine ⟨1569021612077140940436197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16736230528822836697986101 1569021612077140940436197)
                ·
                  refine ⟨294191552264463926331787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569021612077140940436197 294191552264463926331787)
                  ·
                    rfl

theorem cell20_644553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_644553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644553 prefixEnd_644553 := by exact prefixLift 644553
  have htrace : WordTrace (prefixWord ++ tailWord_644553) baseStart_644553 baseEnd_644553 := by
    simpa [prefixWord, tailWord_644553, baseEnd_644553] using wordTrace_append hprefix tailTrace_644553
  have hstable : (prefixWord ++ tailWord_644553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644553).length < 2 ^ (prefixWord ++ tailWord_644553).sum := by decide
  have hdescent : baseEnd_644553 < baseStart_644553 := by decide
  rcases family_descends (prefixWord ++ tailWord_644553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644556 : List Nat := [2, 2, 1, 4, 2, 3, 1, 5]
def baseStart_644556 : Nat := 118140960795 + 644556 * 2 ^ 59
def prefixEnd_644556 : Nat := 4983230072969 + 3 ^ 40 * 644556 * 2
def baseEnd_644556 : Nat := 98064307182069749743925

theorem tailTrace_644556 : CollatzResearch.WordTrace tailWord_644556 prefixEnd_644556 98064307182069749743925 := by
  unfold tailWord_644556
  simp only [CollatzResearch.WordTrace]
  refine ⟨11754444326445584122940761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15672592435260778830587681 11754444326445584122940761)
  ·
    refine ⟨8815833244834188092205571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11754444326445584122940761 8815833244834188092205571)
    ·
      refine ⟨13223749867251282138308357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8815833244834188092205571 13223749867251282138308357)
      ·
        refine ⟨2479453100109615400932817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13223749867251282138308357 2479453100109615400932817)
        ·
          refine ⟨1859589825082211550699613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2479453100109615400932817 1859589825082211550699613)
          ·
            refine ⟨697346184405829331512355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1859589825082211550699613 697346184405829331512355)
            ·
              refine ⟨1046019276608743997268533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697346184405829331512355 1046019276608743997268533)
              ·
                refine ⟨98064307182069749743925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1046019276608743997268533 98064307182069749743925)
                ·
                  rfl

theorem cell20_644556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_644556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644556 prefixEnd_644556 := by exact prefixLift 644556
  have htrace : WordTrace (prefixWord ++ tailWord_644556) baseStart_644556 baseEnd_644556 := by
    simpa [prefixWord, tailWord_644556, baseEnd_644556] using wordTrace_append hprefix tailTrace_644556
  have hstable : (prefixWord ++ tailWord_644556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644556).length < 2 ^ (prefixWord ++ tailWord_644556).sum := by decide
  have hdescent : baseEnd_644556 < baseStart_644556 := by decide
  rcases family_descends (prefixWord ++ tailWord_644556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644570 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_644570 : Nat := 118140960795 + 644570 * 2 ^ 59
def prefixEnd_644570 : Nat := 4983230072969 + 3 ^ 40 * 644570 * 2
def baseEnd_644570 : Nat := 294199311527687422765051

theorem tailTrace_644570 : CollatzResearch.WordTrace tailWord_644570 prefixEnd_644570 294199311527687422765051 := by
  unfold tailWord_644570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5877349818710112159222791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15672932849893632424594109 5877349818710112159222791)
  ·
    refine ⟨8816024728065168238834187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5877349818710112159222791 8816024728065168238834187)
    ·
      refine ⟨13224037092097752358251281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8816024728065168238834187 13224037092097752358251281)
      ·
        refine ⟨9918027819073314268688461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13224037092097752358251281 9918027819073314268688461)
        ·
          refine ⟨3719260432152492850758173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9918027819073314268688461 3719260432152492850758173)
          ·
            refine ⟨1394722662057184819034315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3719260432152492850758173 1394722662057184819034315)
            ·
              refine ⟨2092083993085777228551473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394722662057184819034315 2092083993085777228551473)
              ·
                refine ⟨1569062994814332921413605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092083993085777228551473 1569062994814332921413605)
                ·
                  refine ⟨294199311527687422765051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569062994814332921413605 294199311527687422765051)
                  ·
                    rfl

theorem cell20_644570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_644570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644570 prefixEnd_644570 := by exact prefixLift 644570
  have htrace : WordTrace (prefixWord ++ tailWord_644570) baseStart_644570 baseEnd_644570 := by
    simpa [prefixWord, tailWord_644570, baseEnd_644570] using wordTrace_append hprefix tailTrace_644570
  have hstable : (prefixWord ++ tailWord_644570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644570).length < 2 ^ (prefixWord ++ tailWord_644570).sum := by decide
  have hdescent : baseEnd_644570 < baseStart_644570 := by decide
  rcases family_descends (prefixWord ++ tailWord_644570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644584 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_644584 : Nat := 118140960795 + 644584 * 2 ^ 59
def prefixEnd_644584 : Nat := 4983230072969 + 3 ^ 40 * 644584 * 2
def baseEnd_644584 : Nat := 294205701509165596298327

theorem tailTrace_644584 : CollatzResearch.WordTrace tailWord_644584 prefixEnd_644584 294205701509165596298327 := by
  unfold tailWord_644584
  simp only [CollatzResearch.WordTrace]
  refine ⟨11754954948394864513950403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15673273264526486018600537 11754954948394864513950403)
  ·
    refine ⟨17632432422592296770925605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11754954948394864513950403 17632432422592296770925605)
    ·
      refine ⟨3306081079236055644548551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17632432422592296770925605 3306081079236055644548551)
      ·
        refine ⟨4959121618854083466822827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3306081079236055644548551 4959121618854083466822827)
        ·
          refine ⟨7438682428281125200234241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4959121618854083466822827 7438682428281125200234241)
          ·
            refine ⟨5579011821210843900175681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7438682428281125200234241 5579011821210843900175681)
            ·
              refine ⟨4184258865908132925131761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5579011821210843900175681 4184258865908132925131761)
              ·
                refine ⟨3138194149431099693848821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4184258865908132925131761 3138194149431099693848821)
                ·
                  refine ⟨294205701509165596298327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3138194149431099693848821 294205701509165596298327)
                  ·
                    rfl

theorem cell20_644584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_644584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644584 prefixEnd_644584 := by exact prefixLift 644584
  have htrace : WordTrace (prefixWord ++ tailWord_644584) baseStart_644584 baseEnd_644584 := by
    simpa [prefixWord, tailWord_644584, baseEnd_644584] using wordTrace_append hprefix tailTrace_644584
  have hstable : (prefixWord ++ tailWord_644584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644584).length < 2 ^ (prefixWord ++ tailWord_644584).sum := by decide
  have hdescent : baseEnd_644584 < baseStart_644584 := by decide
  rcases family_descends (prefixWord ++ tailWord_644584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644597 : List Nat := [1, 3, 5, 1, 1, 3, 1, 2, 3]
def baseStart_644597 : Nat := 118140960795 + 644597 * 2 ^ 59
def prefixEnd_644597 : Nat := 4983230072969 + 3 ^ 40 * 644597 * 2
def baseEnd_644597 : Nat := 294211635063395328864941

theorem tailTrace_644597 : CollatzResearch.WordTrace tailWord_644597 prefixEnd_644597 294211635063395328864941 := by
  unfold tailWord_644597
  simp only [CollatzResearch.WordTrace]
  refine ⟨23510384045742632248124045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15673589363828421498749363 23510384045742632248124045)
  ·
    refine ⟨8816394017153487093046517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23510384045742632248124045 8816394017153487093046517)
    ·
      refine ⟨826536939108139414973111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8816394017153487093046517 826536939108139414973111)
      ·
        refine ⟨1239805408662209122459667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826536939108139414973111 1239805408662209122459667)
        ·
          refine ⟨1859708112993313683689501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239805408662209122459667 1859708112993313683689501)
          ·
            refine ⟨697390542372492631383563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1859708112993313683689501 697390542372492631383563)
            ·
              refine ⟨1046085813558738947075345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697390542372492631383563 1046085813558738947075345)
              ·
                refine ⟨784564360169054210306509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046085813558738947075345 784564360169054210306509)
                ·
                  refine ⟨294211635063395328864941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784564360169054210306509 294211635063395328864941)
                  ·
                    rfl

theorem cell20_644597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_644597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644597 prefixEnd_644597 := by exact prefixLift 644597
  have htrace : WordTrace (prefixWord ++ tailWord_644597) baseStart_644597 baseEnd_644597 := by
    simpa [prefixWord, tailWord_644597, baseEnd_644597] using wordTrace_append hprefix tailTrace_644597
  have hstable : (prefixWord ++ tailWord_644597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644597).length < 2 ^ (prefixWord ++ tailWord_644597).sum := by decide
  have hdescent : baseEnd_644597 < baseStart_644597 := by decide
  rcases family_descends (prefixWord ++ tailWord_644597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644618 : List Nat := [3, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_644618 : Nat := 118140960795 + 644618 * 2 ^ 59
def prefixEnd_644618 : Nat := 4983230072969 + 3 ^ 40 * 644618 * 2
def baseEnd_644618 : Nat := 294221220035612589164855

theorem tailTrace_644618 : CollatzResearch.WordTrace tailWord_644618 prefixEnd_644618 294221220035612589164855 := by
  unfold tailWord_644618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5877787494666638208659627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15674099985777701889759005 5877787494666638208659627)
  ·
    refine ⟨8816681241999957312989441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5877787494666638208659627 8816681241999957312989441)
    ·
      refine ⟨6612510931499967984742081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8816681241999957312989441 6612510931499967984742081)
      ·
        refine ⟨4959383198624975988556561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6612510931499967984742081 4959383198624975988556561)
        ·
          refine ⟨3719537398968731991417421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4959383198624975988556561 3719537398968731991417421)
          ·
            refine ⟨1394826524613274496781533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3719537398968731991417421 1394826524613274496781533)
            ·
              refine ⟨523059946729977936293075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1394826524613274496781533 523059946729977936293075)
              ·
                refine ⟨784589920094966904439613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523059946729977936293075 784589920094966904439613)
                ·
                  refine ⟨294221220035612589164855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784589920094966904439613 294221220035612589164855)
                  ·
                    rfl

theorem cell20_644618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_644618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644618 prefixEnd_644618 := by exact prefixLift 644618
  have htrace : WordTrace (prefixWord ++ tailWord_644618) baseStart_644618 baseEnd_644618 := by
    simpa [prefixWord, tailWord_644618, baseEnd_644618] using wordTrace_append hprefix tailTrace_644618
  have hstable : (prefixWord ++ tailWord_644618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644618).length < 2 ^ (prefixWord ++ tailWord_644618).sum := by decide
  have hdescent : baseEnd_644618 < baseStart_644618 := by decide
  rcases family_descends (prefixWord ++ tailWord_644618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644628 : List Nat := [2, 4, 3, 1, 2, 2, 2, 4]
def baseStart_644628 : Nat := 118140960795 + 644628 * 2 ^ 59
def prefixEnd_644628 : Nat := 4983230072969 + 3 ^ 40 * 644628 * 2
def baseEnd_644628 : Nat := 98075261436032332943827

theorem tailTrace_644628 : CollatzResearch.WordTrace tailWord_644628 prefixEnd_644628 98075261436032332943827 := by
  unfold tailWord_644628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11755757354315162271251269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15674343139086883028335025 11755757354315162271251269)
  ·
    refine ⟨2204204503934092925859613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11755757354315162271251269 2204204503934092925859613)
    ·
      refine ⟨826576688975284847197355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2204204503934092925859613 826576688975284847197355)
      ·
        refine ⟨1239865033462927270796033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826576688975284847197355 1239865033462927270796033)
        ·
          refine ⟨929898775097195453097025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1239865033462927270796033 929898775097195453097025)
          ·
            refine ⟨697424081322896589822769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929898775097195453097025 697424081322896589822769)
            ·
              refine ⟨523068060992172442367077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697424081322896589822769 523068060992172442367077)
              ·
                refine ⟨98075261436032332943827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523068060992172442367077 98075261436032332943827)
                ·
                  rfl

theorem cell20_644628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_644628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644628 prefixEnd_644628 := by exact prefixLift 644628
  have htrace : WordTrace (prefixWord ++ tailWord_644628) baseStart_644628 baseEnd_644628 := by
    simpa [prefixWord, tailWord_644628, baseEnd_644628] using wordTrace_append hprefix tailTrace_644628
  have hstable : (prefixWord ++ tailWord_644628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644628).length < 2 ^ (prefixWord ++ tailWord_644628).sum := by decide
  have hdescent : baseEnd_644628 < baseStart_644628 := by decide
  rcases family_descends (prefixWord ++ tailWord_644628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644718 : List Nat := [4, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_644718 : Nat := 118140960795 + 644718 * 2 ^ 59
def prefixEnd_644718 : Nat := 4983230072969 + 3 ^ 40 * 644718 * 2
def baseEnd_644718 : Nat := 294266862760456685831113

theorem tailTrace_644718 : CollatzResearch.WordTrace tailWord_644718 prefixEnd_644718 294266862760456685831113 := by
  unfold tailWord_644718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939349659788033739159851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15676531518869513275519205 2939349659788033739159851)
  ·
    refine ⟨4409024489682050608739777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2939349659788033739159851 4409024489682050608739777)
    ·
      refine ⟨3306768367261537956554833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4409024489682050608739777 3306768367261537956554833)
      ·
        refine ⟨2480076275446153467416125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3306768367261537956554833 2480076275446153467416125)
        ·
          refine ⟨930028603292307550281047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2480076275446153467416125 930028603292307550281047)
          ·
            refine ⟨1395042904938461325421571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930028603292307550281047 1395042904938461325421571)
            ·
              refine ⟨2092564357407691988132357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395042904938461325421571 2092564357407691988132357)
              ·
                refine ⟨392355817013942247774817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2092564357407691988132357 392355817013942247774817)
                ·
                  refine ⟨294266862760456685831113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392355817013942247774817 294266862760456685831113)
                  ·
                    rfl

theorem cell20_644718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_644718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644718 prefixEnd_644718 := by exact prefixLift 644718
  have htrace : WordTrace (prefixWord ++ tailWord_644718) baseStart_644718 baseEnd_644718 := by
    simpa [prefixWord, tailWord_644718, baseEnd_644718] using wordTrace_append hprefix tailTrace_644718
  have hstable : (prefixWord ++ tailWord_644718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644718).length < 2 ^ (prefixWord ++ tailWord_644718).sum := by decide
  have hdescent : baseEnd_644718 < baseStart_644718 := by decide
  rcases family_descends (prefixWord ++ tailWord_644718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644736 : List Nat := [2, 1, 1, 2, 1, 4, 1, 5, 3]
def baseStart_644736 : Nat := 118140960795 + 644736 * 2 ^ 59
def prefixEnd_644736 : Nat := 4983230072969 + 3 ^ 40 * 644736 * 2
def baseEnd_644736 : Nat := 294275078450928623231039

theorem tailTrace_644736 : CollatzResearch.WordTrace tailWord_644736 prefixEnd_644736 294275078450928623231039 := by
  unfold tailWord_644736
  simp only [CollatzResearch.WordTrace]
  refine ⟨11757726896119529493717031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15676969194826039324956041 11757726896119529493717031)
  ·
    refine ⟨17636590344179294240575547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11757726896119529493717031 17636590344179294240575547)
    ·
      refine ⟨26454885516268941360863321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17636590344179294240575547 26454885516268941360863321)
      ·
        refine ⟨19841164137201706020647491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26454885516268941360863321 19841164137201706020647491)
        ·
          refine ⟨29761746205802559030971237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19841164137201706020647491 29761746205802559030971237)
          ·
            refine ⟨5580327413587979818307107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29761746205802559030971237 5580327413587979818307107)
            ·
              refine ⟨8370491120381969727460661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5580327413587979818307107 8370491120381969727460661)
              ·
                refine ⟨784733542535809661949437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8370491120381969727460661 784733542535809661949437)
                ·
                  refine ⟨294275078450928623231039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784733542535809661949437 294275078450928623231039)
                  ·
                    rfl

theorem cell20_644736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_644736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644736 prefixEnd_644736 := by exact prefixLift 644736
  have htrace : WordTrace (prefixWord ++ tailWord_644736) baseStart_644736 baseEnd_644736 := by
    simpa [prefixWord, tailWord_644736, baseEnd_644736] using wordTrace_append hprefix tailTrace_644736
  have hstable : (prefixWord ++ tailWord_644736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644736).length < 2 ^ (prefixWord ++ tailWord_644736).sum := by decide
  have hdescent : baseEnd_644736 < baseStart_644736 := by decide
  rcases family_descends (prefixWord ++ tailWord_644736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644743 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 6]
def baseStart_644743 : Nat := 118140960795 + 644743 * 2 ^ 59
def prefixEnd_644743 : Nat := 4983230072969 + 3 ^ 40 * 644743 * 2
def baseEnd_644743 : Nat := 294278273441667709997677

theorem tailTrace_644743 : CollatzResearch.WordTrace tailWord_644743 prefixEnd_644743 294278273441667709997677 := by
  unfold tailWord_644743
  simp only [CollatzResearch.WordTrace]
  refine ⟨23515709103213699182938883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15677139402142466121959255 23515709103213699182938883)
  ·
    refine ⟨35273563654820548774408325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23515709103213699182938883 35273563654820548774408325)
    ·
      refine ⟨6613793185278852895201561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35273563654820548774408325 6613793185278852895201561)
      ·
        refine ⟨4960344888959139671401171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6613793185278852895201561 4960344888959139671401171)
        ·
          refine ⟨7440517333438709507101757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4960344888959139671401171 7440517333438709507101757)
          ·
            refine ⟨2790194000039516065163159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7440517333438709507101757 2790194000039516065163159)
            ·
              refine ⟨4185291000059274097744739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790194000039516065163159 4185291000059274097744739)
              ·
                refine ⟨6277936500088911146617109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4185291000059274097744739 6277936500088911146617109)
                ·
                  refine ⟨294278273441667709997677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6277936500088911146617109 294278273441667709997677)
                  ·
                    rfl

theorem cell20_644743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_644743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644743 prefixEnd_644743 := by exact prefixLift 644743
  have htrace : WordTrace (prefixWord ++ tailWord_644743) baseStart_644743 baseEnd_644743 := by
    simpa [prefixWord, tailWord_644743, baseEnd_644743] using wordTrace_append hprefix tailTrace_644743
  have hstable : (prefixWord ++ tailWord_644743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644743).length < 2 ^ (prefixWord ++ tailWord_644743).sum := by decide
  have hdescent : baseEnd_644743 < baseStart_644743 := by decide
  rcases family_descends (prefixWord ++ tailWord_644743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644746 : List Nat := [3, 1, 2, 3, 2, 2, 3, 4]
def baseStart_644746 : Nat := 118140960795 + 644746 * 2 ^ 59
def prefixEnd_644746 : Nat := 4983230072969 + 3 ^ 40 * 644746 * 2
def baseEnd_644746 : Nat := 98093214241137677632555

theorem tailTrace_644746 : CollatzResearch.WordTrace tailWord_644746 prefixEnd_644746 98093214241137677632555 := by
  unfold tailWord_644746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5878954630550707673824523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15677212348135220463532061 5878954630550707673824523)
  ·
    refine ⟨8818431945826061510736785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5878954630550707673824523 8818431945826061510736785)
    ·
      refine ⟨6613823959369546133052589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8818431945826061510736785 6613823959369546133052589)
      ·
        refine ⟨2480183984763579799894721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6613823959369546133052589 2480183984763579799894721)
        ·
          refine ⟨1860137988572684849921041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2480183984763579799894721 1860137988572684849921041)
          ·
            refine ⟨1395103491429513637440781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1860137988572684849921041 1395103491429513637440781)
            ·
              refine ⟨523163809286067614040293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1395103491429513637440781 523163809286067614040293)
              ·
                refine ⟨98093214241137677632555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523163809286067614040293 98093214241137677632555)
                ·
                  rfl

theorem cell20_644746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_644746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644746 prefixEnd_644746 := by exact prefixLift 644746
  have htrace : WordTrace (prefixWord ++ tailWord_644746) baseStart_644746 baseEnd_644746 := by
    simpa [prefixWord, tailWord_644746, baseEnd_644746] using wordTrace_append hprefix tailTrace_644746
  have hstable : (prefixWord ++ tailWord_644746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644746).length < 2 ^ (prefixWord ++ tailWord_644746).sum := by decide
  have hdescent : baseEnd_644746 < baseStart_644746 := by decide
  rcases family_descends (prefixWord ++ tailWord_644746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644770 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_644770 : Nat := 118140960795 + 644770 * 2 ^ 59
def prefixEnd_644770 : Nat := 4983230072969 + 3 ^ 40 * 644770 * 2
def baseEnd_644770 : Nat := 294290596977375616097567

theorem tailTrace_644770 : CollatzResearch.WordTrace tailWord_644770 prefixEnd_644770 294290596977375616097567 := by
  unfold tailWord_644770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5879173468528970698542941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15677795916077255196114509 5879173468528970698542941)
  ·
    refine ⟨2204690050698364011953603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5879173468528970698542941 2204690050698364011953603)
    ·
      refine ⟨3307035076047546017930405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2204690050698364011953603 3307035076047546017930405)
      ·
        refine ⟨620069076758914878361951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3307035076047546017930405 620069076758914878361951)
        ·
          refine ⟨930103615138372317542927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620069076758914878361951 930103615138372317542927)
          ·
            refine ⟨1395155422707558476314391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930103615138372317542927 1395155422707558476314391)
            ·
              refine ⟨2092733134061337714471587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395155422707558476314391 2092733134061337714471587)
              ·
                refine ⟨3139099701092006571707381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092733134061337714471587 3139099701092006571707381)
                ·
                  refine ⟨294290596977375616097567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3139099701092006571707381 294290596977375616097567)
                  ·
                    rfl

theorem cell20_644770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_644770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644770 prefixEnd_644770 := by exact prefixLift 644770
  have htrace : WordTrace (prefixWord ++ tailWord_644770) baseStart_644770 baseEnd_644770 := by
    simpa [prefixWord, tailWord_644770, baseEnd_644770] using wordTrace_append hprefix tailTrace_644770
  have hstable : (prefixWord ++ tailWord_644770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644770).length < 2 ^ (prefixWord ++ tailWord_644770).sum := by decide
  have hdescent : baseEnd_644770 < baseStart_644770 := by decide
  rcases family_descends (prefixWord ++ tailWord_644770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644798 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_644798 : Nat := 118140960795 + 644798 * 2 ^ 59
def prefixEnd_644798 : Nat := 4983230072969 + 3 ^ 40 * 644798 * 2
def baseEnd_644798 : Nat := 294303376940331963164119

theorem tailTrace_644798 : CollatzResearch.WordTrace tailWord_644798 prefixEnd_644798 294303376940331963164119 := by
  unfold tailWord_644798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939714389751805447023881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15678476745342962384127365 2939714389751805447023881)
  ·
    refine ⟨2204785792313854085267911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2939714389751805447023881 2204785792313854085267911)
    ·
      refine ⟨3307178688470781127901867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2204785792313854085267911 3307178688470781127901867)
      ·
        refine ⟨4960768032706171691852801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3307178688470781127901867 4960768032706171691852801)
        ·
          refine ⟨3720576024529628768889601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4960768032706171691852801 3720576024529628768889601)
          ·
            refine ⟨2790432018397221576667201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3720576024529628768889601 2790432018397221576667201)
            ·
              refine ⟨2092824013797916182500401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2790432018397221576667201 2092824013797916182500401)
              ·
                refine ⟨1569618010348437136875301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092824013797916182500401 1569618010348437136875301)
                ·
                  refine ⟨294303376940331963164119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569618010348437136875301 294303376940331963164119)
                  ·
                    rfl

theorem cell20_644798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_644798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644798 prefixEnd_644798 := by exact prefixLift 644798
  have htrace : WordTrace (prefixWord ++ tailWord_644798) baseStart_644798 baseEnd_644798 := by
    simpa [prefixWord, tailWord_644798, baseEnd_644798] using wordTrace_append hprefix tailTrace_644798
  have hstable : (prefixWord ++ tailWord_644798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644798).length < 2 ^ (prefixWord ++ tailWord_644798).sum := by decide
  have hdescent : baseEnd_644798 < baseStart_644798 := by decide
  rcases family_descends (prefixWord ++ tailWord_644798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644826 : List Nat := [3, 1, 1, 2, 2, 3, 8]
def baseStart_644826 : Nat := 118140960795 + 644826 * 2 ^ 59
def prefixEnd_644826 : Nat := 4983230072969 + 3 ^ 40 * 644826 * 2
def baseEnd_644826 : Nat := 32701795211476478914519

theorem tailTrace_644826 : CollatzResearch.WordTrace tailWord_644826 prefixEnd_644826 32701795211476478914519 := by
  unfold tailWord_644826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5879684090478251089552583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15679157574608669572140221 5879684090478251089552583)
  ·
    refine ⟨8819526135717376634328875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5879684090478251089552583 8819526135717376634328875)
    ·
      refine ⟨13229289203576064951493313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8819526135717376634328875 13229289203576064951493313)
      ·
        refine ⟨9921966902682048713619985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13229289203576064951493313 9921966902682048713619985)
        ·
          refine ⟨7441475177011536535214989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9921966902682048713619985 7441475177011536535214989)
          ·
            refine ⟨2790553191379326200705621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7441475177011536535214989 2790553191379326200705621)
            ·
              refine ⟨32701795211476478914519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2790553191379326200705621 32701795211476478914519)
              ·
                rfl

theorem cell20_644826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 8].length) (baseStart_644826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644826 prefixEnd_644826 := by exact prefixLift 644826
  have htrace : WordTrace (prefixWord ++ tailWord_644826) baseStart_644826 baseEnd_644826 := by
    simpa [prefixWord, tailWord_644826, baseEnd_644826] using wordTrace_append hprefix tailTrace_644826
  have hstable : (prefixWord ++ tailWord_644826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644826).length < 2 ^ (prefixWord ++ tailWord_644826).sum := by decide
  have hdescent : baseEnd_644826 < baseStart_644826 := by decide
  rcases family_descends (prefixWord ++ tailWord_644826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644877 : List Nat := [1, 7, 2, 1, 9]
def baseStart_644877 : Nat := 118140960795 + 644877 * 2 ^ 59
def prefixEnd_644877 : Nat := 4983230072969 + 3 ^ 40 * 644877 * 2
def baseEnd_644877 : Nat := 3633820181394553080623

theorem tailTrace_644877 : CollatzResearch.WordTrace tailWord_644877 prefixEnd_644877 3633820181394553080623 := by
  unfold tailWord_644877
  simp only [CollatzResearch.WordTrace]
  refine ⟨23520596484728240068316885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15680397656485493378877923 23520596484728240068316885)
  ·
    refine ⟨551263980110818126601177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23520596484728240068316885 551263980110818126601177)
    ·
      refine ⟨413447985083113594950883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 551263980110818126601177 413447985083113594950883)
      ·
        refine ⟨620171977624670392426325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413447985083113594950883 620171977624670392426325)
        ·
          refine ⟨3633820181394553080623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 620171977624670392426325 3633820181394553080623)
          ·
            rfl

theorem cell20_644877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 9].length) (baseStart_644877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644877 prefixEnd_644877 := by exact prefixLift 644877
  have htrace : WordTrace (prefixWord ++ tailWord_644877) baseStart_644877 baseEnd_644877 := by
    simpa [prefixWord, tailWord_644877, baseEnd_644877] using wordTrace_append hprefix tailTrace_644877
  have hstable : (prefixWord ++ tailWord_644877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644877).length < 2 ^ (prefixWord ++ tailWord_644877).sum := by decide
  have hdescent : baseEnd_644877 < baseStart_644877 := by decide
  rcases family_descends (prefixWord ++ tailWord_644877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644888 : List Nat := [2, 1, 2, 3, 1, 1, 3, 4, 3]
def baseStart_644888 : Nat := 118140960795 + 644888 * 2 ^ 59
def prefixEnd_644888 : Nat := 4983230072969 + 3 ^ 40 * 644888 * 2
def baseEnd_644888 : Nat := 294344455392691650163751

theorem tailTrace_644888 : CollatzResearch.WordTrace tailWord_644888 prefixEnd_644888 294344455392691650163751 := by
  unfold tailWord_644888
  simp only [CollatzResearch.WordTrace]
  refine ⟨11760498843844194473483659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15680665125125592631311545 11760498843844194473483659)
  ·
    refine ⟨17640748265766291710225489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11760498843844194473483659 17640748265766291710225489)
    ·
      refine ⟨13230561199324718782669117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17640748265766291710225489 13230561199324718782669117)
      ·
        refine ⟨4961460449746769543500919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13230561199324718782669117 4961460449746769543500919)
        ·
          refine ⟨7442190674620154315251379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4961460449746769543500919 7442190674620154315251379)
          ·
            refine ⟨11163286011930231472877069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7442190674620154315251379 11163286011930231472877069)
            ·
              refine ⟨4186232254473836802328901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11163286011930231472877069 4186232254473836802328901)
              ·
                refine ⟨784918547713844400436669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4186232254473836802328901 784918547713844400436669)
                ·
                  refine ⟨294344455392691650163751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784918547713844400436669 294344455392691650163751)
                  ·
                    rfl

theorem cell20_644888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_644888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644888 prefixEnd_644888 := by exact prefixLift 644888
  have htrace : WordTrace (prefixWord ++ tailWord_644888) baseStart_644888 baseEnd_644888 := by
    simpa [prefixWord, tailWord_644888, baseEnd_644888] using wordTrace_append hprefix tailTrace_644888
  have hstable : (prefixWord ++ tailWord_644888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644888).length < 2 ^ (prefixWord ++ tailWord_644888).sum := by decide
  have hdescent : baseEnd_644888 < baseStart_644888 := by decide
  rcases family_descends (prefixWord ++ tailWord_644888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644894 : List Nat := [4, 3, 2, 2, 1, 2, 1, 5]
def baseStart_644894 : Nat := 118140960795 + 644894 * 2 ^ 59
def prefixEnd_644894 : Nat := 4983230072969 + 3 ^ 40 * 644894 * 2
def baseEnd_644894 : Nat := 98115731318727431987909

theorem tailTrace_644894 : CollatzResearch.WordTrace tailWord_644894 prefixEnd_644894 98115731318727431987909 := by
  unfold tailWord_644894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940152065708331496460717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15680811017111101314457157 2940152065708331496460717)
  ·
    refine ⟨1102557024640624311172769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2940152065708331496460717 1102557024640624311172769)
    ·
      refine ⟨826917768480468233379577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1102557024640624311172769 826917768480468233379577)
      ·
        refine ⟨620188326360351175034683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 826917768480468233379577 620188326360351175034683)
        ·
          refine ⟨930282489540526762552025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620188326360351175034683 930282489540526762552025)
          ·
            refine ⟨697711867155395071914019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 930282489540526762552025 697711867155395071914019)
            ·
              refine ⟨1046567800733092607871029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697711867155395071914019 1046567800733092607871029)
              ·
                refine ⟨98115731318727431987909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1046567800733092607871029 98115731318727431987909)
                ·
                  rfl

theorem cell20_644894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_644894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644894 prefixEnd_644894 := by exact prefixLift 644894
  have htrace : WordTrace (prefixWord ++ tailWord_644894) baseStart_644894 baseEnd_644894 := by
    simpa [prefixWord, tailWord_644894, baseEnd_644894] using wordTrace_append hprefix tailTrace_644894
  have hstable : (prefixWord ++ tailWord_644894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644894).length < 2 ^ (prefixWord ++ tailWord_644894).sum := by decide
  have hdescent : baseEnd_644894 < baseStart_644894 := by decide
  rcases family_descends (prefixWord ++ tailWord_644894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644895 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 4]
def baseStart_644895 : Nat := 118140960795 + 644895 * 2 ^ 59
def prefixEnd_644895 : Nat := 4983230072969 + 3 ^ 40 * 644895 * 2
def baseEnd_644895 : Nat := 294347650383430736930389

theorem tailTrace_644895 : CollatzResearch.WordTrace tailWord_644895 prefixEnd_644895 294347650383430736930389 := by
  unfold tailWord_644895
  simp only [CollatzResearch.WordTrace]
  refine ⟨23521252998663029142472139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15680835332442019428314759 23521252998663029142472139)
  ·
    refine ⟨35281879497994543713708209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23521252998663029142472139 35281879497994543713708209)
    ·
      refine ⟨26461409623495907785281157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35281879497994543713708209 26461409623495907785281157)
      ·
        refine ⟨4961514304405482709740217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26461409623495907785281157 4961514304405482709740217)
        ·
          refine ⟨3721135728304112032305163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4961514304405482709740217 3721135728304112032305163)
          ·
            refine ⟨5581703592456168048457745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3721135728304112032305163 5581703592456168048457745)
            ·
              refine ⟨4186277694342126036343309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5581703592456168048457745 4186277694342126036343309)
              ·
                refine ⟨1569854135378297263628741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4186277694342126036343309 1569854135378297263628741)
                ·
                  refine ⟨294347650383430736930389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569854135378297263628741 294347650383430736930389)
                  ·
                    rfl

theorem cell20_644895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_644895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644895 prefixEnd_644895 := by exact prefixLift 644895
  have htrace : WordTrace (prefixWord ++ tailWord_644895) baseStart_644895 baseEnd_644895 := by
    simpa [prefixWord, tailWord_644895, baseEnd_644895] using wordTrace_append hprefix tailTrace_644895
  have hstable : (prefixWord ++ tailWord_644895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644895).length < 2 ^ (prefixWord ++ tailWord_644895).sum := by decide
  have hdescent : baseEnd_644895 < baseStart_644895 := by decide
  rcases family_descends (prefixWord ++ tailWord_644895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644970 : List Nat := [3, 1, 3, 4, 2, 1, 2, 4]
def baseStart_644970 : Nat := 118140960795 + 644970 * 2 ^ 59
def prefixEnd_644970 : Nat := 4983230072969 + 3 ^ 40 * 644970 * 2
def baseEnd_644970 : Nat := 98127294142354603143361

theorem tailTrace_644970 : CollatzResearch.WordTrace tailWord_644970 prefixEnd_644970 98127294142354603143361 := by
  unfold tailWord_644970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5880997118347829237863091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15682658982260877967634909 5880997118347829237863091)
  ·
    refine ⟨8821495677521743856794637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5880997118347829237863091 8821495677521743856794637)
    ·
      refine ⟨3308060879070653946297989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8821495677521743856794637 3308060879070653946297989)
      ·
        refine ⟨620261414825747614930873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3308060879070653946297989 620261414825747614930873)
        ·
          refine ⟨465196061119310711198155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620261414825747614930873 465196061119310711198155)
          ·
            refine ⟨697794091678966066797233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465196061119310711198155 697794091678966066797233)
            ·
              refine ⟨523345568759224550097925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697794091678966066797233 523345568759224550097925)
              ·
                refine ⟨98127294142354603143361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523345568759224550097925 98127294142354603143361)
                ·
                  rfl

theorem cell20_644970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_644970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644970 prefixEnd_644970 := by exact prefixLift 644970
  have htrace : WordTrace (prefixWord ++ tailWord_644970) baseStart_644970 baseEnd_644970 := by
    simpa [prefixWord, tailWord_644970, baseEnd_644970] using wordTrace_append hprefix tailTrace_644970
  have hstable : (prefixWord ++ tailWord_644970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644970).length < 2 ^ (prefixWord ++ tailWord_644970).sum := by decide
  have hdescent : baseEnd_644970 < baseStart_644970 := by decide
  rcases family_descends (prefixWord ++ tailWord_644970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644974 : List Nat := [4, 1, 2, 3, 1, 1, 4, 4]
def baseStart_644974 : Nat := 118140960795 + 644974 * 2 ^ 59
def prefixEnd_644974 : Nat := 4983230072969 + 3 ^ 40 * 644974 * 2
def baseEnd_644974 : Nat := 98127902712019191098911

theorem tailTrace_644974 : CollatzResearch.WordTrace tailWord_644974 prefixEnd_644974 98127902712019191098911 := by
  unfold tailWord_644974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940516795672103204324747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15682756243584550423065317 2940516795672103204324747)
  ·
    refine ⟨4410775193508154806487121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2940516795672103204324747 4410775193508154806487121)
    ·
      refine ⟨3308081395131116104865341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4410775193508154806487121 3308081395131116104865341)
      ·
        refine ⟨1240530523174168539324503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3308081395131116104865341 1240530523174168539324503)
        ·
          refine ⟨1860795784761252808986755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1240530523174168539324503 1860795784761252808986755)
          ·
            refine ⟨2791193677141879213480133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860795784761252808986755 2791193677141879213480133)
            ·
              refine ⟨523348814464102352527525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2791193677141879213480133 523348814464102352527525)
              ·
                refine ⟨98127902712019191098911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523348814464102352527525 98127902712019191098911)
                ·
                  rfl

theorem cell20_644974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_644974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644974 prefixEnd_644974 := by exact prefixLift 644974
  have htrace : WordTrace (prefixWord ++ tailWord_644974) baseStart_644974 baseEnd_644974 := by
    simpa [prefixWord, tailWord_644974, baseEnd_644974] using wordTrace_append hprefix tailTrace_644974
  have hstable : (prefixWord ++ tailWord_644974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644974).length < 2 ^ (prefixWord ++ tailWord_644974).sum := by decide
  have hdescent : baseEnd_644974 < baseStart_644974 := by decide
  rcases family_descends (prefixWord ++ tailWord_644974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644985 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 7]
def baseStart_644985 : Nat := 118140960795 + 644985 * 2 ^ 59
def prefixEnd_644985 : Nat := 4983230072969 + 3 ^ 40 * 644985 * 2
def baseEnd_644985 : Nat := 294388728835790423930021

theorem tailTrace_644985 : CollatzResearch.WordTrace tailWord_644985 prefixEnd_644985 294388728835790423930021 := by
  unfold tailWord_644985
  simp only [CollatzResearch.WordTrace]
  refine ⟨23524535568336974513248409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15683023712224649675498939 23524535568336974513248409)
  ·
    refine ⟨17643401676252730884936307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23524535568336974513248409 17643401676252730884936307)
    ·
      refine ⟨26465102514379096327404461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17643401676252730884936307 26465102514379096327404461)
      ·
        refine ⟨9924413442892161122776673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26465102514379096327404461 9924413442892161122776673)
        ·
          refine ⟨7443310082169120842082505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9924413442892161122776673 7443310082169120842082505)
          ·
            refine ⟨5582482561626840631561879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7443310082169120842082505 5582482561626840631561879)
            ·
              refine ⟨8373723842440260947342819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5582482561626840631561879 8373723842440260947342819)
              ·
                refine ⟨12560585763660391421014229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8373723842440260947342819 12560585763660391421014229)
                ·
                  refine ⟨294388728835790423930021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12560585763660391421014229 294388728835790423930021)
                  ·
                    rfl

theorem cell20_644985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_644985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644985 prefixEnd_644985 := by exact prefixLift 644985
  have htrace : WordTrace (prefixWord ++ tailWord_644985) baseStart_644985 baseEnd_644985 := by
    simpa [prefixWord, tailWord_644985, baseEnd_644985] using wordTrace_append hprefix tailTrace_644985
  have hstable : (prefixWord ++ tailWord_644985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644985).length < 2 ^ (prefixWord ++ tailWord_644985).sum := by decide
  have hdescent : baseEnd_644985 < baseStart_644985 := by decide
  rcases family_descends (prefixWord ++ tailWord_644985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645009 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 4]
def baseStart_645009 : Nat := 118140960795 + 645009 * 2 ^ 59
def prefixEnd_645009 : Nat := 4983230072969 + 3 ^ 40 * 645009 * 2
def baseEnd_645009 : Nat := 294399683089753007129923

theorem tailTrace_645009 : CollatzResearch.WordTrace tailWord_645009 prefixEnd_645009 294399683089753007129923 := by
  unfold tailWord_645009
  simp only [CollatzResearch.WordTrace]
  refine ⟨23525410920250026612122081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15683607280166684408081387 23525410920250026612122081)
  ·
    refine ⟨17644058190187519959091561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23525410920250026612122081 17644058190187519959091561)
    ·
      refine ⟨13233043642640639969318671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17644058190187519959091561 13233043642640639969318671)
      ·
        refine ⟨19849565463960959953978007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13233043642640639969318671 19849565463960959953978007)
        ·
          refine ⟨29774348195941439930967011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19849565463960959953978007 29774348195941439930967011)
          ·
            refine ⟨44661522293912159896450517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29774348195941439930967011 44661522293912159896450517)
            ·
              refine ⟨1046754428763566247573059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 44661522293912159896450517 1046754428763566247573059)
              ·
                refine ⟨1570131643145349371359589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046754428763566247573059 1570131643145349371359589)
                ·
                  refine ⟨294399683089753007129923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1570131643145349371359589 294399683089753007129923)
                  ·
                    rfl

theorem cell20_645009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_645009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645009 prefixEnd_645009 := by exact prefixLift 645009
  have htrace : WordTrace (prefixWord ++ tailWord_645009) baseStart_645009 baseEnd_645009 := by
    simpa [prefixWord, tailWord_645009, baseEnd_645009] using wordTrace_append hprefix tailTrace_645009
  have hstable : (prefixWord ++ tailWord_645009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645009).length < 2 ^ (prefixWord ++ tailWord_645009).sum := by decide
  have hdescent : baseEnd_645009 < baseStart_645009 := by decide
  rcases family_descends (prefixWord ++ tailWord_645009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645054 : List Nat := [4, 2, 1, 1, 1, 11]
def baseStart_645054 : Nat := 118140960795 + 645054 * 2 ^ 59
def prefixEnd_645054 : Nat := 4983230072969 + 3 ^ 40 * 645054 * 2
def baseEnd_645054 : Nat := 10904452678367883356657

theorem tailTrace_645054 : CollatzResearch.WordTrace tailWord_645054 prefixEnd_645054 10904452678367883356657 := by
  unfold tailWord_645054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940881525635874912188777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15684701470057999531673477 2940881525635874912188777)
  ·
    refine ⟨2205661144226906184141583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2940881525635874912188777 2205661144226906184141583)
    ·
      refine ⟨3308491716340359276212375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2205661144226906184141583 3308491716340359276212375)
      ·
        refine ⟨4962737574510538914318563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3308491716340359276212375 4962737574510538914318563)
        ·
          refine ⟨7444106361765808371477845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4962737574510538914318563 7444106361765808371477845)
          ·
            refine ⟨10904452678367883356657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7444106361765808371477845 10904452678367883356657)
            ·
              rfl

theorem cell20_645054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 11].length) (baseStart_645054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645054 prefixEnd_645054 := by exact prefixLift 645054
  have htrace : WordTrace (prefixWord ++ tailWord_645054) baseStart_645054 baseEnd_645054 := by
    simpa [prefixWord, tailWord_645054, baseEnd_645054] using wordTrace_append hprefix tailTrace_645054
  have hstable : (prefixWord ++ tailWord_645054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645054).length < 2 ^ (prefixWord ++ tailWord_645054).sum := by decide
  have hdescent : baseEnd_645054 < baseStart_645054 := by decide
  rcases family_descends (prefixWord ++ tailWord_645054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645084 : List Nat := [2, 2, 6, 1, 1, 1, 3, 4]
def baseStart_645084 : Nat := 118140960795 + 645084 * 2 ^ 59
def prefixEnd_645084 : Nat := 4983230072969 + 3 ^ 40 * 645084 * 2
def baseEnd_645084 : Nat := 98144638377795359876539

theorem tailTrace_645084 : CollatzResearch.WordTrace tailWord_645084 prefixEnd_645084 98144638377795359876539 := by
  unfold tailWord_645084
  simp only [CollatzResearch.WordTrace]
  refine ⟨11764073197489157210551153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15685430929985542947401537 11764073197489157210551153)
  ·
    refine ⟨8823054898116867907913365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11764073197489157210551153 8823054898116867907913365)
    ·
      refine ⟨413580698349228183183439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8823054898116867907913365 413580698349228183183439)
      ·
        refine ⟨620371047523842274775159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413580698349228183183439 620371047523842274775159)
        ·
          refine ⟨930556571285763412162739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620371047523842274775159 930556571285763412162739)
          ·
            refine ⟨1395834856928645118244109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930556571285763412162739 1395834856928645118244109)
            ·
              refine ⟨523438071348241919341541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1395834856928645118244109 523438071348241919341541)
              ·
                refine ⟨98144638377795359876539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523438071348241919341541 98144638377795359876539)
                ·
                  rfl

theorem cell20_645084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_645084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645084 prefixEnd_645084 := by exact prefixLift 645084
  have htrace : WordTrace (prefixWord ++ tailWord_645084) baseStart_645084 baseEnd_645084 := by
    simpa [prefixWord, tailWord_645084, baseEnd_645084] using wordTrace_append hprefix tailTrace_645084
  have hstable : (prefixWord ++ tailWord_645084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645084).length < 2 ^ (prefixWord ++ tailWord_645084).sum := by decide
  have hdescent : baseEnd_645084 < baseStart_645084 := by decide
  rcases family_descends (prefixWord ++ tailWord_645084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645143 : List Nat := [1, 1, 3, 5, 3, 1, 2, 4]
def baseStart_645143 : Nat := 118140960795 + 645143 * 2 ^ 59
def prefixEnd_645143 : Nat := 4983230072969 + 3 ^ 40 * 645143 * 2
def baseEnd_645143 : Nat := 98153614780348032220903

theorem tailTrace_645143 : CollatzResearch.WordTrace tailWord_645143 prefixEnd_645143 98153614780348032220903 := by
  unfold tailWord_645143
  simp only [CollatzResearch.WordTrace]
  refine ⟨23530298301764567497500083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15686865534509711665000055 23530298301764567497500083)
  ·
    refine ⟨35295447452646851246250125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23530298301764567497500083 35295447452646851246250125)
    ·
      refine ⟨13235792794742569217343797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35295447452646851246250125 13235792794742569217343797)
      ·
        refine ⟨1240855574507115864125981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13235792794742569217343797 1240855574507115864125981)
        ·
          refine ⟨465320840440168449047243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1240855574507115864125981 465320840440168449047243)
          ·
            refine ⟨697981260660252673570865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465320840440168449047243 697981260660252673570865)
            ·
              refine ⟨523485945495189505178149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697981260660252673570865 523485945495189505178149)
              ·
                refine ⟨98153614780348032220903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523485945495189505178149 98153614780348032220903)
                ·
                  rfl

theorem cell20_645143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 4].length) (baseStart_645143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645143 prefixEnd_645143 := by exact prefixLift 645143
  have htrace : WordTrace (prefixWord ++ tailWord_645143) baseStart_645143 baseEnd_645143 := by
    simpa [prefixWord, tailWord_645143, baseEnd_645143] using wordTrace_append hprefix tailTrace_645143
  have hstable : (prefixWord ++ tailWord_645143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645143).length < 2 ^ (prefixWord ++ tailWord_645143).sum := by decide
  have hdescent : baseEnd_645143 < baseStart_645143 := by decide
  rcases family_descends (prefixWord ++ tailWord_645143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645157 : List Nat := [1, 3, 1, 2, 2, 5, 1, 3, 2]
def baseStart_645157 : Nat := 118140960795 + 645157 * 2 ^ 59
def prefixEnd_645157 : Nat := 4983230072969 + 3 ^ 40 * 645157 * 2
def baseEnd_645157 : Nat := 294467234322522270195985

theorem tailTrace_645157 : CollatzResearch.WordTrace tailWord_645157 prefixEnd_645157 294467234322522270195985 := by
  unfold tailWord_645157
  simp only [CollatzResearch.WordTrace]
  refine ⟨23530808923713847888509725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15687205949142565259006483 23530808923713847888509725)
  ·
    refine ⟨8824053346392692958191147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23530808923713847888509725 8824053346392692958191147)
    ·
      refine ⟨13236080019589039437286721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8824053346392692958191147 13236080019589039437286721)
      ·
        refine ⟨9927060014691779577965041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13236080019589039437286721 9927060014691779577965041)
        ·
          refine ⟨7445295011018834683473781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9927060014691779577965041 7445295011018834683473781)
          ·
            refine ⟨697996407283015751575667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7445295011018834683473781 697996407283015751575667)
            ·
              refine ⟨1046994610924523627363501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697996407283015751575667 1046994610924523627363501)
              ·
                refine ⟨392622979096696360261313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1046994610924523627363501 392622979096696360261313)
                ·
                  refine ⟨294467234322522270195985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392622979096696360261313 294467234322522270195985)
                  ·
                    rfl

theorem cell20_645157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_645157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645157 prefixEnd_645157 := by exact prefixLift 645157
  have htrace : WordTrace (prefixWord ++ tailWord_645157) baseStart_645157 baseEnd_645157 := by
    simpa [prefixWord, tailWord_645157, baseEnd_645157] using wordTrace_append hprefix tailTrace_645157
  have hstable : (prefixWord ++ tailWord_645157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645157).length < 2 ^ (prefixWord ++ tailWord_645157).sum := by decide
  have hdescent : baseEnd_645157 < baseStart_645157 := by decide
  rcases family_descends (prefixWord ++ tailWord_645157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645168 : List Nat := [2, 1, 1, 1, 2, 7, 6]
def baseStart_645168 : Nat := 118140960795 + 645168 * 2 ^ 59
def prefixEnd_645168 : Nat := 4983230072969 + 3 ^ 40 * 645168 * 2
def baseEnd_645168 : Nat := 32719139446917235647697

theorem tailTrace_645168 : CollatzResearch.WordTrace tailWord_645168 prefixEnd_645168 32719139446917235647697 := by
  unfold tailWord_645168
  simp only [CollatzResearch.WordTrace]
  refine ⟨11765605063336998383580079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15687473417782664511440105 11765605063336998383580079)
  ·
    refine ⟨17648407595005497575370119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11765605063336998383580079 17648407595005497575370119)
    ·
      refine ⟨26472611392508246363055179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17648407595005497575370119 26472611392508246363055179)
      ·
        refine ⟨39708917088762369544582769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26472611392508246363055179 39708917088762369544582769)
        ·
          refine ⟨29781687816571777158437077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39708917088762369544582769 29781687816571777158437077)
          ·
            refine ⟨698008308200901027150869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29781687816571777158437077 698008308200901027150869)
            ·
              refine ⟨32719139446917235647697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 698008308200901027150869 32719139446917235647697)
              ·
                rfl

theorem cell20_645168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 6].length) (baseStart_645168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645168 prefixEnd_645168 := by exact prefixLift 645168
  have htrace : WordTrace (prefixWord ++ tailWord_645168) baseStart_645168 baseEnd_645168 := by
    simpa [prefixWord, tailWord_645168, baseEnd_645168] using wordTrace_append hprefix tailTrace_645168
  have hstable : (prefixWord ++ tailWord_645168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645168).length < 2 ^ (prefixWord ++ tailWord_645168).sum := by decide
  have hdescent : baseEnd_645168 < baseStart_645168 := by decide
  rcases family_descends (prefixWord ++ tailWord_645168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645174 : List Nat := [5, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_645174 : Nat := 118140960795 + 645174 * 2 ^ 59
def prefixEnd_645174 : Nat := 4983230072969 + 3 ^ 40 * 645174 * 2
def baseEnd_645174 : Nat := 294474993585745766629249

theorem tailTrace_645174 : CollatzResearch.WordTrace tailWord_645174 prefixEnd_645174 294474993585745766629249 := by
  unfold tailWord_645174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1470714310290766236992411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15687619309768173194585717 1470714310290766236992411)
  ·
    refine ⟨2206071465436149355488617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1470714310290766236992411 2206071465436149355488617)
    ·
      refine ⟨1654553599077112016616463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2206071465436149355488617 1654553599077112016616463)
      ·
        refine ⟨2481830398615668024924695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1654553599077112016616463 2481830398615668024924695)
        ·
          refine ⟨3722745597923502037387043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481830398615668024924695 3722745597923502037387043)
          ·
            refine ⟨5584118396885253056080565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722745597923502037387043 5584118396885253056080565)
            ·
              refine ⟨523511099707992474007553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5584118396885253056080565 523511099707992474007553)
              ·
                refine ⟨392633324780994355505665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523511099707992474007553 392633324780994355505665)
                ·
                  refine ⟨294474993585745766629249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392633324780994355505665 294474993585745766629249)
                  ·
                    rfl

theorem cell20_645174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_645174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645174 prefixEnd_645174 := by exact prefixLift 645174
  have htrace : WordTrace (prefixWord ++ tailWord_645174) baseStart_645174 baseEnd_645174 := by
    simpa [prefixWord, tailWord_645174, baseEnd_645174] using wordTrace_append hprefix tailTrace_645174
  have hstable : (prefixWord ++ tailWord_645174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645174).length < 2 ^ (prefixWord ++ tailWord_645174).sum := by decide
  have hdescent : baseEnd_645174 < baseStart_645174 := by decide
  rcases family_descends (prefixWord ++ tailWord_645174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645175 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 5]
def baseStart_645175 : Nat := 118140960795 + 645175 * 2 ^ 59
def prefixEnd_645175 : Nat := 4983230072969 + 3 ^ 40 * 645175 * 2
def baseEnd_645175 : Nat := 294475450012994207595911

theorem tailTrace_645175 : CollatzResearch.WordTrace tailWord_645175 prefixEnd_645175 294475450012994207595911 := by
  unfold tailWord_645175
  simp only [CollatzResearch.WordTrace]
  refine ⟨23531465437648636962664979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15687643625099091308443319 23531465437648636962664979)
  ·
    refine ⟨35297198156472955443997469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23531465437648636962664979 35297198156472955443997469)
    ·
      refine ⟨13236449308677358291499051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35297198156472955443997469 13236449308677358291499051)
      ·
        refine ⟨19854673963016037437248577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13236449308677358291499051 19854673963016037437248577)
        ·
          refine ⟨14891005472262028077936433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19854673963016037437248577 14891005472262028077936433)
          ·
            refine ⟨11168254104196521058452325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14891005472262028077936433 11168254104196521058452325)
            ·
              refine ⟨2094047644536847698459811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11168254104196521058452325 2094047644536847698459811)
              ·
                refine ⟨3141071466805271547689717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094047644536847698459811 3141071466805271547689717)
                ·
                  refine ⟨294475450012994207595911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3141071466805271547689717 294475450012994207595911)
                  ·
                    rfl

theorem cell20_645175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_645175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645175 prefixEnd_645175 := by exact prefixLift 645175
  have htrace : WordTrace (prefixWord ++ tailWord_645175) baseStart_645175 baseEnd_645175 := by
    simpa [prefixWord, tailWord_645175, baseEnd_645175] using wordTrace_append hprefix tailTrace_645175
  have hstable : (prefixWord ++ tailWord_645175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645175).length < 2 ^ (prefixWord ++ tailWord_645175).sum := by decide
  have hdescent : baseEnd_645175 < baseStart_645175 := by decide
  rcases family_descends (prefixWord ++ tailWord_645175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645185 : List Nat := [1, 2, 5, 1, 2, 2, 2, 5]
def baseStart_645185 : Nat := 118140960795 + 645185 * 2 ^ 59
def prefixEnd_645185 : Nat := 4983230072969 + 3 ^ 40 * 645185 * 2
def baseEnd_645185 : Nat := 98160004761826205754179

theorem tailTrace_645185 : CollatzResearch.WordTrace tailWord_645185 prefixEnd_645185 98160004761826205754179 := by
  unfold tailWord_645185
  simp only [CollatzResearch.WordTrace]
  refine ⟨23531830167612408670529009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15687886778408272447019339 23531830167612408670529009)
  ·
    refine ⟨17648872625709306502896757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23531830167612408670529009 17648872625709306502896757)
    ·
      refine ⟨1654581808660247484646571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17648872625709306502896757 1654581808660247484646571)
      ·
        refine ⟨2481872712990371226969857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1654581808660247484646571 2481872712990371226969857)
        ·
          refine ⟨1861404534742778420227393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2481872712990371226969857 1861404534742778420227393)
          ·
            refine ⟨1396053401057083815170545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1861404534742778420227393 1396053401057083815170545)
            ·
              refine ⟨1047040050792812861377909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1396053401057083815170545 1047040050792812861377909)
              ·
                refine ⟨98160004761826205754179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1047040050792812861377909 98160004761826205754179)
                ·
                  rfl

theorem cell20_645185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_645185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645185 prefixEnd_645185 := by exact prefixLift 645185
  have htrace : WordTrace (prefixWord ++ tailWord_645185) baseStart_645185 baseEnd_645185 := by
    simpa [prefixWord, tailWord_645185, baseEnd_645185] using wordTrace_append hprefix tailTrace_645185
  have hstable : (prefixWord ++ tailWord_645185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645185).length < 2 ^ (prefixWord ++ tailWord_645185).sum := by decide
  have hdescent : baseEnd_645185 < baseStart_645185 := by decide
  rcases family_descends (prefixWord ++ tailWord_645185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645244 : List Nat := [2, 2, 2, 1, 1, 4, 3, 5]
def baseStart_645244 : Nat := 118140960795 + 645244 * 2 ^ 59
def prefixEnd_645244 : Nat := 4983230072969 + 3 ^ 40 * 645244 * 2
def baseEnd_645244 : Nat := 98168981164378878098543

theorem tailTrace_645244 : CollatzResearch.WordTrace tailWord_645244 prefixEnd_645244 98168981164378878098543 := by
  unfold tailWord_645244
  simp only [CollatzResearch.WordTrace]
  refine ⟨11766991037199330873463393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15689321382932441164617857 11766991037199330873463393)
  ·
    refine ⟨8825243277899498155097545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11766991037199330873463393 8825243277899498155097545)
    ·
      refine ⟨6618932458424623616323159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8825243277899498155097545 6618932458424623616323159)
      ·
        refine ⟨9928398687636935424484739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6618932458424623616323159 9928398687636935424484739)
        ·
          refine ⟨14892598031455403136727109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9928398687636935424484739 14892598031455403136727109)
          ·
            refine ⟨2792362130897888088136333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14892598031455403136727109 2792362130897888088136333)
            ·
              refine ⟨1047135799086708033051125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2792362130897888088136333 1047135799086708033051125)
              ·
                refine ⟨98168981164378878098543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1047135799086708033051125 98168981164378878098543)
                ·
                  rfl

theorem cell20_645244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_645244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645244 prefixEnd_645244 := by exact prefixLift 645244
  have htrace : WordTrace (prefixWord ++ tailWord_645244) baseStart_645244 baseEnd_645244 := by
    simpa [prefixWord, tailWord_645244, baseEnd_645244] using wordTrace_append hprefix tailTrace_645244
  have hstable : (prefixWord ++ tailWord_645244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645244).length < 2 ^ (prefixWord ++ tailWord_645244).sum := by decide
  have hdescent : baseEnd_645244 < baseStart_645244 := by decide
  rcases family_descends (prefixWord ++ tailWord_645244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645271 : List Nat := [1, 1, 3, 3, 4, 1, 2, 3, 2]
def baseStart_645271 : Nat := 118140960795 + 645271 * 2 ^ 59
def prefixEnd_645271 : Nat := 4983230072969 + 3 ^ 40 * 645271 * 2
def baseEnd_645271 : Nat := 294519267028844540395519

theorem tailTrace_645271 : CollatzResearch.WordTrace tailWord_645271 prefixEnd_645271 294519267028844540395519 := by
  unfold tailWord_645271
  simp only [CollatzResearch.WordTrace]
  refine ⟨23534966845300845358159667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15689977896867230238773111 23534966845300845358159667)
  ·
    refine ⟨35302450267951268037239501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23534966845300845358159667 35302450267951268037239501)
    ·
      refine ⟨13238418850481725513964813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35302450267951268037239501 13238418850481725513964813)
      ·
        refine ⟨4964407068930647067736805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13238418850481725513964813 4964407068930647067736805)
        ·
          refine ⟨930826325424496325200651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4964407068930647067736805 930826325424496325200651)
          ·
            refine ⟨1396239488136744487800977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930826325424496325200651 1396239488136744487800977)
            ·
              refine ⟨1047179616102558365850733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1396239488136744487800977 1047179616102558365850733)
              ·
                refine ⟨392692356038459387194025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1047179616102558365850733 392692356038459387194025)
                ·
                  refine ⟨294519267028844540395519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392692356038459387194025 294519267028844540395519)
                  ·
                    rfl

theorem cell20_645271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 2].length) (baseStart_645271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645271 prefixEnd_645271 := by exact prefixLift 645271
  have htrace : WordTrace (prefixWord ++ tailWord_645271) baseStart_645271 baseEnd_645271 := by
    simpa [prefixWord, tailWord_645271, baseEnd_645271] using wordTrace_append hprefix tailTrace_645271
  have hstable : (prefixWord ++ tailWord_645271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645271).length < 2 ^ (prefixWord ++ tailWord_645271).sum := by decide
  have hdescent : baseEnd_645271 < baseStart_645271 := by decide
  rcases family_descends (prefixWord ++ tailWord_645271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645316 : List Nat := [2, 3, 3, 1, 2, 3, 2, 4]
def baseStart_645316 : Nat := 118140960795 + 645316 * 2 ^ 59
def prefixEnd_645316 : Nat := 4983230072969 + 3 ^ 40 * 645316 * 2
def baseEnd_645316 : Nat := 98179935418341461298445

theorem tailTrace_645316 : CollatzResearch.WordTrace tailWord_645316 prefixEnd_645316 98179935418341461298445 := by
  unfold tailWord_645316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11768304065068909021773901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15691072086758545362365201 11768304065068909021773901)
  ·
    refine ⟨4413114024400840883165213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11768304065068909021773901 4413114024400840883165213)
    ·
      refine ⟨1654917759150315331186955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4413114024400840883165213 1654917759150315331186955)
      ·
        refine ⟨2482376638725472996780433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1654917759150315331186955 2482376638725472996780433)
        ·
          refine ⟨1861782479044104747585325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2482376638725472996780433 1861782479044104747585325)
          ·
            refine ⟨698168429641539280344497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1861782479044104747585325 698168429641539280344497)
            ·
              refine ⟨523626322231154460258373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698168429641539280344497 523626322231154460258373)
              ·
                refine ⟨98179935418341461298445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523626322231154460258373 98179935418341461298445)
                ·
                  rfl

theorem cell20_645316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_645316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645316 prefixEnd_645316 := by exact prefixLift 645316
  have htrace : WordTrace (prefixWord ++ tailWord_645316) baseStart_645316 baseEnd_645316 := by
    simpa [prefixWord, tailWord_645316, baseEnd_645316] using wordTrace_append hprefix tailTrace_645316
  have hstable : (prefixWord ++ tailWord_645316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645316).length < 2 ^ (prefixWord ++ tailWord_645316).sum := by decide
  have hdescent : baseEnd_645316 < baseStart_645316 := by decide
  rcases family_descends (prefixWord ++ tailWord_645316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645347 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 4]
def baseStart_645347 : Nat := 118140960795 + 645347 * 2 ^ 59
def prefixEnd_645347 : Nat := 4983230072969 + 3 ^ 40 * 645347 * 2
def baseEnd_645347 : Nat := 294553955499726053861875

theorem tailTrace_645347 : CollatzResearch.WordTrace tailWord_645347 prefixEnd_645347 294553955499726053861875 := by
  unfold tailWord_645347
  simp only [CollatzResearch.WordTrace]
  refine ⟨23537738793025510337926295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15691825862017006891950863 23537738793025510337926295)
  ·
    refine ⟨35306608189538265506889443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23537738793025510337926295 35306608189538265506889443)
    ·
      refine ⟨52959912284307398260334165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35306608189538265506889443 52959912284307398260334165)
      ·
        refine ⟨620623972081727323363291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 52959912284307398260334165 620623972081727323363291)
        ·
          refine ⟨930935958122590985044937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620623972081727323363291 930935958122590985044937)
          ·
            refine ⟨698201968591943238783703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 930935958122590985044937 698201968591943238783703)
            ·
              refine ⟨1047302952887914858175555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698201968591943238783703 1047302952887914858175555)
              ·
                refine ⟨1570954429331872287263333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047302952887914858175555 1570954429331872287263333)
                ·
                  refine ⟨294553955499726053861875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1570954429331872287263333 294553955499726053861875)
                  ·
                    rfl

theorem cell20_645347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 4].length) (baseStart_645347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645347 prefixEnd_645347 := by exact prefixLift 645347
  have htrace : WordTrace (prefixWord ++ tailWord_645347) baseStart_645347 baseEnd_645347 := by
    simpa [prefixWord, tailWord_645347, baseEnd_645347] using wordTrace_append hprefix tailTrace_645347
  have hstable : (prefixWord ++ tailWord_645347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645347).length < 2 ^ (prefixWord ++ tailWord_645347).sum := by decide
  have hdescent : baseEnd_645347 < baseStart_645347 := by decide
  rcases family_descends (prefixWord ++ tailWord_645347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645357 : List Nat := [1, 5, 1, 2, 4, 1, 2, 1, 3]
def baseStart_645357 : Nat := 118140960795 + 645357 * 2 ^ 59
def prefixEnd_645357 : Nat := 4983230072969 + 3 ^ 40 * 645357 * 2
def baseEnd_645357 : Nat := 294558519772210463528501

theorem tailTrace_645357 : CollatzResearch.WordTrace tailWord_645357 prefixEnd_645357 294558519772210463528501 := by
  unfold tailWord_645357
  simp only [CollatzResearch.WordTrace]
  refine ⟨23538103522989282045790325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15692069015326188030526883 23538103522989282045790325)
  ·
    refine ⟨2206697205280245191792843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23538103522989282045790325 2206697205280245191792843)
    ·
      refine ⟨3310045807920367787689265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2206697205280245191792843 3310045807920367787689265)
      ·
        refine ⟨2482534355940275840766949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3310045807920367787689265 2482534355940275840766949)
        ·
          refine ⟨465475191738801720143803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2482534355940275840766949 465475191738801720143803)
          ·
            refine ⟨698212787608202580215705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465475191738801720143803 698212787608202580215705)
            ·
              refine ⟨523659590706151935161779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698212787608202580215705 523659590706151935161779)
              ·
                refine ⟨785489386059227902742669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523659590706151935161779 785489386059227902742669)
                ·
                  refine ⟨294558519772210463528501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785489386059227902742669 294558519772210463528501)
                  ·
                    rfl

theorem cell20_645357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_645357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645357 prefixEnd_645357 := by exact prefixLift 645357
  have htrace : WordTrace (prefixWord ++ tailWord_645357) baseStart_645357 baseEnd_645357 := by
    simpa [prefixWord, tailWord_645357, baseEnd_645357] using wordTrace_append hprefix tailTrace_645357
  have hstable : (prefixWord ++ tailWord_645357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645357).length < 2 ^ (prefixWord ++ tailWord_645357).sum := by decide
  have hdescent : baseEnd_645357 < baseStart_645357 := by decide
  rcases family_descends (prefixWord ++ tailWord_645357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645379 : List Nat := [1, 1, 1, 3, 2, 3, 1, 8]
def baseStart_645379 : Nat := 118140960795 + 645379 * 2 ^ 59
def prefixEnd_645379 : Nat := 4983230072969 + 3 ^ 40 * 645379 * 2
def baseEnd_645379 : Nat := 98189520390558721598359

theorem tailTrace_645379 : CollatzResearch.WordTrace tailWord_645379 prefixEnd_645379 98189520390558721598359 := by
  unfold tailWord_645379
  simp only [CollatzResearch.WordTrace]
  refine ⟨23538905928909579803091191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15692603952606386535394127 23538905928909579803091191)
  ·
    refine ⟨35308358893364369704636787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23538905928909579803091191 35308358893364369704636787)
    ·
      refine ⟨52962538340046554556955181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35308358893364369704636787 52962538340046554556955181)
      ·
        refine ⟨19860951877517457958858193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52962538340046554556955181 19860951877517457958858193)
        ·
          refine ⟨14895713908138093469143645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19860951877517457958858193 14895713908138093469143645)
          ·
            refine ⟨5585892715551785050928867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14895713908138093469143645 5585892715551785050928867)
            ·
              refine ⟨8378839073327677576393301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585892715551785050928867 8378839073327677576393301)
              ·
                refine ⟨98189520390558721598359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8378839073327677576393301 98189520390558721598359)
                ·
                  rfl

theorem cell20_645379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_645379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645379 prefixEnd_645379 := by exact prefixLift 645379
  have htrace : WordTrace (prefixWord ++ tailWord_645379) baseStart_645379 baseEnd_645379 := by
    simpa [prefixWord, tailWord_645379, baseEnd_645379] using wordTrace_append hprefix tailTrace_645379
  have hstable : (prefixWord ++ tailWord_645379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645379).length < 2 ^ (prefixWord ++ tailWord_645379).sum := by decide
  have hdescent : baseEnd_645379 < baseStart_645379 := by decide
  rcases family_descends (prefixWord ++ tailWord_645379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645402 : List Nat := [3, 1, 1, 3, 4, 2, 2, 2, 2]
def baseStart_645402 : Nat := 118140960795 + 645402 * 2 ^ 59
def prefixEnd_645402 : Nat := 4983230072969 + 3 ^ 40 * 645402 * 2
def baseEnd_645402 : Nat := 294579058998390307028317

theorem tailTrace_645402 : CollatzResearch.WordTrace tailWord_645402 prefixEnd_645402 294579058998390307028317 := by
  unfold tailWord_645402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5884936201956563682794615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15693163205217503154118973 5884936201956563682794615)
  ·
    refine ⟨8827404302934845524191923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5884936201956563682794615 8827404302934845524191923)
    ·
      refine ⟨13241106454402268286287885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8827404302934845524191923 13241106454402268286287885)
      ·
        refine ⟨4965414920400850607357957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13241106454402268286287885 4965414920400850607357957)
        ·
          refine ⟨931015297575159488879617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4965414920400850607357957 931015297575159488879617)
          ·
            refine ⟨698261473181369616659713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931015297575159488879617 698261473181369616659713)
            ·
              refine ⟨523696104886027212494785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698261473181369616659713 523696104886027212494785)
              ·
                refine ⟨392772078664520409371089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523696104886027212494785 392772078664520409371089)
                ·
                  refine ⟨294579058998390307028317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392772078664520409371089 294579058998390307028317)
                  ·
                    rfl

theorem cell20_645402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_645402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645402 prefixEnd_645402 := by exact prefixLift 645402
  have htrace : WordTrace (prefixWord ++ tailWord_645402) baseStart_645402 baseEnd_645402 := by
    simpa [prefixWord, tailWord_645402, baseEnd_645402] using wordTrace_append hprefix tailTrace_645402
  have hstable : (prefixWord ++ tailWord_645402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645402).length < 2 ^ (prefixWord ++ tailWord_645402).sum := by decide
  have hdescent : baseEnd_645402 < baseStart_645402 := by decide
  rcases family_descends (prefixWord ++ tailWord_645402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645403 : List Nat := [1, 1, 1, 1, 1, 1, 7, 4, 3]
def baseStart_645403 : Nat := 118140960795 + 645403 * 2 ^ 59
def prefixEnd_645403 : Nat := 4983230072969 + 3 ^ 40 * 645403 * 2
def baseEnd_645403 : Nat := 294579515425638747994979

theorem tailTrace_645403 : CollatzResearch.WordTrace tailWord_645403 prefixEnd_645403 294579515425638747994979 := by
  unfold tailWord_645403
  simp only [CollatzResearch.WordTrace]
  refine ⟨23539781280822631901964863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15693187520548421267976575 23539781280822631901964863)
  ·
    refine ⟨35309671921233947852947295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23539781280822631901964863 35309671921233947852947295)
    ·
      refine ⟨52964507881850921779420943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35309671921233947852947295 52964507881850921779420943)
      ·
        refine ⟨79446761822776382669131415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52964507881850921779420943 79446761822776382669131415)
        ·
          refine ⟨119170142734164574003697123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79446761822776382669131415 119170142734164574003697123)
          ·
            refine ⟨178755214101246861005545685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119170142734164574003697123 178755214101246861005545685)
            ·
              refine ⟨4189575330497973304817477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 178755214101246861005545685 4189575330497973304817477)
              ·
                refine ⟨785545374468369994653277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4189575330497973304817477 785545374468369994653277)
                ·
                  refine ⟨294579515425638747994979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785545374468369994653277 294579515425638747994979)
                  ·
                    rfl

theorem cell20_645403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 3].length) (baseStart_645403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645403 prefixEnd_645403 := by exact prefixLift 645403
  have htrace : WordTrace (prefixWord ++ tailWord_645403) baseStart_645403 baseEnd_645403 := by
    simpa [prefixWord, tailWord_645403, baseEnd_645403] using wordTrace_append hprefix tailTrace_645403
  have hstable : (prefixWord ++ tailWord_645403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645403).length < 2 ^ (prefixWord ++ tailWord_645403).sum := by decide
  have hdescent : baseEnd_645403 < baseStart_645403 := by decide
  rcases family_descends (prefixWord ++ tailWord_645403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645413 : List Nat := [1, 3, 1, 2, 5, 2, 1, 5]
def baseStart_645413 : Nat := 118140960795 + 645413 * 2 ^ 59
def prefixEnd_645413 : Nat := 4983230072969 + 3 ^ 40 * 645413 * 2
def baseEnd_645413 : Nat := 98194693232707719220535

theorem tailTrace_645413 : CollatzResearch.WordTrace tailWord_645413 prefixEnd_645413 98194693232707719220535 := by
  unfold tailWord_645413
  simp only [CollatzResearch.WordTrace]
  refine ⟨23540146010786403609828893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15693430673857602406552595 23540146010786403609828893)
  ·
    refine ⟨8827554754044901353685835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23540146010786403609828893 8827554754044901353685835)
    ·
      refine ⟨13241332131067352030528753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8827554754044901353685835 13241332131067352030528753)
      ·
        refine ⟨9930999098300514022896565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13241332131067352030528753 9930999098300514022896565)
        ·
          refine ⟨931031165465673189646553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9930999098300514022896565 931031165465673189646553)
          ·
            refine ⟨698273374099254892234915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931031165465673189646553 698273374099254892234915)
            ·
              refine ⟨1047410061148882338352373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698273374099254892234915 1047410061148882338352373)
              ·
                refine ⟨98194693232707719220535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1047410061148882338352373 98194693232707719220535)
                ·
                  rfl

theorem cell20_645413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 5].length) (baseStart_645413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645413 prefixEnd_645413 := by exact prefixLift 645413
  have htrace : WordTrace (prefixWord ++ tailWord_645413) baseStart_645413 baseEnd_645413 := by
    simpa [prefixWord, tailWord_645413, baseEnd_645413] using wordTrace_append hprefix tailTrace_645413
  have hstable : (prefixWord ++ tailWord_645413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645413).length < 2 ^ (prefixWord ++ tailWord_645413).sum := by decide
  have hdescent : baseEnd_645413 < baseStart_645413 := by decide
  rcases family_descends (prefixWord ++ tailWord_645413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645458 : List Nat := [3, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_645458 : Nat := 118140960795 + 645458 * 2 ^ 59
def prefixEnd_645458 : Nat := 4983230072969 + 3 ^ 40 * 645458 * 2
def baseEnd_645458 : Nat := 294604618924303001161421

theorem tailTrace_645458 : CollatzResearch.WordTrace tailWord_645458 prefixEnd_645458 294604618924303001161421 := by
  unfold tailWord_645458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5885446823905844073804257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15694524863748917530144685 5885446823905844073804257)
  ·
    refine ⟨4414085117929383055353193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5885446823905844073804257 4414085117929383055353193)
    ·
      refine ⟨3310563838447037291514895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4414085117929383055353193 3310563838447037291514895)
      ·
        refine ⟨4965845757670555937272343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3310563838447037291514895 4965845757670555937272343)
        ·
          refine ⟨7448768636505833905908515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4965845757670555937272343 7448768636505833905908515)
          ·
            refine ⟨11173152954758750858862773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7448768636505833905908515 11173152954758750858862773)
            ·
              refine ⟨1047483089508632893018385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11173152954758750858862773 1047483089508632893018385)
              ·
                refine ⟨785612317131474669763789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1047483089508632893018385 785612317131474669763789)
                ·
                  refine ⟨294604618924303001161421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785612317131474669763789 294604618924303001161421)
                  ·
                    rfl

theorem cell20_645458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_645458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645458 prefixEnd_645458 := by exact prefixLift 645458
  have htrace : WordTrace (prefixWord ++ tailWord_645458) baseStart_645458 baseEnd_645458 := by
    simpa [prefixWord, tailWord_645458, baseEnd_645458] using wordTrace_append hprefix tailTrace_645458
  have hstable : (prefixWord ++ tailWord_645458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645458).length < 2 ^ (prefixWord ++ tailWord_645458).sum := by decide
  have hdescent : baseEnd_645458 < baseStart_645458 := by decide
  rcases family_descends (prefixWord ++ tailWord_645458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645506 : List Nat := [3, 4, 2, 1, 2, 2, 6]
def baseStart_645506 : Nat := 118140960795 + 645506 * 2 ^ 59
def prefixEnd_645506 : Nat := 4983230072969 + 3 ^ 40 * 645506 * 2
def baseEnd_645506 : Nat := 32736280825803129729025

theorem tailTrace_645506 : CollatzResearch.WordTrace tailWord_645506 prefixEnd_645506 32736280825803129729025 := by
  unfold tailWord_645506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5885884499862370123241093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15695691999632986995309581 5885884499862370123241093)
  ·
    refine ⟨1103603343724194398107705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5885884499862370123241093 1103603343724194398107705)
    ·
      refine ⟨827702507793145798580779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1103603343724194398107705 827702507793145798580779)
      ·
        refine ⟨1241553761689718697871169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827702507793145798580779 1241553761689718697871169)
        ·
          refine ⟨931165321267289023403377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1241553761689718697871169 931165321267289023403377)
          ·
            refine ⟨698373990950466767552533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931165321267289023403377 698373990950466767552533)
            ·
              refine ⟨32736280825803129729025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 698373990950466767552533 32736280825803129729025)
              ·
                rfl

theorem cell20_645506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 6].length) (baseStart_645506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645506 prefixEnd_645506 := by exact prefixLift 645506
  have htrace : WordTrace (prefixWord ++ tailWord_645506) baseStart_645506 baseEnd_645506 := by
    simpa [prefixWord, tailWord_645506, baseEnd_645506] using wordTrace_append hprefix tailTrace_645506
  have hstable : (prefixWord ++ tailWord_645506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645506).length < 2 ^ (prefixWord ++ tailWord_645506).sum := by decide
  have hdescent : baseEnd_645506 < baseStart_645506 := by decide
  rcases family_descends (prefixWord ++ tailWord_645506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645575 : List Nat := [1, 1, 4, 1, 1, 6, 2, 2, 2]
def baseStart_645575 : Nat := 118140960795 + 645575 * 2 ^ 59
def prefixEnd_645575 : Nat := 4983230072969 + 3 ^ 40 * 645575 * 2
def baseEnd_645575 : Nat := 294658020912370594260943

theorem tailTrace_645575 : CollatzResearch.WordTrace tailWord_645575 prefixEnd_645575 294658020912370594260943 := by
  unfold tailWord_645575
  simp only [CollatzResearch.WordTrace]
  refine ⟨23546054636199505277226179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15697369757466336851484119 23546054636199505277226179)
  ·
    refine ⟨35319081954299257915839269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23546054636199505277226179 35319081954299257915839269)
    ·
      refine ⟨6622327866431110859219863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35319081954299257915839269 6622327866431110859219863)
      ·
        refine ⟨9933491799646666288829795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6622327866431110859219863 9933491799646666288829795)
        ·
          refine ⟨14900237699469999433244693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9933491799646666288829795 14900237699469999433244693)
          ·
            refine ⟨698448642162656223433345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14900237699469999433244693 698448642162656223433345)
            ·
              refine ⟨523836481621992167575009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698448642162656223433345 523836481621992167575009)
              ·
                refine ⟨392877361216494125681257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523836481621992167575009 392877361216494125681257)
                ·
                  refine ⟨294658020912370594260943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392877361216494125681257 294658020912370594260943)
                  ·
                    rfl

theorem cell20_645575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 2].length) (baseStart_645575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645575 prefixEnd_645575 := by exact prefixLift 645575
  have htrace : WordTrace (prefixWord ++ tailWord_645575) baseStart_645575 baseEnd_645575 := by
    simpa [prefixWord, tailWord_645575, baseEnd_645575] using wordTrace_append hprefix tailTrace_645575
  have hstable : (prefixWord ++ tailWord_645575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645575).length < 2 ^ (prefixWord ++ tailWord_645575).sum := by decide
  have hdescent : baseEnd_645575 < baseStart_645575 := by decide
  rcases family_descends (prefixWord ++ tailWord_645575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645593 : List Nat := [1, 2, 1, 2, 4, 1, 1, 5, 3]
def baseStart_645593 : Nat := 118140960795 + 645593 * 2 ^ 59
def prefixEnd_645593 : Nat := 4983230072969 + 3 ^ 40 * 645593 * 2
def baseEnd_645593 : Nat := 294666236602842531660869

theorem tailTrace_645593 : CollatzResearch.WordTrace tailWord_645593 prefixEnd_645593 294666236602842531660869 := by
  unfold tailWord_645593
  simp only [CollatzResearch.WordTrace]
  refine ⟨23546711150134294351381433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15697807433422862900920955 23546711150134294351381433)
  ·
    refine ⟨17660033362600720763536075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23546711150134294351381433 17660033362600720763536075)
    ·
      refine ⟨26490050043901081145304113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17660033362600720763536075 26490050043901081145304113)
      ·
        refine ⟨19867537532925810858978085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26490050043901081145304113 19867537532925810858978085)
        ·
          refine ⟨3725163287423589536058391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19867537532925810858978085 3725163287423589536058391)
          ·
            refine ⟨5587744931135384304087587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3725163287423589536058391 5587744931135384304087587)
            ·
              refine ⟨8381617396703076456131381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5587744931135384304087587 8381617396703076456131381)
              ·
                refine ⟨785776630940913417762317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8381617396703076456131381 785776630940913417762317)
                ·
                  refine ⟨294666236602842531660869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785776630940913417762317 294666236602842531660869)
                  ·
                    rfl

theorem cell20_645593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_645593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645593 prefixEnd_645593 := by exact prefixLift 645593
  have htrace : WordTrace (prefixWord ++ tailWord_645593) baseStart_645593 baseEnd_645593 := by
    simpa [prefixWord, tailWord_645593, baseEnd_645593] using wordTrace_append hprefix tailTrace_645593
  have hstable : (prefixWord ++ tailWord_645593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645593).length < 2 ^ (prefixWord ++ tailWord_645593).sum := by decide
  have hdescent : baseEnd_645593 < baseStart_645593 := by decide
  rcases family_descends (prefixWord ++ tailWord_645593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645600 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_645600 : Nat := 118140960795 + 645600 * 2 ^ 59
def prefixEnd_645600 : Nat := 4983230072969 + 3 ^ 40 * 645600 * 2
def baseEnd_645600 : Nat := 294669431593581618427507

theorem tailTrace_645600 : CollatzResearch.WordTrace tailWord_645600 prefixEnd_645600 294669431593581618427507 := by
  unfold tailWord_645600
  simp only [CollatzResearch.WordTrace]
  refine ⟨11773483230554467273443127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15697977640739289697924169 11773483230554467273443127)
  ·
    refine ⟨17660224845831700910164691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11773483230554467273443127 17660224845831700910164691)
    ·
      refine ⟨26490337268747551365247037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17660224845831700910164691 26490337268747551365247037)
      ·
        refine ⟨9933876475780331761967639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26490337268747551365247037 9933876475780331761967639)
        ·
          refine ⟨14900814713670497642951459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9933876475780331761967639 14900814713670497642951459)
          ·
            refine ⟨22351222070505746464427189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14900814713670497642951459 22351222070505746464427189)
            ·
              refine ⟨2095427069109913731040049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22351222070505746464427189 2095427069109913731040049)
              ·
                refine ⟨1571570301832435298280037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2095427069109913731040049 1571570301832435298280037)
                ·
                  refine ⟨294669431593581618427507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1571570301832435298280037 294669431593581618427507)
                  ·
                    rfl

theorem cell20_645600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_645600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645600 prefixEnd_645600 := by exact prefixLift 645600
  have htrace : WordTrace (prefixWord ++ tailWord_645600) baseStart_645600 baseEnd_645600 := by
    simpa [prefixWord, tailWord_645600, baseEnd_645600] using wordTrace_append hprefix tailTrace_645600
  have hstable : (prefixWord ++ tailWord_645600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645600).length < 2 ^ (prefixWord ++ tailWord_645600).sum := by decide
  have hdescent : baseEnd_645600 < baseStart_645600 := by decide
  rcases family_descends (prefixWord ++ tailWord_645600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645603 : List Nat := [1, 1, 1, 6, 3, 1, 3, 4]
def baseStart_645603 : Nat := 118140960795 + 645603 * 2 ^ 59
def prefixEnd_645603 : Nat := 4983230072969 + 3 ^ 40 * 645603 * 2
def baseEnd_645603 : Nat := 98223600291775647109165

theorem tailTrace_645603 : CollatzResearch.WordTrace tailWord_645603 prefixEnd_645603 98223600291775647109165 := by
  unfold tailWord_645603
  simp only [CollatzResearch.WordTrace]
  refine ⟨23547075880098066059245463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15698050586732044039496975 23547075880098066059245463)
  ·
    refine ⟨35320613820147099088868195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23547075880098066059245463 35320613820147099088868195)
    ·
      refine ⟨52980920730220648633302293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35320613820147099088868195 52980920730220648633302293)
      ·
        refine ⟨2483480659229092904686045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52980920730220648633302293 2483480659229092904686045)
        ·
          refine ⟨931305247210909839257267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2483480659229092904686045 931305247210909839257267)
          ·
            refine ⟨1396957870816364758885901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931305247210909839257267 1396957870816364758885901)
            ·
              refine ⟨523859201556136784582213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1396957870816364758885901 523859201556136784582213)
              ·
                refine ⟨98223600291775647109165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523859201556136784582213 98223600291775647109165)
                ·
                  rfl

theorem cell20_645603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 4].length) (baseStart_645603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645603 prefixEnd_645603 := by exact prefixLift 645603
  have htrace : WordTrace (prefixWord ++ tailWord_645603) baseStart_645603 baseEnd_645603 := by
    simpa [prefixWord, tailWord_645603, baseEnd_645603] using wordTrace_append hprefix tailTrace_645603
  have hstable : (prefixWord ++ tailWord_645603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645603).length < 2 ^ (prefixWord ++ tailWord_645603).sum := by decide
  have hdescent : baseEnd_645603 < baseStart_645603 := by decide
  rcases family_descends (prefixWord ++ tailWord_645603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645613 : List Nat := [1, 5, 1, 3, 1, 2, 2, 3, 2]
def baseStart_645613 : Nat := 118140960795 + 645613 * 2 ^ 59
def prefixEnd_645613 : Nat := 4983230072969 + 3 ^ 40 * 645613 * 2
def baseEnd_645613 : Nat := 294675365147811350994121

theorem tailTrace_645613 : CollatzResearch.WordTrace tailWord_645613 prefixEnd_645613 294675365147811350994121 := by
  unfold tailWord_645613
  simp only [CollatzResearch.WordTrace]
  refine ⟨23547440610061837767109493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15698293740041225178072995 23547440610061837767109493)
  ·
    refine ⟨2207572557193297290666515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23547440610061837767109493 2207572557193297290666515)
    ·
      refine ⟨3311358835789945935999773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2207572557193297290666515 3311358835789945935999773)
      ·
        refine ⟨1241759563421229725999915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3311358835789945935999773 1241759563421229725999915)
        ·
          refine ⟨1862639345131844588999873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241759563421229725999915 1862639345131844588999873)
          ·
            refine ⟨1396979508848883441749905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1862639345131844588999873 1396979508848883441749905)
            ·
              refine ⟨1047734631636662581312429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1396979508848883441749905 1047734631636662581312429)
              ·
                refine ⟨392900486863748467992161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1047734631636662581312429 392900486863748467992161)
                ·
                  refine ⟨294675365147811350994121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392900486863748467992161 294675365147811350994121)
                  ·
                    rfl

theorem cell20_645613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_645613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645613 prefixEnd_645613 := by exact prefixLift 645613
  have htrace : WordTrace (prefixWord ++ tailWord_645613) baseStart_645613 baseEnd_645613 := by
    simpa [prefixWord, tailWord_645613, baseEnd_645613] using wordTrace_append hprefix tailTrace_645613
  have hstable : (prefixWord ++ tailWord_645613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645613).length < 2 ^ (prefixWord ++ tailWord_645613).sum := by decide
  have hdescent : baseEnd_645613 < baseStart_645613 := by decide
  rcases family_descends (prefixWord ++ tailWord_645613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645668 : List Nat := [2, 3, 1, 5, 1, 2, 1, 3, 2]
def baseStart_645668 : Nat := 118140960795 + 645668 * 2 ^ 59
def prefixEnd_645668 : Nat := 4983230072969 + 3 ^ 40 * 645668 * 2
def baseEnd_645668 : Nat := 294700468646475604160563

theorem tailTrace_645668 : CollatzResearch.WordTrace tailWord_645668 prefixEnd_645668 294700468646475604160563 := by
  unfold tailWord_645668
  simp only [CollatzResearch.WordTrace]
  refine ⟨11774723312431291080180829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15699631083241721440241105 11774723312431291080180829)
  ·
    refine ⟨4415521242161734155067811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11774723312431291080180829 4415521242161734155067811)
    ·
      refine ⟨6623281863242601232601717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4415521242161734155067811 6623281863242601232601717)
      ·
        refine ⟨620932674678993865556411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6623281863242601232601717 620932674678993865556411)
        ·
          refine ⟨931399012018490798334617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620932674678993865556411 931399012018490798334617)
          ·
            refine ⟨698549259013868098750963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931399012018490798334617 698549259013868098750963)
            ·
              refine ⟨1047823888520802148126445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698549259013868098750963 1047823888520802148126445)
              ·
                refine ⟨392933958195300805547417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1047823888520802148126445 392933958195300805547417)
                ·
                  refine ⟨294700468646475604160563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392933958195300805547417 294700468646475604160563)
                  ·
                    rfl

theorem cell20_645668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_645668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645668 prefixEnd_645668 := by exact prefixLift 645668
  have htrace : WordTrace (prefixWord ++ tailWord_645668) baseStart_645668 baseEnd_645668 := by
    simpa [prefixWord, tailWord_645668, baseEnd_645668] using wordTrace_append hprefix tailTrace_645668
  have hstable : (prefixWord ++ tailWord_645668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645668).length < 2 ^ (prefixWord ++ tailWord_645668).sum := by decide
  have hdescent : baseEnd_645668 < baseStart_645668 := by decide
  rcases family_descends (prefixWord ++ tailWord_645668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645686 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_645686 : Nat := 118140960795 + 645686 * 2 ^ 59
def prefixEnd_645686 : Nat := 4983230072969 + 3 ^ 40 * 645686 * 2
def baseEnd_645686 : Nat := 294708684336947541560489

theorem tailTrace_645686 : CollatzResearch.WordTrace tailWord_645686 prefixEnd_645686 294708684336947541560489 := by
  unfold tailWord_645686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1471881446174835702157307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15700068759198247489677941 1471881446174835702157307)
  ·
    refine ⟨2207822169262253553235961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1471881446174835702157307 2207822169262253553235961)
    ·
      refine ⟨1655866626946690164926971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2207822169262253553235961 1655866626946690164926971)
      ·
        refine ⟨2483799940420035247390457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655866626946690164926971 2483799940420035247390457)
        ·
          refine ⟨1862849955315026435542843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2483799940420035247390457 1862849955315026435542843)
          ·
            refine ⟨2794274932972539653314265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862849955315026435542843 2794274932972539653314265)
            ·
              refine ⟨2095706199729404739985699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2794274932972539653314265 2095706199729404739985699)
              ·
                refine ⟨3143559299594107109978549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095706199729404739985699 3143559299594107109978549)
                ·
                  refine ⟨294708684336947541560489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3143559299594107109978549 294708684336947541560489)
                  ·
                    rfl

theorem cell20_645686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_645686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645686 prefixEnd_645686 := by exact prefixLift 645686
  have htrace : WordTrace (prefixWord ++ tailWord_645686) baseStart_645686 baseEnd_645686 := by
    simpa [prefixWord, tailWord_645686, baseEnd_645686] using wordTrace_append hprefix tailTrace_645686
  have hstable : (prefixWord ++ tailWord_645686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645686).length < 2 ^ (prefixWord ++ tailWord_645686).sum := by decide
  have hdescent : baseEnd_645686 < baseStart_645686 := by decide
  rcases family_descends (prefixWord ++ tailWord_645686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645693 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 4]
def baseStart_645693 : Nat := 118140960795 + 645693 * 2 ^ 59
def prefixEnd_645693 : Nat := 4983230072969 + 3 ^ 40 * 645693 * 2
def baseEnd_645693 : Nat := 294711879327686628327127

theorem tailTrace_645693 : CollatzResearch.WordTrace tailWord_645693 prefixEnd_645693 294711879327686628327127 := by
  unfold tailWord_645693
  simp only [CollatzResearch.WordTrace]
  refine ⟨23550358449772011430021733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15700238966514674286681155 23550358449772011430021733)
  ·
    refine ⟨4415692209332252143129075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23550358449772011430021733 4415692209332252143129075)
    ·
      refine ⟨6623538313998378214693613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4415692209332252143129075 6623538313998378214693613)
      ·
        refine ⟨2483826867749391830510105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6623538313998378214693613 2483826867749391830510105)
        ·
          refine ⟨1862870150812043872882579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2483826867749391830510105 1862870150812043872882579)
          ·
            refine ⟨2794305226218065809323869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862870150812043872882579 2794305226218065809323869)
            ·
              refine ⟨1047864459831774678496451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2794305226218065809323869 1047864459831774678496451)
              ·
                refine ⟨1571796689747662017744677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047864459831774678496451 1571796689747662017744677)
                ·
                  refine ⟨294711879327686628327127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1571796689747662017744677 294711879327686628327127)
                  ·
                    rfl

theorem cell20_645693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_645693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645693 prefixEnd_645693 := by exact prefixLift 645693
  have htrace : WordTrace (prefixWord ++ tailWord_645693) baseStart_645693 baseEnd_645693 := by
    simpa [prefixWord, tailWord_645693, baseEnd_645693] using wordTrace_append hprefix tailTrace_645693
  have hstable : (prefixWord ++ tailWord_645693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645693).length < 2 ^ (prefixWord ++ tailWord_645693).sum := by decide
  have hdescent : baseEnd_645693 < baseStart_645693 := by decide
  rcases family_descends (prefixWord ++ tailWord_645693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645703 : List Nat := [1, 1, 4, 1, 4, 3, 2, 1, 3]
def baseStart_645703 : Nat := 118140960795 + 645703 * 2 ^ 59
def prefixEnd_645703 : Nat := 4983230072969 + 3 ^ 40 * 645703 * 2
def baseEnd_645703 : Nat := 294716443600171037993753

theorem tailTrace_645703 : CollatzResearch.WordTrace tailWord_645703 prefixEnd_645703 294716443600171037993753 := by
  unfold tailWord_645703
  simp only [CollatzResearch.WordTrace]
  refine ⟨23550723179735783137885763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15700482119823855425257175 23550723179735783137885763)
  ·
    refine ⟨35326084769603674706828645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23550723179735783137885763 35326084769603674706828645)
    ·
      refine ⟨6623640894300689007530371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35326084769603674706828645 6623640894300689007530371)
      ·
        refine ⟨9935461341451033511295557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6623640894300689007530371 9935461341451033511295557)
        ·
          refine ⟨1862899001522068783367917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9935461341451033511295557 1862899001522068783367917)
          ·
            refine ⟨698587125570775793762969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1862899001522068783367917 698587125570775793762969)
            ·
              refine ⟨523940344178081845322227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698587125570775793762969 523940344178081845322227)
              ·
                refine ⟨785910516267122767983341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523940344178081845322227 785910516267122767983341)
                ·
                  refine ⟨294716443600171037993753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785910516267122767983341 294716443600171037993753)
                  ·
                    rfl

theorem cell20_645703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 3].length) (baseStart_645703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645703 prefixEnd_645703 := by exact prefixLift 645703
  have htrace : WordTrace (prefixWord ++ tailWord_645703) baseStart_645703 baseEnd_645703 := by
    simpa [prefixWord, tailWord_645703, baseEnd_645703] using wordTrace_append hprefix tailTrace_645703
  have hstable : (prefixWord ++ tailWord_645703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645703).length < 2 ^ (prefixWord ++ tailWord_645703).sum := by decide
  have hdescent : baseEnd_645703 < baseStart_645703 := by decide
  rcases family_descends (prefixWord ++ tailWord_645703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645714 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_645714 : Nat := 118140960795 + 645714 * 2 ^ 59
def prefixEnd_645714 : Nat := 4983230072969 + 3 ^ 40 * 645714 * 2
def baseEnd_645714 : Nat := 294721464299903888627041

theorem tailTrace_645714 : CollatzResearch.WordTrace tailWord_645714 prefixEnd_645714 294721464299903888627041 := by
  unfold tailWord_645714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5887781095673983004134049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15700749588463954677690797 5887781095673983004134049)
  ·
    refine ⟨4415835821755487253100537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5887781095673983004134049 4415835821755487253100537)
    ·
      refine ⟨3311876866316615439825403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4415835821755487253100537 3311876866316615439825403)
      ·
        refine ⟨4967815299474923159738105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3311876866316615439825403 4967815299474923159738105)
        ·
          refine ⟨3725861474606192369803579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4967815299474923159738105 3725861474606192369803579)
          ·
            refine ⟨5588792211909288554705369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3725861474606192369803579 5588792211909288554705369)
            ·
              refine ⟨4191594158931966416029027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5588792211909288554705369 4191594158931966416029027)
              ·
                refine ⟨6287391238397949624043541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4191594158931966416029027 6287391238397949624043541)
                ·
                  refine ⟨294721464299903888627041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6287391238397949624043541 294721464299903888627041)
                  ·
                    rfl

theorem cell20_645714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_645714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645714 prefixEnd_645714 := by exact prefixLift 645714
  have htrace : WordTrace (prefixWord ++ tailWord_645714) baseStart_645714 baseEnd_645714 := by
    simpa [prefixWord, tailWord_645714, baseEnd_645714] using wordTrace_append hprefix tailTrace_645714
  have hstable : (prefixWord ++ tailWord_645714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645714).length < 2 ^ (prefixWord ++ tailWord_645714).sum := by decide
  have hdescent : baseEnd_645714 < baseStart_645714 := by decide
  rcases family_descends (prefixWord ++ tailWord_645714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645728 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_645728 : Nat := 118140960795 + 645728 * 2 ^ 59
def prefixEnd_645728 : Nat := 4983230072969 + 3 ^ 40 * 645728 * 2
def baseEnd_645728 : Nat := 294727854281382062160317

theorem tailTrace_645728 : CollatzResearch.WordTrace tailWord_645728 prefixEnd_645728 294727854281382062160317 := by
  unfold tailWord_645728
  simp only [CollatzResearch.WordTrace]
  refine ⟨11775817502322606203772919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15701090003096808271697225 11775817502322606203772919)
  ·
    refine ⟨17663726253483909305659379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11775817502322606203772919 17663726253483909305659379)
    ·
      refine ⟨26495589380225863958489069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17663726253483909305659379 26495589380225863958489069)
      ·
        refine ⟨9935846017584698984433401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26495589380225863958489069 9935846017584698984433401)
        ·
          refine ⟨7451884513188524238325051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9935846017584698984433401 7451884513188524238325051)
          ·
            refine ⟨11177826769782786357487577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7451884513188524238325051 11177826769782786357487577)
            ·
              refine ⟨8383370077337089768115683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11177826769782786357487577 8383370077337089768115683)
              ·
                refine ⟨12575055116005634652173525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8383370077337089768115683 12575055116005634652173525)
                ·
                  refine ⟨294727854281382062160317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12575055116005634652173525 294727854281382062160317)
                  ·
                    rfl

theorem cell20_645728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_645728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645728 prefixEnd_645728 := by exact prefixLift 645728
  have htrace : WordTrace (prefixWord ++ tailWord_645728) baseStart_645728 baseEnd_645728 := by
    simpa [prefixWord, tailWord_645728, baseEnd_645728] using wordTrace_append hprefix tailTrace_645728
  have hstable : (prefixWord ++ tailWord_645728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645728).length < 2 ^ (prefixWord ++ tailWord_645728).sum := by decide
  have hdescent : baseEnd_645728 < baseStart_645728 := by decide
  rcases family_descends (prefixWord ++ tailWord_645728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645731 : List Nat := [1, 1, 1, 5, 1, 2, 2, 5, 2]
def baseStart_645731 : Nat := 118140960795 + 645731 * 2 ^ 59
def prefixEnd_645731 : Nat := 4983230072969 + 3 ^ 40 * 645731 * 2
def baseEnd_645731 : Nat := 294729223563127385060305

theorem tailTrace_645731 : CollatzResearch.WordTrace tailWord_645731 prefixEnd_645731 294729223563127385060305 := by
  unfold tailWord_645731
  simp only [CollatzResearch.WordTrace]
  refine ⟨23551744423634343919905047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15701162949089562613270031 23551744423634343919905047)
  ·
    refine ⟨35327616635451515879857571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23551744423634343919905047 35327616635451515879857571)
    ·
      refine ⟨52991424953177273819786357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35327616635451515879857571 52991424953177273819786357)
      ·
        refine ⟨4967946089360369420604971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52991424953177273819786357 4967946089360369420604971)
        ·
          refine ⟨7451919134040554130907457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4967946089360369420604971 7451919134040554130907457)
          ·
            refine ⟨5588939350530415598180593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7451919134040554130907457 5588939350530415598180593)
            ·
              refine ⟨4191704512897811698635445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5588939350530415598180593 4191704512897811698635445)
              ·
                refine ⟨392972298084169846747073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4191704512897811698635445 392972298084169846747073)
                ·
                  refine ⟨294729223563127385060305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392972298084169846747073 294729223563127385060305)
                  ·
                    rfl

theorem cell20_645731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 2].length) (baseStart_645731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645731 prefixEnd_645731 := by exact prefixLift 645731
  have htrace : WordTrace (prefixWord ++ tailWord_645731) baseStart_645731 baseEnd_645731 := by
    simpa [prefixWord, tailWord_645731, baseEnd_645731] using wordTrace_append hprefix tailTrace_645731
  have hstable : (prefixWord ++ tailWord_645731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645731).length < 2 ^ (prefixWord ++ tailWord_645731).sum := by decide
  have hdescent : baseEnd_645731 < baseStart_645731 := by decide
  rcases family_descends (prefixWord ++ tailWord_645731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645744 : List Nat := [2, 1, 1, 1, 8, 1, 2, 2, 2]
def baseStart_645744 : Nat := 118140960795 + 645744 * 2 ^ 59
def prefixEnd_645744 : Nat := 4983230072969 + 3 ^ 40 * 645744 * 2
def baseEnd_645744 : Nat := 294735157117357117626919

theorem tailTrace_645744 : CollatzResearch.WordTrace tailWord_645744 prefixEnd_645744 294735157117357117626919 := by
  unfold tailWord_645744
  simp only [CollatzResearch.WordTrace]
  refine ⟨11776109286293623570064143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15701479048391498093418857 11776109286293623570064143)
  ·
    refine ⟨17664163929440435355096215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11776109286293623570064143 17664163929440435355096215)
    ·
      refine ⟨26496245894160653032644323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17664163929440435355096215 26496245894160653032644323)
      ·
        refine ⟨39744368841240979548966485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26496245894160653032644323 39744368841240979548966485)
        ·
          refine ⟨465754322358292729089451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 39744368841240979548966485 465754322358292729089451)
          ·
            refine ⟨698631483537439093634177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465754322358292729089451 698631483537439093634177)
            ·
              refine ⟨523973612653079320225633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698631483537439093634177 523973612653079320225633)
              ·
                refine ⟨392980209489809490169225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523973612653079320225633 392980209489809490169225)
                ·
                  refine ⟨294735157117357117626919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392980209489809490169225 294735157117357117626919)
                  ·
                    rfl

theorem cell20_645744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 2].length) (baseStart_645744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645744 prefixEnd_645744 := by exact prefixLift 645744
  have htrace : WordTrace (prefixWord ++ tailWord_645744) baseStart_645744 baseEnd_645744 := by
    simpa [prefixWord, tailWord_645744, baseEnd_645744] using wordTrace_append hprefix tailTrace_645744
  have hstable : (prefixWord ++ tailWord_645744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645744).length < 2 ^ (prefixWord ++ tailWord_645744).sum := by decide
  have hdescent : baseEnd_645744 < baseStart_645744 := by decide
  rcases family_descends (prefixWord ++ tailWord_645744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645807 : List Nat := [1, 1, 2, 1, 2, 5, 2, 4, 2]
def baseStart_645807 : Nat := 118140960795 + 645807 * 2 ^ 59
def prefixEnd_645807 : Nat := 4983230072969 + 3 ^ 40 * 645807 * 2
def baseEnd_645807 : Nat := 294763912034008898526661

theorem tailTrace_645807 : CollatzResearch.WordTrace tailWord_645807 prefixEnd_645807 294763912034008898526661 := by
  unfold tailWord_645807
  simp only [CollatzResearch.WordTrace]
  refine ⟨23554516371359008899671675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15703010914239339266447783 23554516371359008899671675)
  ·
    refine ⟨35331774557038513349507513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23554516371359008899671675 35331774557038513349507513)
    ·
      refine ⟨26498830917778885012130635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35331774557038513349507513 26498830917778885012130635)
      ·
        refine ⟨39748246376668327518195953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26498830917778885012130635 39748246376668327518195953)
        ·
          refine ⟨29811184782501245638646965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39748246376668327518195953 29811184782501245638646965)
          ·
            refine ⟨2794798573359491778623153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29811184782501245638646965 2794798573359491778623153)
            ·
              refine ⟨2096098930019618833967365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2794798573359491778623153 2096098930019618833967365)
              ·
                refine ⟨393018549378678531368881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2096098930019618833967365 393018549378678531368881)
                ·
                  refine ⟨294763912034008898526661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393018549378678531368881 294763912034008898526661)
                  ·
                    rfl

theorem cell20_645807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 2].length) (baseStart_645807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645807 prefixEnd_645807 := by exact prefixLift 645807
  have htrace : WordTrace (prefixWord ++ tailWord_645807) baseStart_645807 baseEnd_645807 := by
    simpa [prefixWord, tailWord_645807, baseEnd_645807] using wordTrace_append hprefix tailTrace_645807
  have hstable : (prefixWord ++ tailWord_645807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645807).length < 2 ^ (prefixWord ++ tailWord_645807).sum := by decide
  have hdescent : baseEnd_645807 < baseStart_645807 := by decide
  rcases family_descends (prefixWord ++ tailWord_645807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645837 : List Nat := [1, 6, 2, 1, 3, 1, 1, 3, 2]
def baseStart_645837 : Nat := 118140960795 + 645837 * 2 ^ 59
def prefixEnd_645837 : Nat := 4983230072969 + 3 ^ 40 * 645837 * 2
def baseEnd_645837 : Nat := 294777604851462127526539

theorem tailTrace_645837 : CollatzResearch.WordTrace tailWord_645837 prefixEnd_645837 294777604851462127526539 := by
  unfold tailWord_645837
  simp only [CollatzResearch.WordTrace]
  refine ⟨23555610561250324023263765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15703740374166882682175843 23555610561250324023263765)
  ·
    refine ⟨1104169245058608938590489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23555610561250324023263765 1104169245058608938590489)
    ·
      refine ⟨828126933793956703942867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1104169245058608938590489 828126933793956703942867)
      ·
        refine ⟨1242190400690935055914301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828126933793956703942867 1242190400690935055914301)
        ·
          refine ⟨465821400259100645967863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1242190400690935055914301 465821400259100645967863)
          ·
            refine ⟨698732100388650968951795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465821400259100645967863 698732100388650968951795)
            ·
              refine ⟨1048098150582976453427693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698732100388650968951795 1048098150582976453427693)
              ·
                refine ⟨393036806468616170035385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1048098150582976453427693 393036806468616170035385)
                ·
                  refine ⟨294777604851462127526539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393036806468616170035385 294777604851462127526539)
                  ·
                    rfl

theorem cell20_645837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_645837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645837 prefixEnd_645837 := by exact prefixLift 645837
  have htrace : WordTrace (prefixWord ++ tailWord_645837) baseStart_645837 baseEnd_645837 := by
    simpa [prefixWord, tailWord_645837, baseEnd_645837] using wordTrace_append hprefix tailTrace_645837
  have hstable : (prefixWord ++ tailWord_645837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645837).length < 2 ^ (prefixWord ++ tailWord_645837).sum := by decide
  have hdescent : baseEnd_645837 < baseStart_645837 := by decide
  rcases family_descends (prefixWord ++ tailWord_645837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645852 : List Nat := [2, 2, 5, 1, 1, 1, 8]
def baseStart_645852 : Nat := 118140960795 + 645852 * 2 ^ 59
def prefixEnd_645852 : Nat := 4983230072969 + 3 ^ 40 * 645852 * 2
def baseEnd_645852 : Nat := 32753827917798749114053

theorem tailTrace_645852 : CollatzResearch.WordTrace tailWord_645852 prefixEnd_645852 32753827917798749114053 := by
  unfold tailWord_645852
  simp only [CollatzResearch.WordTrace]
  refine ⟨11778078828097990792529905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15704105104130654390039873 11778078828097990792529905)
  ·
    refine ⟨8833559121073493094397429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11778078828097990792529905 8833559121073493094397429)
    ·
      refine ⟨828146167600639977599759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8833559121073493094397429 828146167600639977599759)
      ·
        refine ⟨1242219251400959966399639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828146167600639977599759 1242219251400959966399639)
        ·
          refine ⟨1863328877101439949599459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242219251400959966399639 1863328877101439949599459)
          ·
            refine ⟨2794993315652159924399189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1863328877101439949599459 2794993315652159924399189)
            ·
              refine ⟨32753827917798749114053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2794993315652159924399189 32753827917798749114053)
              ·
                rfl

theorem cell20_645852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 8].length) (baseStart_645852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645852 prefixEnd_645852 := by exact prefixLift 645852
  have htrace : WordTrace (prefixWord ++ tailWord_645852) baseStart_645852 baseEnd_645852 := by
    simpa [prefixWord, tailWord_645852, baseEnd_645852] using wordTrace_append hprefix tailTrace_645852
  have hstable : (prefixWord ++ tailWord_645852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645852).length < 2 ^ (prefixWord ++ tailWord_645852).sum := by decide
  have hdescent : baseEnd_645852 < baseStart_645852 := by decide
  rcases family_descends (prefixWord ++ tailWord_645852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645859 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 5]
def baseStart_645859 : Nat := 118140960795 + 645859 * 2 ^ 59
def prefixEnd_645859 : Nat := 4983230072969 + 3 ^ 40 * 645859 * 2
def baseEnd_645859 : Nat := 294787646250927828793115

theorem tailTrace_645859 : CollatzResearch.WordTrace tailWord_645859 prefixEnd_645859 294787646250927828793115 := by
  unfold tailWord_645859
  simp only [CollatzResearch.WordTrace]
  refine ⟨23556412967170621780564631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15704275311447081187043087 23556412967170621780564631)
  ·
    refine ⟨35334619450755932670846947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23556412967170621780564631 35334619450755932670846947)
    ·
      refine ⟨53001929176133899006270421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35334619450755932670846947 53001929176133899006270421)
      ·
        refine ⟨1242232715065638257959463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 53001929176133899006270421 1242232715065638257959463)
        ·
          refine ⟨1863349072598457386939195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242232715065638257959463 1863349072598457386939195)
          ·
            refine ⟨2795023608897686080408793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1863349072598457386939195 2795023608897686080408793)
            ·
              refine ⟨2096267706673264560306595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2795023608897686080408793 2096267706673264560306595)
              ·
                refine ⟨3144401560009896840459893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096267706673264560306595 3144401560009896840459893)
                ·
                  refine ⟨294787646250927828793115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3144401560009896840459893 294787646250927828793115)
                  ·
                    rfl

theorem cell20_645859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_645859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645859 prefixEnd_645859 := by exact prefixLift 645859
  have htrace : WordTrace (prefixWord ++ tailWord_645859) baseStart_645859 baseEnd_645859 := by
    simpa [prefixWord, tailWord_645859, baseEnd_645859] using wordTrace_append hprefix tailTrace_645859
  have hstable : (prefixWord ++ tailWord_645859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645859).length < 2 ^ (prefixWord ++ tailWord_645859).sum := by decide
  have hdescent : baseEnd_645859 < baseStart_645859 := by decide
  rcases family_descends (prefixWord ++ tailWord_645859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645873 : List Nat := [1, 2, 2, 2, 2, 2, 4, 5]
def baseStart_645873 : Nat := 118140960795 + 645873 * 2 ^ 59
def prefixEnd_645873 : Nat := 4983230072969 + 3 ^ 40 * 645873 * 2
def baseEnd_645873 : Nat := 98264678744135334108797

theorem tailTrace_645873 : CollatzResearch.WordTrace tailWord_645873 prefixEnd_645873 98264678744135334108797 := by
  unfold tailWord_645873
  simp only [CollatzResearch.WordTrace]
  refine ⟨23556923589119902171574273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15704615726079934781049515 23556923589119902171574273)
  ·
    refine ⟨17667692691839926628680705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23556923589119902171574273 17667692691839926628680705)
    ·
      refine ⟨13250769518879944971510529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17667692691839926628680705 13250769518879944971510529)
      ·
        refine ⟨9938077139159958728632897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13250769518879944971510529 9938077139159958728632897)
        ·
          refine ⟨7453557854369969046474673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9938077139159958728632897 7453557854369969046474673)
          ·
            refine ⟨5590168390777476784856005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7453557854369969046474673 5590168390777476784856005)
            ·
              refine ⟨1048156573270776897160501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5590168390777476784856005 1048156573270776897160501)
              ·
                refine ⟨98264678744135334108797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1048156573270776897160501 98264678744135334108797)
                ·
                  rfl

theorem cell20_645873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_645873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645873 prefixEnd_645873 := by exact prefixLift 645873
  have htrace : WordTrace (prefixWord ++ tailWord_645873) baseStart_645873 baseEnd_645873 := by
    simpa [prefixWord, tailWord_645873, baseEnd_645873] using wordTrace_append hprefix tailTrace_645873
  have hstable : (prefixWord ++ tailWord_645873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645873).length < 2 ^ (prefixWord ++ tailWord_645873).sum := by decide
  have hdescent : baseEnd_645873 < baseStart_645873 := by decide
  rcases family_descends (prefixWord ++ tailWord_645873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645887 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 6]
def baseStart_645887 : Nat := 118140960795 + 645887 * 2 ^ 59
def prefixEnd_645887 : Nat := 4983230072969 + 3 ^ 40 * 645887 * 2
def baseEnd_645887 : Nat := 294800426213884175859667

theorem tailTrace_645887 : CollatzResearch.WordTrace tailWord_645887 prefixEnd_645887 294800426213884175859667 := by
  unfold tailWord_645887
  simp only [CollatzResearch.WordTrace]
  refine ⟨23557434211069182562583915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15704956140712788375055943 23557434211069182562583915)
  ·
    refine ⟨35336151316603773843875873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23557434211069182562583915 35336151316603773843875873)
    ·
      refine ⟨26502113487452830382906905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35336151316603773843875873 26502113487452830382906905)
      ·
        refine ⟨19876585115589622787180179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26502113487452830382906905 19876585115589622787180179)
        ·
          refine ⟨29814877673384434180770269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19876585115589622787180179 29814877673384434180770269)
          ·
            refine ⟨11180579127519162817788851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29814877673384434180770269 11180579127519162817788851)
            ·
              refine ⟨16770868691278744226683277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11180579127519162817788851 16770868691278744226683277)
              ·
                refine ⟨6289075759229529085006229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16770868691278744226683277 6289075759229529085006229)
                ·
                  refine ⟨294800426213884175859667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6289075759229529085006229 294800426213884175859667)
                  ·
                    rfl

theorem cell20_645887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_645887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645887 prefixEnd_645887 := by exact prefixLift 645887
  have htrace : WordTrace (prefixWord ++ tailWord_645887) baseStart_645887 baseEnd_645887 := by
    simpa [prefixWord, tailWord_645887, baseEnd_645887] using wordTrace_append hprefix tailTrace_645887
  have hstable : (prefixWord ++ tailWord_645887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645887).length < 2 ^ (prefixWord ++ tailWord_645887).sum := by decide
  have hdescent : baseEnd_645887 < baseStart_645887 := by decide
  rcases family_descends (prefixWord ++ tailWord_645887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645890 : List Nat := [3, 4, 1, 1, 1, 2, 2, 6]
def baseStart_645890 : Nat := 118140960795 + 645890 * 2 ^ 59
def prefixEnd_645890 : Nat := 4983230072969 + 3 ^ 40 * 645890 * 2
def baseEnd_645890 : Nat := 98267265165209832919885

theorem tailTrace_645890 : CollatzResearch.WordTrace tailWord_645890 prefixEnd_645890 98267265165209832919885 := by
  unfold tailWord_645890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5889385907514578518735781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15705029086705542716628749 5889385907514578518735781)
  ·
    refine ⟨1104259857658983472262959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5889385907514578518735781 1104259857658983472262959)
    ·
      refine ⟨1656389786488475208394439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1104259857658983472262959 1656389786488475208394439)
      ·
        refine ⟨2484584679732712812591659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1656389786488475208394439 2484584679732712812591659)
        ·
          refine ⟨3726877019599069218887489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484584679732712812591659 3726877019599069218887489)
          ·
            refine ⟨2795157764699301914165617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3726877019599069218887489 2795157764699301914165617)
            ·
              refine ⟨2096368323524476435624213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2795157764699301914165617 2096368323524476435624213)
              ·
                refine ⟨98267265165209832919885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2096368323524476435624213 98267265165209832919885)
                ·
                  rfl

theorem cell20_645890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_645890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645890 prefixEnd_645890 := by exact prefixLift 645890
  have htrace : WordTrace (prefixWord ++ tailWord_645890) baseStart_645890 baseEnd_645890 := by
    simpa [prefixWord, tailWord_645890, baseEnd_645890] using wordTrace_append hprefix tailTrace_645890
  have hstable : (prefixWord ++ tailWord_645890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645890).length < 2 ^ (prefixWord ++ tailWord_645890).sum := by decide
  have hdescent : baseEnd_645890 < baseStart_645890 := by decide
  rcases family_descends (prefixWord ++ tailWord_645890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645911 : List Nat := [1, 1, 3, 4, 3, 8]
def baseStart_645911 : Nat := 118140960795 + 645911 * 2 ^ 59
def prefixEnd_645911 : Nat := 4983230072969 + 3 ^ 40 * 645911 * 2
def baseEnd_645911 : Nat := 10918940017327657742947

theorem tailTrace_645911 : CollatzResearch.WordTrace tailWord_645911 prefixEnd_645911 10918940017327657742947 := by
  unfold tailWord_645911
  simp only [CollatzResearch.WordTrace]
  refine ⟨23558309562982234661457587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15705539708654823107638391 23558309562982234661457587)
  ·
    refine ⟨35337464344473351992186381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23558309562982234661457587 35337464344473351992186381)
    ·
      refine ⟨13251549129177506997069893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35337464344473351992186381 13251549129177506997069893)
      ·
        refine ⟨2484665461720782561950605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13251549129177506997069893 2484665461720782561950605)
        ·
          refine ⟨931749548145293460731477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2484665461720782561950605 931749548145293460731477)
          ·
            refine ⟨10918940017327657742947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 931749548145293460731477 10918940017327657742947)
            ·
              rfl

theorem cell20_645911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 8].length) (baseStart_645911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645911 prefixEnd_645911 := by exact prefixLift 645911
  have htrace : WordTrace (prefixWord ++ tailWord_645911) baseStart_645911 baseEnd_645911 := by
    simpa [prefixWord, tailWord_645911, baseEnd_645911] using wordTrace_append hprefix tailTrace_645911
  have hstable : (prefixWord ++ tailWord_645911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645911).length < 2 ^ (prefixWord ++ tailWord_645911).sum := by decide
  have hdescent : baseEnd_645911 < baseStart_645911 := by decide
  rcases family_descends (prefixWord ++ tailWord_645911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645917 : List Nat := [1, 4, 2, 4, 1, 1, 1, 4, 2]
def baseStart_645917 : Nat := 118140960795 + 645917 * 2 ^ 59
def prefixEnd_645917 : Nat := 4983230072969 + 3 ^ 40 * 645917 * 2
def baseEnd_645917 : Nat := 294814119031337404859545

theorem tailTrace_645917 : CollatzResearch.WordTrace tailWord_645917 prefixEnd_645917 294814119031337404859545 := by
  unfold tailWord_645917
  simp only [CollatzResearch.WordTrace]
  refine ⟨23558528400960497686176005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15705685600640331790784003 23558528400960497686176005)
  ·
    refine ⟨4417224075180093316158001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23558528400960497686176005 4417224075180093316158001)
    ·
      refine ⟨3312918056385069987118501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4417224075180093316158001 3312918056385069987118501)
      ·
        refine ⟨621172135572200622584719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3312918056385069987118501 621172135572200622584719)
        ·
          refine ⟨931758203358300933877079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621172135572200622584719 931758203358300933877079)
          ·
            refine ⟨1397637305037451400815619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931758203358300933877079 1397637305037451400815619)
            ·
              refine ⟨2096455957556177101223429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397637305037451400815619 2096455957556177101223429)
              ·
                refine ⟨393085492041783206479393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2096455957556177101223429 393085492041783206479393)
                ·
                  refine ⟨294814119031337404859545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393085492041783206479393 294814119031337404859545)
                  ·
                    rfl

theorem cell20_645917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_645917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645917 prefixEnd_645917 := by exact prefixLift 645917
  have htrace : WordTrace (prefixWord ++ tailWord_645917) baseStart_645917 baseEnd_645917 := by
    simpa [prefixWord, tailWord_645917, baseEnd_645917] using wordTrace_append hprefix tailTrace_645917
  have hstable : (prefixWord ++ tailWord_645917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645917).length < 2 ^ (prefixWord ++ tailWord_645917).sum := by decide
  have hdescent : baseEnd_645917 < baseStart_645917 := by decide
  rcases family_descends (prefixWord ++ tailWord_645917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645921 : List Nat := [1, 2, 3, 2, 1, 2, 3, 4, 2]
def baseStart_645921 : Nat := 118140960795 + 645921 * 2 ^ 59
def prefixEnd_645921 : Nat := 4983230072969 + 3 ^ 40 * 645921 * 2
def baseEnd_645921 : Nat := 294815944740331168726195

theorem tailTrace_645921 : CollatzResearch.WordTrace tailWord_645921 prefixEnd_645921 294815944740331168726195 := by
  unfold tailWord_645921
  simp only [CollatzResearch.WordTrace]
  refine ⟨23558674292946006369321617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15705782861964004246214411 23558674292946006369321617)
  ·
    refine ⟨17669005719709504776991213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23558674292946006369321617 17669005719709504776991213)
    ·
      refine ⟨6625877144891064291371705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17669005719709504776991213 6625877144891064291371705)
      ·
        refine ⟨4969407858668298218528779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6625877144891064291371705 4969407858668298218528779)
        ·
          refine ⟨7454111788002447327793169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4969407858668298218528779 7454111788002447327793169)
          ·
            refine ⟨5590583841001835495844877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7454111788002447327793169 5590583841001835495844877)
            ·
              refine ⟨2096468940375688310941829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5590583841001835495844877 2096468940375688310941829)
              ·
                refine ⟨393087926320441558301593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2096468940375688310941829 393087926320441558301593)
                ·
                  refine ⟨294815944740331168726195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393087926320441558301593 294815944740331168726195)
                  ·
                    rfl

theorem cell20_645921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 2].length) (baseStart_645921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645921 prefixEnd_645921 := by exact prefixLift 645921
  have htrace : WordTrace (prefixWord ++ tailWord_645921) baseStart_645921 baseEnd_645921 := by
    simpa [prefixWord, tailWord_645921, baseEnd_645921] using wordTrace_append hprefix tailTrace_645921
  have hstable : (prefixWord ++ tailWord_645921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645921).length < 2 ^ (prefixWord ++ tailWord_645921).sum := by decide
  have hdescent : baseEnd_645921 < baseStart_645921 := by decide
  rcases family_descends (prefixWord ++ tailWord_645921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645969 : List Nat := [1, 2, 2, 1, 7, 1, 1, 2, 3]
def baseStart_645969 : Nat := 118140960795 + 645969 * 2 ^ 59
def prefixEnd_645969 : Nat := 4983230072969 + 3 ^ 40 * 645969 * 2
def baseEnd_645969 : Nat := 294837853248256335125999

theorem tailTrace_645969 : CollatzResearch.WordTrace tailWord_645969 prefixEnd_645969 294837853248256335125999 := by
  unfold tailWord_645969
  simp only [CollatzResearch.WordTrace]
  refine ⟨23560424996772110567068961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15706949997848073711379307 23560424996772110567068961)
  ·
    refine ⟨17670318747579082925301721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23560424996772110567068961 17670318747579082925301721)
    ·
      refine ⟨13252739060684312193976291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17670318747579082925301721 13252739060684312193976291)
      ·
        refine ⟨19879108591026468290964437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13252739060684312193976291 19879108591026468290964437)
        ·
          refine ⟨465916607602182850569479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19879108591026468290964437 465916607602182850569479)
          ·
            refine ⟨698874911403274275854219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465916607602182850569479 698874911403274275854219)
            ·
              refine ⟨1048312367104911413781329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698874911403274275854219 1048312367104911413781329)
              ·
                refine ⟨786234275328683560335997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1048312367104911413781329 786234275328683560335997)
                ·
                  refine ⟨294837853248256335125999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 786234275328683560335997 294837853248256335125999)
                  ·
                    rfl

theorem cell20_645969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 3].length) (baseStart_645969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_645969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_645969 prefixEnd_645969 := by exact prefixLift 645969
  have htrace : WordTrace (prefixWord ++ tailWord_645969) baseStart_645969 baseEnd_645969 := by
    simpa [prefixWord, tailWord_645969, baseEnd_645969] using wordTrace_append hprefix tailTrace_645969
  have hstable : (prefixWord ++ tailWord_645969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645969).length < 2 ^ (prefixWord ++ tailWord_645969).sum := by decide
  have hdescent : baseEnd_645969 < baseStart_645969 := by decide
  rcases family_descends (prefixWord ++ tailWord_645969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646025 : List Nat := [1, 2, 1, 1, 5, 4, 6]
def baseStart_646025 : Nat := 118140960795 + 646025 * 2 ^ 59
def prefixEnd_646025 : Nat := 4983230072969 + 3 ^ 40 * 646025 * 2
def baseEnd_646025 : Nat := 32762601463796558806567

theorem tailTrace_646025 : CollatzResearch.WordTrace tailWord_646025 prefixEnd_646025 32762601463796558806567 := by
  unfold tailWord_646025
  simp only [CollatzResearch.WordTrace]
  refine ⟨23562467484569232131107529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15708311656379488087405019 23562467484569232131107529)
  ·
    refine ⟨17671850613426924098330647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23562467484569232131107529 17671850613426924098330647)
    ·
      refine ⟨26507775920140386147495971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17671850613426924098330647 26507775920140386147495971)
      ·
        refine ⟨39761663880210579221243957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26507775920140386147495971 39761663880210579221243957)
        ·
          refine ⟨3727655988769741801991621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39761663880210579221243957 3727655988769741801991621)
          ·
            refine ⟨698935497894326587873429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3727655988769741801991621 698935497894326587873429)
            ·
              refine ⟨32762601463796558806567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 698935497894326587873429 32762601463796558806567)
              ·
                rfl

theorem cell20_646025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 6].length) (baseStart_646025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646025 prefixEnd_646025 := by exact prefixLift 646025
  have htrace : WordTrace (prefixWord ++ tailWord_646025) baseStart_646025 baseEnd_646025 := by
    simpa [prefixWord, tailWord_646025, baseEnd_646025] using wordTrace_append hprefix tailTrace_646025
  have hstable : (prefixWord ++ tailWord_646025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646025).length < 2 ^ (prefixWord ++ tailWord_646025).sum := by decide
  have hdescent : baseEnd_646025 < baseStart_646025 := by decide
  rcases family_descends (prefixWord ++ tailWord_646025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646038 : List Nat := [5, 3, 1, 1, 1, 2, 2, 5]
def baseStart_646038 : Nat := 118140960795 + 646038 * 2 ^ 59
def prefixEnd_646038 : Nat := 4983230072969 + 3 ^ 40 * 646038 * 2
def baseEnd_646038 : Nat := 98289782242799587275239

theorem tailTrace_646038 : CollatzResearch.WordTrace tailWord_646038 prefixEnd_646038 98289782242799587275239 := by
  unfold tailWord_646038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472683852095133459458173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15708627755681423567553845 1472683852095133459458173)
  ·
    refine ⟨552256444535675047296815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1472683852095133459458173 552256444535675047296815)
    ·
      refine ⟨828384666803512570945223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 552256444535675047296815 828384666803512570945223)
      ·
        refine ⟨1242577000205268856417835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828384666803512570945223 1242577000205268856417835)
        ·
          refine ⟨1863865500307903284626753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242577000205268856417835 1863865500307903284626753)
          ·
            refine ⟨1397899125230927463470065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1863865500307903284626753 1397899125230927463470065)
            ·
              refine ⟨1048424343923195597602549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1397899125230927463470065 1048424343923195597602549)
              ·
                refine ⟨98289782242799587275239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1048424343923195597602549 98289782242799587275239)
                ·
                  rfl

theorem cell20_646038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_646038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646038 prefixEnd_646038 := by exact prefixLift 646038
  have htrace : WordTrace (prefixWord ++ tailWord_646038) baseStart_646038 baseEnd_646038 := by
    simpa [prefixWord, tailWord_646038, baseEnd_646038] using wordTrace_append hprefix tailTrace_646038
  have hstable : (prefixWord ++ tailWord_646038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646038).length < 2 ^ (prefixWord ++ tailWord_646038).sum := by decide
  have hdescent : baseEnd_646038 < baseStart_646038 := by decide
  rcases family_descends (prefixWord ++ tailWord_646038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646042 : List Nat := [3, 1, 1, 4, 3, 1, 2, 5]
def baseStart_646042 : Nat := 118140960795 + 646042 * 2 ^ 59
def prefixEnd_646042 : Nat := 4983230072969 + 3 ^ 40 * 646042 * 2
def baseEnd_646042 : Nat := 98290390812464175230789

theorem tailTrace_646042 : CollatzResearch.WordTrace tailWord_646042 prefixEnd_646042 98290390812464175230789 := by
  unfold tailWord_646042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5890771881376911008619095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15708725017005096022984253 5890771881376911008619095)
  ·
    refine ⟨8836157822065366512928643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5890771881376911008619095 8836157822065366512928643)
    ·
      refine ⟨13254236733098049769392965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8836157822065366512928643 13254236733098049769392965)
      ·
        refine ⟨2485169387455884331761181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13254236733098049769392965 2485169387455884331761181)
        ·
          refine ⟨931938520295956624410443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2485169387455884331761181 931938520295956624410443)
          ·
            refine ⟨1397907780443934936615665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931938520295956624410443 1397907780443934936615665)
            ·
              refine ⟨1048430835332951202461749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1397907780443934936615665 1048430835332951202461749)
              ·
                refine ⟨98290390812464175230789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1048430835332951202461749 98290390812464175230789)
                ·
                  rfl

theorem cell20_646042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_646042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646042 prefixEnd_646042 := by exact prefixLift 646042
  have htrace : WordTrace (prefixWord ++ tailWord_646042) baseStart_646042 baseEnd_646042 := by
    simpa [prefixWord, tailWord_646042, baseEnd_646042] using wordTrace_append hprefix tailTrace_646042
  have hstable : (prefixWord ++ tailWord_646042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646042).length < 2 ^ (prefixWord ++ tailWord_646042).sum := by decide
  have hdescent : baseEnd_646042 < baseStart_646042 := by decide
  rcases family_descends (prefixWord ++ tailWord_646042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646093 : List Nat := [1, 6, 3, 1, 1, 2, 1, 5]
def baseStart_646093 : Nat := 118140960795 + 646093 * 2 ^ 59
def prefixEnd_646093 : Nat := 4983230072969 + 3 ^ 40 * 646093 * 2
def baseEnd_646093 : Nat := 98298150075687671664053

theorem tailTrace_646093 : CollatzResearch.WordTrace tailWord_646093 prefixEnd_646093 98298150075687671664053 := by
  unfold tailWord_646093
  simp only [CollatzResearch.WordTrace]
  refine ⟨23564947648322879744582933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15709965098881919829721955 23564947648322879744582933)
  ·
    refine ⟨1104606921015134988027325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23564947648322879744582933 1104606921015134988027325)
    ·
      refine ⟨414227595380675620510247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1104606921015134988027325 414227595380675620510247)
      ·
        refine ⟨621341393071013430765371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414227595380675620510247 621341393071013430765371)
        ·
          refine ⟨932012089606520146148057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621341393071013430765371 932012089606520146148057)
          ·
            refine ⟨699009067204890109611043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 932012089606520146148057 699009067204890109611043)
            ·
              refine ⟨1048513600807335164416565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699009067204890109611043 1048513600807335164416565)
              ·
                refine ⟨98298150075687671664053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1048513600807335164416565 98298150075687671664053)
                ·
                  rfl

theorem cell20_646093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 5].length) (baseStart_646093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646093 prefixEnd_646093 := by exact prefixLift 646093
  have htrace : WordTrace (prefixWord ++ tailWord_646093) baseStart_646093 baseEnd_646093 := by
    simpa [prefixWord, tailWord_646093, baseEnd_646093] using wordTrace_append hprefix tailTrace_646093
  have hstable : (prefixWord ++ tailWord_646093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646093).length < 2 ^ (prefixWord ++ tailWord_646093).sum := by decide
  have hdescent : baseEnd_646093 < baseStart_646093 := by decide
  rcases family_descends (prefixWord ++ tailWord_646093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646142 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_646142 : Nat := 118140960795 + 646142 * 2 ^ 59
def prefixEnd_646142 : Nat := 4983230072969 + 3 ^ 40 * 646142 * 2
def baseEnd_646142 : Nat := 294916815162236622358625

theorem tailTrace_646142 : CollatzResearch.WordTrace tailWord_646142 prefixEnd_646142 294916815162236622358625 := by
  unfold tailWord_646142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2945841853143170139139585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15711156550096907408744453 2945841853143170139139585)
  ·
    refine ⟨2209381389857377604354689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2945841853143170139139585 2209381389857377604354689)
    ·
      refine ⟨1657036042393033203266017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2209381389857377604354689 1657036042393033203266017)
      ·
        refine ⟨1242777031794774902449513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1657036042393033203266017 1242777031794774902449513)
        ·
          refine ⟨932082773846081176837135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1242777031794774902449513 932082773846081176837135)
          ·
            refine ⟨1398124160769121765255703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932082773846081176837135 1398124160769121765255703)
            ·
              refine ⟨2097186241153682647883555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1398124160769121765255703 2097186241153682647883555)
              ·
                refine ⟨3145779361730523971825333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097186241153682647883555 3145779361730523971825333)
                ·
                  refine ⟨294916815162236622358625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3145779361730523971825333 294916815162236622358625)
                  ·
                    rfl

theorem cell20_646142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_646142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646142 prefixEnd_646142 := by exact prefixLift 646142
  have htrace : WordTrace (prefixWord ++ tailWord_646142) baseStart_646142 baseEnd_646142 := by
    simpa [prefixWord, tailWord_646142, baseEnd_646142] using wordTrace_append hprefix tailTrace_646142
  have hstable : (prefixWord ++ tailWord_646142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646142).length < 2 ^ (prefixWord ++ tailWord_646142).sum := by decide
  have hdescent : baseEnd_646142 < baseStart_646142 := by decide
  rcases family_descends (prefixWord ++ tailWord_646142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646173 : List Nat := [1, 4, 2, 2, 3, 2, 2, 4]
def baseStart_646173 : Nat := 118140960795 + 646173 * 2 ^ 59
def prefixEnd_646173 : Nat := 4983230072969 + 3 ^ 40 * 646173 * 2
def baseEnd_646173 : Nat := 98310321468979430775055

theorem tailTrace_646173 : CollatzResearch.WordTrace tailWord_646173 prefixEnd_646173 98310321468979430775055 := by
  unfold tailWord_646173
  simp only [CollatzResearch.WordTrace]
  refine ⟨23567865488033053407495173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15711910325355368938330115 23567865488033053407495173)
  ·
    refine ⟨4418974779006197513905345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23567865488033053407495173 4418974779006197513905345)
    ·
      refine ⟨3314231084254648135429009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4418974779006197513905345 3314231084254648135429009)
      ·
        refine ⟨2485673313190986101571757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3314231084254648135429009 2485673313190986101571757)
        ·
          refine ⟨932127492446619788089409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2485673313190986101571757 932127492446619788089409)
          ·
            refine ⟨699095619334964841067057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 932127492446619788089409 699095619334964841067057)
            ·
              refine ⟨524321714501223630800293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699095619334964841067057 524321714501223630800293)
              ·
                refine ⟨98310321468979430775055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 524321714501223630800293 98310321468979430775055)
                ·
                  rfl

theorem cell20_646173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 4].length) (baseStart_646173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646173 prefixEnd_646173 := by exact prefixLift 646173
  have htrace : WordTrace (prefixWord ++ tailWord_646173) baseStart_646173 baseEnd_646173 := by
    simpa [prefixWord, tailWord_646173, baseEnd_646173] using wordTrace_append hprefix tailTrace_646173
  have hstable : (prefixWord ++ tailWord_646173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646173).length < 2 ^ (prefixWord ++ tailWord_646173).sum := by decide
  have hdescent : baseEnd_646173 < baseStart_646173 := by decide
  rcases family_descends (prefixWord ++ tailWord_646173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646177 : List Nat := [1, 2, 3, 2, 3, 2, 1, 6]
def baseStart_646177 : Nat := 118140960795 + 646177 * 2 ^ 59
def prefixEnd_646177 : Nat := 4983230072969 + 3 ^ 40 * 646177 * 2
def baseEnd_646177 : Nat := 98310930038644018730605

theorem tailTrace_646177 : CollatzResearch.WordTrace tailWord_646177 prefixEnd_646177 98310930038644018730605 := by
  unfold tailWord_646177
  simp only [CollatzResearch.WordTrace]
  refine ⟨23568011380018562090640785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15712007586679041393760523 23568011380018562090640785)
  ·
    refine ⟨17676008535013921567980589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23568011380018562090640785 17676008535013921567980589)
    ·
      refine ⟨6628503200630220587992721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17676008535013921567980589 6628503200630220587992721)
      ·
        refine ⟨4971377400472665440994541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6628503200630220587992721 4971377400472665440994541)
        ·
          refine ⟨1864266525177249540372953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4971377400472665440994541 1864266525177249540372953)
          ·
            refine ⟨1398199893882937155279715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1864266525177249540372953 1398199893882937155279715)
            ·
              refine ⟨2097299840824405732919573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1398199893882937155279715 2097299840824405732919573)
              ·
                refine ⟨98310930038644018730605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2097299840824405732919573 98310930038644018730605)
                ·
                  rfl

theorem cell20_646177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_646177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646177 prefixEnd_646177 := by exact prefixLift 646177
  have htrace : WordTrace (prefixWord ++ tailWord_646177) baseStart_646177 baseEnd_646177 := by
    simpa [prefixWord, tailWord_646177, baseEnd_646177] using wordTrace_append hprefix tailTrace_646177
  have hstable : (prefixWord ++ tailWord_646177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646177).length < 2 ^ (prefixWord ++ tailWord_646177).sum := by decide
  have hdescent : baseEnd_646177 < baseStart_646177 := by decide
  rcases family_descends (prefixWord ++ tailWord_646177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646183 : List Nat := [1, 1, 7, 1, 1, 3, 1, 3, 2]
def baseStart_646183 : Nat := 118140960795 + 646183 * 2 ^ 59
def prefixEnd_646183 : Nat := 4983230072969 + 3 ^ 40 * 646183 * 2
def baseEnd_646183 : Nat := 294935528679422701991791

theorem tailTrace_646183 : CollatzResearch.WordTrace tailWord_646183 prefixEnd_646183 294935528679422701991791 := by
  unfold tailWord_646183
  simp only [CollatzResearch.WordTrace]
  refine ⟨23568230217996825115359203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15712153478664550076906135 23568230217996825115359203)
  ·
    refine ⟨35352345326995237673038805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23568230217996825115359203 35352345326995237673038805)
    ·
      refine ⟨828570593601450882961847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 35352345326995237673038805 828570593601450882961847)
      ·
        refine ⟨1242855890402176324442771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828570593601450882961847 1242855890402176324442771)
        ·
          refine ⟨1864283835603264486664157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242855890402176324442771 1864283835603264486664157)
          ·
            refine ⟨699106438351224182499059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1864283835603264486664157 699106438351224182499059)
            ·
              refine ⟨1048659657526836273748589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699106438351224182499059 1048659657526836273748589)
              ·
                refine ⟨393247371572563602655721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1048659657526836273748589 393247371572563602655721)
                ·
                  refine ⟨294935528679422701991791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393247371572563602655721 294935528679422701991791)
                  ·
                    rfl

theorem cell20_646183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 2].length) (baseStart_646183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646183 prefixEnd_646183 := by exact prefixLift 646183
  have htrace : WordTrace (prefixWord ++ tailWord_646183) baseStart_646183 baseEnd_646183 := by
    simpa [prefixWord, tailWord_646183, baseEnd_646183] using wordTrace_append hprefix tailTrace_646183
  have hstable : (prefixWord ++ tailWord_646183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646183).length < 2 ^ (prefixWord ++ tailWord_646183).sum := by decide
  have hdescent : baseEnd_646183 < baseStart_646183 := by decide
  rcases family_descends (prefixWord ++ tailWord_646183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646204 : List Nat := [2, 2, 2, 2, 2, 3, 3, 2, 2]
def baseStart_646204 : Nat := 118140960795 + 646204 * 2 ^ 59
def prefixEnd_646204 : Nat := 4983230072969 + 3 ^ 40 * 646204 * 2
def baseEnd_646204 : Nat := 294945113651639962291705

theorem tailTrace_646204 : CollatzResearch.WordTrace tailWord_646204 prefixEnd_646204 294945113651639962291705 := by
  unfold tailWord_646204
  simp only [CollatzResearch.WordTrace]
  refine ⟨11784498075460372850936833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15712664100613830467915777 11784498075460372850936833)
  ·
    refine ⟨8838373556595279638202625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11784498075460372850936833 8838373556595279638202625)
    ·
      refine ⟨6628780167446459728651969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8838373556595279638202625 6628780167446459728651969)
      ·
        refine ⟨4971585125584844796488977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6628780167446459728651969 4971585125584844796488977)
        ·
          refine ⟨3728688844188633597366733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4971585125584844796488977 3728688844188633597366733)
          ·
            refine ⟨1398258316570737599012525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3728688844188633597366733 1398258316570737599012525)
            ·
              refine ⟨524346868714026599629697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1398258316570737599012525 524346868714026599629697)
              ·
                refine ⟨393260151535519949722273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524346868714026599629697 393260151535519949722273)
                ·
                  refine ⟨294945113651639962291705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393260151535519949722273 294945113651639962291705)
                  ·
                    rfl

theorem cell20_646204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_646204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646204 prefixEnd_646204 := by exact prefixLift 646204
  have htrace : WordTrace (prefixWord ++ tailWord_646204) baseStart_646204 baseEnd_646204 := by
    simpa [prefixWord, tailWord_646204, baseEnd_646204] using wordTrace_append hprefix tailTrace_646204
  have hstable : (prefixWord ++ tailWord_646204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646204).length < 2 ^ (prefixWord ++ tailWord_646204).sum := by decide
  have hdescent : baseEnd_646204 < baseStart_646204 := by decide
  rcases family_descends (prefixWord ++ tailWord_646204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646214 : List Nat := [6, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_646214 : Nat := 118140960795 + 646214 * 2 ^ 59
def prefixEnd_646214 : Nat := 4983230072969 + 3 ^ 40 * 646214 * 2
def baseEnd_646214 : Nat := 294949677924124371958331

theorem tailTrace_646214 : CollatzResearch.WordTrace tailWord_646214 prefixEnd_646214 294949677924124371958331 := by
  unfold tailWord_646214
  simp only [CollatzResearch.WordTrace]
  refine ⟨736542527527641169054303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15712907253923011606491797 736542527527641169054303)
  ·
    refine ⟨1104813791291461753581455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 736542527527641169054303 1104813791291461753581455)
    ·
      refine ⟨1657220686937192630372183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1104813791291461753581455 1657220686937192630372183)
      ·
        refine ⟨2485831030405788945558275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1657220686937192630372183 2485831030405788945558275)
        ·
          refine ⟨3728746545608683418337413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485831030405788945558275 3728746545608683418337413)
          ·
            refine ⟨699139977301628140938265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3728746545608683418337413 699139977301628140938265)
            ·
              refine ⟨524354982976221105703699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699139977301628140938265 524354982976221105703699)
              ·
                refine ⟨786532474464331658555549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524354982976221105703699 786532474464331658555549)
                ·
                  refine ⟨294949677924124371958331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 786532474464331658555549 294949677924124371958331)
                  ·
                    rfl

theorem cell20_646214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_646214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646214 prefixEnd_646214 := by exact prefixLift 646214
  have htrace : WordTrace (prefixWord ++ tailWord_646214) baseStart_646214 baseEnd_646214 := by
    simpa [prefixWord, tailWord_646214, baseEnd_646214] using wordTrace_append hprefix tailTrace_646214
  have hstable : (prefixWord ++ tailWord_646214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646214).length < 2 ^ (prefixWord ++ tailWord_646214).sum := by decide
  have hdescent : baseEnd_646214 < baseStart_646214 := by decide
  rcases family_descends (prefixWord ++ tailWord_646214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646215 : List Nat := [1, 1, 4, 1, 3, 3, 2, 5]
def baseStart_646215 : Nat := 118140960795 + 646215 * 2 ^ 59
def prefixEnd_646215 : Nat := 4983230072969 + 3 ^ 40 * 646215 * 2
def baseEnd_646215 : Nat := 98316711450457604308331

theorem tailTrace_646215 : CollatzResearch.WordTrace tailWord_646215 prefixEnd_646215 98316711450457604308331 := by
  unfold tailWord_646215
  simp only [CollatzResearch.WordTrace]
  refine ⟨23569397353880894580524099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15712931569253929720349399 23569397353880894580524099)
  ·
    refine ⟨35354096030821341870786149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23569397353880894580524099 35354096030821341870786149)
    ·
      refine ⟨6628893005779001600772403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35354096030821341870786149 6628893005779001600772403)
      ·
        refine ⟨9943339508668502401158605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6628893005779001600772403 9943339508668502401158605)
        ·
          refine ⟨3728752315750688400434477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9943339508668502401158605 3728752315750688400434477)
          ·
            refine ⟨1398282118406508150162929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3728752315750688400434477 1398282118406508150162929)
            ·
              refine ⟨1048711588804881112622197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1398282118406508150162929 1048711588804881112622197)
              ·
                refine ⟨98316711450457604308331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1048711588804881112622197 98316711450457604308331)
                ·
                  rfl

theorem cell20_646215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_646215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646215 prefixEnd_646215 := by exact prefixLift 646215
  have htrace : WordTrace (prefixWord ++ tailWord_646215) baseStart_646215 baseEnd_646215 := by
    simpa [prefixWord, tailWord_646215, baseEnd_646215] using wordTrace_append hprefix tailTrace_646215
  have hstable : (prefixWord ++ tailWord_646215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646215).length < 2 ^ (prefixWord ++ tailWord_646215).sum := by decide
  have hdescent : baseEnd_646215 < baseStart_646215 := by decide
  rcases family_descends (prefixWord ++ tailWord_646215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646229 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 6]
def baseStart_646229 : Nat := 118140960795 + 646229 * 2 ^ 59
def prefixEnd_646229 : Nat := 4983230072969 + 3 ^ 40 * 646229 * 2
def baseEnd_646229 : Nat := 294956524332850986458269

theorem tailTrace_646229 : CollatzResearch.WordTrace tailWord_646229 prefixEnd_646229 294956524332850986458269 := by
  unfold tailWord_646229
  simp only [CollatzResearch.WordTrace]
  refine ⟨23569907975830174971533741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15713271983886783314355827 23569907975830174971533741)
  ·
    refine ⟨8838715490936315614325153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23569907975830174971533741 8838715490936315614325153)
    ·
      refine ⟨6629036618202236710743865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8838715490936315614325153 6629036618202236710743865)
      ·
        refine ⟨4971777463651677533057899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6629036618202236710743865 4971777463651677533057899)
        ·
          refine ⟨7457666195477516299586849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4971777463651677533057899 7457666195477516299586849)
          ·
            refine ⟨5593249646608137224690137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7457666195477516299586849 5593249646608137224690137)
            ·
              refine ⟨4194937234956102918517603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5593249646608137224690137 4194937234956102918517603)
              ·
                refine ⟨6292405852434154377776405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4194937234956102918517603 6292405852434154377776405)
                ·
                  refine ⟨294956524332850986458269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6292405852434154377776405 294956524332850986458269)
                  ·
                    rfl

theorem cell20_646229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_646229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646229 prefixEnd_646229 := by exact prefixLift 646229
  have htrace : WordTrace (prefixWord ++ tailWord_646229) baseStart_646229 baseEnd_646229 := by
    simpa [prefixWord, tailWord_646229, baseEnd_646229] using wordTrace_append hprefix tailTrace_646229
  have hstable : (prefixWord ++ tailWord_646229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646229).length < 2 ^ (prefixWord ++ tailWord_646229).sum := by decide
  have hdescent : baseEnd_646229 < baseStart_646229 := by decide
  rcases family_descends (prefixWord ++ tailWord_646229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646301 : List Nat := [1, 4, 2, 1, 1, 2, 4, 3, 2]
def baseStart_646301 : Nat := 118140960795 + 646301 * 2 ^ 59
def prefixEnd_646301 : Nat := 4983230072969 + 3 ^ 40 * 646301 * 2
def baseEnd_646301 : Nat := 294989387094738736057975

theorem tailTrace_646301 : CollatzResearch.WordTrace tailWord_646301 prefixEnd_646301 294989387094738736057975 := by
  unfold tailWord_646301
  simp only [CollatzResearch.WordTrace]
  refine ⟨23572534031569331268154757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15715022687712887512103171 23572534031569331268154757)
  ·
    refine ⟨4419850130919249612779017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23572534031569331268154757 4419850130919249612779017)
    ·
      refine ⟨3314887598189437209584263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4419850130919249612779017 3314887598189437209584263)
      ·
        refine ⟨4972331397284155814376395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3314887598189437209584263 4972331397284155814376395)
        ·
          refine ⟨7458497095926233721564593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4972331397284155814376395 7458497095926233721564593)
          ·
            refine ⟨5593872821944675291173445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7458497095926233721564593 5593872821944675291173445)
            ·
              refine ⟨1048851154114626617095021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5593872821944675291173445 1048851154114626617095021)
              ·
                refine ⟨393319182792984981410633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1048851154114626617095021 393319182792984981410633)
                ·
                  refine ⟨294989387094738736057975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393319182792984981410633 294989387094738736057975)
                  ·
                    rfl

theorem cell20_646301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_646301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646301 prefixEnd_646301 := by exact prefixLift 646301
  have htrace : WordTrace (prefixWord ++ tailWord_646301) baseStart_646301 baseEnd_646301 := by
    simpa [prefixWord, tailWord_646301, baseEnd_646301] using wordTrace_append hprefix tailTrace_646301
  have hstable : (prefixWord ++ tailWord_646301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646301).length < 2 ^ (prefixWord ++ tailWord_646301).sum := by decide
  have hdescent : baseEnd_646301 < baseStart_646301 := by decide
  rcases family_descends (prefixWord ++ tailWord_646301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646305 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 6]
def baseStart_646305 : Nat := 118140960795 + 646305 * 2 ^ 59
def prefixEnd_646305 : Nat := 4983230072969 + 3 ^ 40 * 646305 * 2
def baseEnd_646305 : Nat := 294991212803732499924625

theorem tailTrace_646305 : CollatzResearch.WordTrace tailWord_646305 prefixEnd_646305 294991212803732499924625 := by
  unfold tailWord_646305
  simp only [CollatzResearch.WordTrace]
  refine ⟨23572679923554839951300369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15715119949036559967533579 23572679923554839951300369)
  ·
    refine ⟨17679509942666129963475277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23572679923554839951300369 17679509942666129963475277)
    ·
      refine ⟨6629816228499798736303229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17679509942666129963475277 6629816228499798736303229)
      ·
        refine ⟨2486181085687424526113711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6629816228499798736303229 2486181085687424526113711)
        ·
          refine ⟨3729271628531136789170567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2486181085687424526113711 3729271628531136789170567)
          ·
            refine ⟨5593907442796705183755851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3729271628531136789170567 5593907442796705183755851)
            ·
              refine ⟨8390861164195057775633777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5593907442796705183755851 8390861164195057775633777)
              ·
                refine ⟨6293145873146293331725333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8390861164195057775633777 6293145873146293331725333)
                ·
                  refine ⟨294991212803732499924625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6293145873146293331725333 294991212803732499924625)
                  ·
                    rfl

theorem cell20_646305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_646305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646305 prefixEnd_646305 := by exact prefixLift 646305
  have htrace : WordTrace (prefixWord ++ tailWord_646305) baseStart_646305 baseEnd_646305 := by
    simpa [prefixWord, tailWord_646305, baseEnd_646305] using wordTrace_append hprefix tailTrace_646305
  have hstable : (prefixWord ++ tailWord_646305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646305).length < 2 ^ (prefixWord ++ tailWord_646305).sum := by decide
  have hdescent : baseEnd_646305 < baseStart_646305 := by decide
  rcases family_descends (prefixWord ++ tailWord_646305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646322 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_646322 : Nat := 118140960795 + 646322 * 2 ^ 59
def prefixEnd_646322 : Nat := 4983230072969 + 3 ^ 40 * 646322 * 2
def baseEnd_646322 : Nat := 294998972066955996357889

theorem tailTrace_646322 : CollatzResearch.WordTrace tailWord_646322 prefixEnd_646322 294998972066955996357889 := by
  unfold tailWord_646322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5893324991123312963667305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15715533309662167903112813 5893324991123312963667305)
  ·
    refine ⟨4419993743342484722750479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5893324991123312963667305 4419993743342484722750479)
    ·
      refine ⟨6629990615013727084125719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4419993743342484722750479 6629990615013727084125719)
      ·
        refine ⟨9944985922520590626188579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6629990615013727084125719 9944985922520590626188579)
        ·
          refine ⟨14917478883780885939282869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9944985922520590626188579 14917478883780885939282869)
          ·
            refine ⟨1398513645354458056807769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14917478883780885939282869 1398513645354458056807769)
            ·
              refine ⟨1048885234015843542605827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1398513645354458056807769 1048885234015843542605827)
              ·
                refine ⟨1573327851023765313908741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048885234015843542605827 1573327851023765313908741)
                ·
                  refine ⟨294998972066955996357889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1573327851023765313908741 294998972066955996357889)
                  ·
                    rfl

theorem cell20_646322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_646322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646322 prefixEnd_646322 := by exact prefixLift 646322
  have htrace : WordTrace (prefixWord ++ tailWord_646322) baseStart_646322 baseEnd_646322 := by
    simpa [prefixWord, tailWord_646322, baseEnd_646322] using wordTrace_append hprefix tailTrace_646322
  have hstable : (prefixWord ++ tailWord_646322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646322).length < 2 ^ (prefixWord ++ tailWord_646322).sum := by decide
  have hdescent : baseEnd_646322 < baseStart_646322 := by decide
  rcases family_descends (prefixWord ++ tailWord_646322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646332 : List Nat := [2, 2, 2, 3, 2, 2, 3, 1, 3]
def baseStart_646332 : Nat := 118140960795 + 646332 * 2 ^ 59
def prefixEnd_646332 : Nat := 4983230072969 + 3 ^ 40 * 646332 * 2
def baseEnd_646332 : Nat := 295003536339440406024515

theorem tailTrace_646332 : CollatzResearch.WordTrace tailWord_646332 prefixEnd_646332 295003536339440406024515 := by
  unfold tailWord_646332
  simp only [CollatzResearch.WordTrace]
  refine ⟨11786832347228511781266625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15715776462971349041688833 11786832347228511781266625)
  ·
    refine ⟨8840124260421383835949969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11786832347228511781266625 8840124260421383835949969)
    ·
      refine ⟨6630093195316037876962477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8840124260421383835949969 6630093195316037876962477)
      ·
        refine ⟨2486284948243514203860929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6630093195316037876962477 2486284948243514203860929)
        ·
          refine ⟨1864713711182635652895697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2486284948243514203860929 1864713711182635652895697)
          ·
            refine ⟨1398535283386976739671773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1864713711182635652895697 1398535283386976739671773)
            ·
              refine ⟨524450731270116277376915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1398535283386976739671773 524450731270116277376915)
              ·
                refine ⟨786676096905174416065373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524450731270116277376915 786676096905174416065373)
                ·
                  refine ⟨295003536339440406024515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 786676096905174416065373 295003536339440406024515)
                  ·
                    rfl

theorem cell20_646332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_646332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646332 prefixEnd_646332 := by exact prefixLift 646332
  have htrace : WordTrace (prefixWord ++ tailWord_646332) baseStart_646332 baseEnd_646332 := by
    simpa [prefixWord, tailWord_646332, baseEnd_646332] using wordTrace_append hprefix tailTrace_646332
  have hstable : (prefixWord ++ tailWord_646332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646332).length < 2 ^ (prefixWord ++ tailWord_646332).sum := by decide
  have hdescent : baseEnd_646332 < baseStart_646332 := by decide
  rcases family_descends (prefixWord ++ tailWord_646332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646342 : List Nat := [6, 1, 2, 2, 1, 1, 1, 6]
def baseStart_646342 : Nat := 118140960795 + 646342 * 2 ^ 59
def prefixEnd_646342 : Nat := 4983230072969 + 3 ^ 40 * 646342 * 2
def baseEnd_646342 : Nat := 98336033537308271897047

theorem tailTrace_646342 : CollatzResearch.WordTrace tailWord_646342 prefixEnd_646342 98336033537308271897047 := by
  unfold tailWord_646342
  simp only [CollatzResearch.WordTrace]
  refine ⟨736688419513149852199915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15716019616280530180264853 736688419513149852199915)
  ·
    refine ⟨1105032629269724778299873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 736688419513149852199915 1105032629269724778299873)
    ·
      refine ⟨828774471952293583724905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1105032629269724778299873 828774471952293583724905)
      ·
        refine ⟨621580853964220187793679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 828774471952293583724905 621580853964220187793679)
        ·
          refine ⟨932371280946330281690519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621580853964220187793679 932371280946330281690519)
          ·
            refine ⟨1398556921419495422535779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932371280946330281690519 1398556921419495422535779)
            ·
              refine ⟨2097835382129243133803669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1398556921419495422535779 2097835382129243133803669)
              ·
                refine ⟨98336033537308271897047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2097835382129243133803669 98336033537308271897047)
                ·
                  rfl

theorem cell20_646342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_646342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646342 prefixEnd_646342 := by exact prefixLift 646342
  have htrace : WordTrace (prefixWord ++ tailWord_646342) baseStart_646342 baseEnd_646342 := by
    simpa [prefixWord, tailWord_646342, baseEnd_646342] using wordTrace_append hprefix tailTrace_646342
  have hstable : (prefixWord ++ tailWord_646342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646342).length < 2 ^ (prefixWord ++ tailWord_646342).sum := by decide
  have hdescent : baseEnd_646342 < baseStart_646342 := by decide
  rcases family_descends (prefixWord ++ tailWord_646342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646346 : List Nat := [3, 1, 2, 1, 3, 4, 2, 4]
def baseStart_646346 : Nat := 118140960795 + 646346 * 2 ^ 59
def prefixEnd_646346 : Nat := 4983230072969 + 3 ^ 40 * 646346 * 2
def baseEnd_646346 : Nat := 98336642106972859852597

theorem tailTrace_646346 : CollatzResearch.WordTrace tailWord_646346 prefixEnd_646346 98336642106972859852597 := by
  unfold tailWord_646346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5893543829101575988385723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15716116877604202635695261 5893543829101575988385723)
  ·
    refine ⟨8840315743652363982578585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5893543829101575988385723 8840315743652363982578585)
    ·
      refine ⟨6630236807739272986933939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8840315743652363982578585 6630236807739272986933939)
      ·
        refine ⟨9945355211608909480400909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6630236807739272986933939 9945355211608909480400909)
        ·
          refine ⟨3729508204353341055150341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9945355211608909480400909 3729508204353341055150341)
          ·
            refine ⟨699282788316251447840689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3729508204353341055150341 699282788316251447840689)
            ·
              refine ⟨524462091237188585880517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699282788316251447840689 524462091237188585880517)
              ·
                refine ⟨98336642106972859852597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 524462091237188585880517 98336642106972859852597)
                ·
                  rfl

theorem cell20_646346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_646346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646346 prefixEnd_646346 := by exact prefixLift 646346
  have htrace : WordTrace (prefixWord ++ tailWord_646346) baseStart_646346 baseEnd_646346 := by
    simpa [prefixWord, tailWord_646346, baseEnd_646346] using wordTrace_append hprefix tailTrace_646346
  have hstable : (prefixWord ++ tailWord_646346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646346).length < 2 ^ (prefixWord ++ tailWord_646346).sum := by decide
  have hdescent : baseEnd_646346 < baseStart_646346 := by decide
  rcases family_descends (prefixWord ++ tailWord_646346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646426 : List Nat := [3, 1, 1, 3, 3, 9]
def baseStart_646426 : Nat := 118140960795 + 646426 * 2 ^ 59
def prefixEnd_646426 : Nat := 4983230072969 + 3 ^ 40 * 646426 * 2
def baseEnd_646426 : Nat := 10927645944473846551511

theorem tailTrace_646426 : CollatzResearch.WordTrace tailWord_646426 prefixEnd_646426 10927645944473846551511 := by
  unfold tailWord_646426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5894273289029119404113783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15718062104077651744303421 5894273289029119404113783)
  ·
    refine ⟨8841409933543679106170675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5894273289029119404113783 8841409933543679106170675)
    ·
      refine ⟨13262114900315518659256013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8841409933543679106170675 13262114900315518659256013)
      ·
        refine ⟨4973293087618319497221005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13262114900315518659256013 4973293087618319497221005)
        ·
          refine ⟨1864984907856869811457877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4973293087618319497221005 1864984907856869811457877)
          ·
            refine ⟨10927645944473846551511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1864984907856869811457877 10927645944473846551511)
            ·
              rfl

theorem cell20_646426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 9].length) (baseStart_646426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646426 prefixEnd_646426 := by exact prefixLift 646426
  have htrace : WordTrace (prefixWord ++ tailWord_646426) baseStart_646426 baseEnd_646426 := by
    simpa [prefixWord, tailWord_646426, baseEnd_646426] using wordTrace_append hprefix tailTrace_646426
  have hstable : (prefixWord ++ tailWord_646426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646426).length < 2 ^ (prefixWord ++ tailWord_646426).sum := by decide
  have hdescent : baseEnd_646426 < baseStart_646426 := by decide
  rcases family_descends (prefixWord ++ tailWord_646426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646429 : List Nat := [1, 4, 2, 3, 1, 1, 1, 4, 3]
def baseStart_646429 : Nat := 118140960795 + 646429 * 2 ^ 59
def prefixEnd_646429 : Nat := 4983230072969 + 3 ^ 40 * 646429 * 2
def baseEnd_646429 : Nat := 295047809782539179790785

theorem tailTrace_646429 : CollatzResearch.WordTrace tailWord_646429 prefixEnd_646429 295047809782539179790785 := by
  unfold tailWord_646429
  simp only [CollatzResearch.WordTrace]
  refine ⟨23577202575105609128814341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15718135050070406085876227 23577202575105609128814341)
  ·
    refine ⟨4420725482832301711652689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23577202575105609128814341 4420725482832301711652689)
    ·
      refine ⟨3315544112124226283739517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4420725482832301711652689 3315544112124226283739517)
      ·
        refine ⟨1243329042046584856402319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3315544112124226283739517 1243329042046584856402319)
        ·
          refine ⟨1864993563069877284603479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1243329042046584856402319 1864993563069877284603479)
          ·
            refine ⟨2797490344604815926905219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864993563069877284603479 2797490344604815926905219)
            ·
              refine ⟨4196235516907223890357829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797490344604815926905219 4196235516907223890357829)
              ·
                refine ⟨786794159420104479442093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4196235516907223890357829 786794159420104479442093)
                ·
                  refine ⟨295047809782539179790785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 786794159420104479442093 295047809782539179790785)
                  ·
                    rfl

theorem cell20_646429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_646429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646429 prefixEnd_646429 := by exact prefixLift 646429
  have htrace : WordTrace (prefixWord ++ tailWord_646429) baseStart_646429 baseEnd_646429 := by
    simpa [prefixWord, tailWord_646429, baseEnd_646429] using wordTrace_append hprefix tailTrace_646429
  have hstable : (prefixWord ++ tailWord_646429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646429).length < 2 ^ (prefixWord ++ tailWord_646429).sum := by decide
  have hdescent : baseEnd_646429 < baseStart_646429 := by decide
  rcases family_descends (prefixWord ++ tailWord_646429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646546 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_646546 : Nat := 118140960795 + 646546 * 2 ^ 59
def prefixEnd_646546 : Nat := 4983230072969 + 3 ^ 40 * 646546 * 2
def baseEnd_646546 : Nat := 295101211770606772890307

theorem tailTrace_646546 : CollatzResearch.WordTrace tailWord_646546 prefixEnd_646546 295101211770606772890307 := by
  unfold tailWord_646546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5895367478920434527705873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15720979943787825407215661 5895367478920434527705873)
  ·
    refine ⟨4421525609190325895779405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5895367478920434527705873 4421525609190325895779405)
    ·
      refine ⟨1658072103446372210917277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4421525609190325895779405 1658072103446372210917277)
      ·
        refine ⟨621777038792389579093979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1658072103446372210917277 621777038792389579093979)
        ·
          refine ⟨932665558188584368640969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621777038792389579093979 932665558188584368640969)
          ·
            refine ⟨699499168641438276480727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 932665558188584368640969 699499168641438276480727)
            ·
              refine ⟨1049248752962157414721091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699499168641438276480727 1049248752962157414721091)
              ·
                refine ⟨1573873129443236122081637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049248752962157414721091 1573873129443236122081637)
                ·
                  refine ⟨295101211770606772890307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1573873129443236122081637 295101211770606772890307)
                  ·
                    rfl

theorem cell20_646546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_646546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646546 prefixEnd_646546 := by exact prefixLift 646546
  have htrace : WordTrace (prefixWord ++ tailWord_646546) baseStart_646546 baseEnd_646546 := by
    simpa [prefixWord, tailWord_646546, baseEnd_646546] using wordTrace_append hprefix tailTrace_646546
  have hstable : (prefixWord ++ tailWord_646546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646546).length < 2 ^ (prefixWord ++ tailWord_646546).sum := by decide
  have hdescent : baseEnd_646546 < baseStart_646546 := by decide
  rcases family_descends (prefixWord ++ tailWord_646546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646556 : List Nat := [2, 2, 3, 4, 2, 1, 2, 1, 3]
def baseStart_646556 : Nat := 118140960795 + 646556 * 2 ^ 59
def prefixEnd_646556 : Nat := 4983230072969 + 3 ^ 40 * 646556 * 2
def baseEnd_646556 : Nat := 295105776043091182556933

theorem tailTrace_646556 : CollatzResearch.WordTrace tailWord_646556 prefixEnd_646556 295105776043091182556933 := by
  unfold tailWord_646556
  simp only [CollatzResearch.WordTrace]
  refine ⟨11790917322822754909343761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15721223097097006545791681 11790917322822754909343761)
  ·
    refine ⟨8843187992117066182007821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11790917322822754909343761 8843187992117066182007821)
    ·
      refine ⟨3316195497043899818252933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8843187992117066182007821 3316195497043899818252933)
      ·
        refine ⟨621786655695731215922425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3316195497043899818252933 621786655695731215922425)
        ·
          refine ⟨466339991771798411941819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 621786655695731215922425 466339991771798411941819)
          ·
            refine ⟨699509987657697617912729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466339991771798411941819 699509987657697617912729)
            ·
              refine ⟨524632490743273213434547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699509987657697617912729 524632490743273213434547)
              ·
                refine ⟨786948736114909820151821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524632490743273213434547 786948736114909820151821)
                ·
                  refine ⟨295105776043091182556933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 786948736114909820151821 295105776043091182556933)
                  ·
                    rfl

theorem cell20_646556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_646556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646556 prefixEnd_646556 := by exact prefixLift 646556
  have htrace : WordTrace (prefixWord ++ tailWord_646556) baseStart_646556 baseEnd_646556 := by
    simpa [prefixWord, tailWord_646556, baseEnd_646556] using wordTrace_append hprefix tailTrace_646556
  have hstable : (prefixWord ++ tailWord_646556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646556).length < 2 ^ (prefixWord ++ tailWord_646556).sum := by decide
  have hdescent : baseEnd_646556 < baseStart_646556 := by decide
  rcases family_descends (prefixWord ++ tailWord_646556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646557 : List Nat := [1, 4, 2, 1, 3, 2, 2, 5]
def baseStart_646557 : Nat := 118140960795 + 646557 * 2 ^ 59
def prefixEnd_646557 : Nat := 4983230072969 + 3 ^ 40 * 646557 * 2
def baseEnd_646557 : Nat := 98368744156779874507865

theorem tailTrace_646557 : CollatzResearch.WordTrace tailWord_646557 prefixEnd_646557 98368744156779874507865 := by
  unfold tailWord_646557
  simp only [CollatzResearch.WordTrace]
  refine ⟨23581871118641886989473925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15721247412427924659649283 23581871118641886989473925)
  ·
    refine ⟨4421600834745353810526361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23581871118641886989473925 4421600834745353810526361)
    ·
      refine ⟨3316200626059015357894771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4421600834745353810526361 3316200626059015357894771)
      ·
        refine ⟨4974300939088523036842157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3316200626059015357894771 4974300939088523036842157)
        ·
          refine ⟨1865362852158196138815809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4974300939088523036842157 1865362852158196138815809)
          ·
            refine ⟨1399022139118647104111857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1865362852158196138815809 1399022139118647104111857)
            ·
              refine ⟨1049266604338985328083893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1399022139118647104111857 1049266604338985328083893)
              ·
                refine ⟨98368744156779874507865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1049266604338985328083893 98368744156779874507865)
                ·
                  rfl

theorem cell20_646557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_646557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646557 prefixEnd_646557 := by exact prefixLift 646557
  have htrace : WordTrace (prefixWord ++ tailWord_646557) baseStart_646557 baseEnd_646557 := by
    simpa [prefixWord, tailWord_646557, baseEnd_646557] using wordTrace_append hprefix tailTrace_646557
  have hstable : (prefixWord ++ tailWord_646557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646557).length < 2 ^ (prefixWord ++ tailWord_646557).sum := by decide
  have hdescent : baseEnd_646557 < baseStart_646557 := by decide
  rcases family_descends (prefixWord ++ tailWord_646557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646602 : List Nat := [3, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_646602 : Nat := 118140960795 + 646602 * 2 ^ 59
def prefixEnd_646602 : Nat := 4983230072969 + 3 ^ 40 * 646602 * 2
def baseEnd_646602 : Nat := 295126771696519467023411

theorem tailTrace_646602 : CollatzResearch.WordTrace tailWord_646602 prefixEnd_646602 295126771696519467023411 := by
  unfold tailWord_646602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5895878100869714918715515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15722341602319239783241373 5895878100869714918715515)
  ·
    refine ⟨8843817151304572378073273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5895878100869714918715515 8843817151304572378073273)
    ·
      refine ⟨6632862863478429283554955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8843817151304572378073273 6632862863478429283554955)
      ·
        refine ⟨9949294295217643925332433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6632862863478429283554955 9949294295217643925332433)
        ·
          refine ⟨7461970721413232943999325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9949294295217643925332433 7461970721413232943999325)
          ·
            refine ⟨2798239020529962353999747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7461970721413232943999325 2798239020529962353999747)
            ·
              refine ⟨4197358530794943530999621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798239020529962353999747 4197358530794943530999621)
              ·
                refine ⟨787004724524051912062429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4197358530794943530999621 787004724524051912062429)
                ·
                  refine ⟨295126771696519467023411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 787004724524051912062429 295126771696519467023411)
                  ·
                    rfl

theorem cell20_646602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_646602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646602 prefixEnd_646602 := by exact prefixLift 646602
  have htrace : WordTrace (prefixWord ++ tailWord_646602) baseStart_646602 baseEnd_646602 := by
    simpa [prefixWord, tailWord_646602, baseEnd_646602] using wordTrace_append hprefix tailTrace_646602
  have hstable : (prefixWord ++ tailWord_646602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646602).length < 2 ^ (prefixWord ++ tailWord_646602).sum := by decide
  have hdescent : baseEnd_646602 < baseStart_646602 := by decide
  rcases family_descends (prefixWord ++ tailWord_646602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646612 : List Nat := [2, 4, 1, 2, 3, 2, 1, 5]
def baseStart_646612 : Nat := 118140960795 + 646612 * 2 ^ 59
def prefixEnd_646612 : Nat := 4983230072969 + 3 ^ 40 * 646612 * 2
def baseEnd_646612 : Nat := 98377111989667958896679

theorem tailTrace_646612 : CollatzResearch.WordTrace tailWord_646612 prefixEnd_646612 98377111989667958896679 := by
  unfold tailWord_646612
  simp only [CollatzResearch.WordTrace]
  refine ⟨11791938566721315691363045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15722584755628420921817393 11791938566721315691363045)
  ·
    refine ⟨2210988481260246692130571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11791938566721315691363045 2210988481260246692130571)
    ·
      refine ⟨3316482721890370038195857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2210988481260246692130571 3316482721890370038195857)
      ·
        refine ⟨2487362041417777528646893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3316482721890370038195857 2487362041417777528646893)
        ·
          refine ⟨932760765531666573242585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2487362041417777528646893 932760765531666573242585)
          ·
            refine ⟨699570574148749929931939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 932760765531666573242585 699570574148749929931939)
            ·
              refine ⟨1049355861223124894897909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699570574148749929931939 1049355861223124894897909)
              ·
                refine ⟨98377111989667958896679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1049355861223124894897909 98377111989667958896679)
                ·
                  rfl

theorem cell20_646612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_646612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646612 prefixEnd_646612 := by exact prefixLift 646612
  have htrace : WordTrace (prefixWord ++ tailWord_646612) baseStart_646612 baseEnd_646612 := by
    simpa [prefixWord, tailWord_646612, baseEnd_646612] using wordTrace_append hprefix tailTrace_646612
  have hstable : (prefixWord ++ tailWord_646612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646612).length < 2 ^ (prefixWord ++ tailWord_646612).sum := by decide
  have hdescent : baseEnd_646612 < baseStart_646612 := by decide
  rcases family_descends (prefixWord ++ tailWord_646612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646616 : List Nat := [2, 1, 2, 2, 2, 1, 5, 5]
def baseStart_646616 : Nat := 118140960795 + 646616 * 2 ^ 59
def prefixEnd_646616 : Nat := 4983230072969 + 3 ^ 40 * 646616 * 2
def baseEnd_646616 : Nat := 98377720559332546852229

theorem tailTrace_646616 : CollatzResearch.WordTrace tailWord_646616 prefixEnd_646616 98377720559332546852229 := by
  unfold tailWord_646616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11792011512714070032935851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15722682016952093377247801 11792011512714070032935851)
  ·
    refine ⟨17688017269071105049403777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11792011512714070032935851 17688017269071105049403777)
    ·
      refine ⟨13266012951803328787052833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17688017269071105049403777 13266012951803328787052833)
      ·
        refine ⟨9949509713852496590289625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13266012951803328787052833 9949509713852496590289625)
        ·
          refine ⟨7462132285389372442717219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9949509713852496590289625 7462132285389372442717219)
          ·
            refine ⟨11193198428084058664075829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7462132285389372442717219 11193198428084058664075829)
            ·
              refine ⟨1049362352632880499757109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11193198428084058664075829 1049362352632880499757109)
              ·
                refine ⟨98377720559332546852229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1049362352632880499757109 98377720559332546852229)
                ·
                  rfl

theorem cell20_646616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_646616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646616 prefixEnd_646616 := by exact prefixLift 646616
  have htrace : WordTrace (prefixWord ++ tailWord_646616) baseStart_646616 baseEnd_646616 := by
    simpa [prefixWord, tailWord_646616, baseEnd_646616] using wordTrace_append hprefix tailTrace_646616
  have hstable : (prefixWord ++ tailWord_646616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646616).length < 2 ^ (prefixWord ++ tailWord_646616).sum := by decide
  have hdescent : baseEnd_646616 < baseStart_646616 := by decide
  rcases family_descends (prefixWord ++ tailWord_646616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646664 : List Nat := [2, 1, 3, 2, 1, 1, 4, 4, 2]
def baseStart_646664 : Nat := 118140960795 + 646664 * 2 ^ 59
def prefixEnd_646664 : Nat := 4983230072969 + 3 ^ 40 * 646664 * 2
def baseEnd_646664 : Nat := 295155070185922806956491

theorem tailTrace_646664 : CollatzResearch.WordTrace tailWord_646664 prefixEnd_646664 295155070185922806956491 := by
  unfold tailWord_646664
  simp only [CollatzResearch.WordTrace]
  refine ⟨11792886864627122131809523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15723849152836162842412697 11792886864627122131809523)
  ·
    refine ⟨17689330296940683197714285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11792886864627122131809523 17689330296940683197714285)
    ·
      refine ⟨6633498861352756199142857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17689330296940683197714285 6633498861352756199142857)
      ·
        refine ⟨4975124146014567149357143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6633498861352756199142857 4975124146014567149357143)
        ·
          refine ⟨7462686219021850724035715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4975124146014567149357143 7462686219021850724035715)
          ·
            refine ⟨11194029328532776086053573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7462686219021850724035715 11194029328532776086053573)
            ·
              refine ⟨2098880499099895516135045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11194029328532776086053573 2098880499099895516135045)
              ·
                refine ⟨393540093581230409275321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2098880499099895516135045 393540093581230409275321)
                ·
                  refine ⟨295155070185922806956491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393540093581230409275321 295155070185922806956491)
                  ·
                    rfl

theorem cell20_646664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 2].length) (baseStart_646664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646664 prefixEnd_646664 := by exact prefixLift 646664
  have htrace : WordTrace (prefixWord ++ tailWord_646664) baseStart_646664 baseEnd_646664 := by
    simpa [prefixWord, tailWord_646664, baseEnd_646664] using wordTrace_append hprefix tailTrace_646664
  have hstable : (prefixWord ++ tailWord_646664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646664).length < 2 ^ (prefixWord ++ tailWord_646664).sum := by decide
  have hdescent : baseEnd_646664 < baseStart_646664 := by decide
  rcases family_descends (prefixWord ++ tailWord_646664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646685 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 4]
def baseStart_646685 : Nat := 118140960795 + 646685 * 2 ^ 59
def prefixEnd_646685 : Nat := 4983230072969 + 3 ^ 40 * 646685 * 2
def baseEnd_646685 : Nat := 295164655158140067256405

theorem tailTrace_646685 : CollatzResearch.WordTrace tailWord_646685 prefixEnd_646685 295164655158140067256405 := by
  unfold tailWord_646685
  simp only [CollatzResearch.WordTrace]
  refine ⟨23586539662178164850133509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15724359774785443233422339 23586539662178164850133509)
  ·
    refine ⟨4422476186658405909400033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23586539662178164850133509 4422476186658405909400033)
    ·
      refine ⟨3316857139993804432050025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4422476186658405909400033 3316857139993804432050025)
      ·
        refine ⟨2487642854995353324037519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3316857139993804432050025 2487642854995353324037519)
        ·
          refine ⟨3731464282493029986056279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487642854995353324037519 3731464282493029986056279)
          ·
            refine ⟨5597196423739544979084419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731464282493029986056279 5597196423739544979084419)
            ·
              refine ⟨8395794635609317468626629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5597196423739544979084419 8395794635609317468626629)
              ·
                refine ⟨1574211494176747025367493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8395794635609317468626629 1574211494176747025367493)
                ·
                  refine ⟨295164655158140067256405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1574211494176747025367493 295164655158140067256405)
                  ·
                    rfl

theorem cell20_646685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_646685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646685 prefixEnd_646685 := by exact prefixLift 646685
  have htrace : WordTrace (prefixWord ++ tailWord_646685) baseStart_646685 baseEnd_646685 := by
    simpa [prefixWord, tailWord_646685, baseEnd_646685] using wordTrace_append hprefix tailTrace_646685
  have hstable : (prefixWord ++ tailWord_646685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646685).length < 2 ^ (prefixWord ++ tailWord_646685).sum := by decide
  have hdescent : baseEnd_646685 < baseStart_646685 := by decide
  rcases family_descends (prefixWord ++ tailWord_646685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646688 : List Nat := [2, 1, 1, 6, 1, 3, 2, 4]
def baseStart_646688 : Nat := 118140960795 + 646688 * 2 ^ 59
def prefixEnd_646688 : Nat := 4983230072969 + 3 ^ 40 * 646688 * 2
def baseEnd_646688 : Nat := 98388674813295130052131

theorem tailTrace_646688 : CollatzResearch.WordTrace tailWord_646688 prefixEnd_646688 98388674813295130052131 := by
  unfold tailWord_646688
  simp only [CollatzResearch.WordTrace]
  refine ⟨11793324540583648181246359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15724432720778197574995145 11793324540583648181246359)
  ·
    refine ⟨17689986810875472271869539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11793324540583648181246359 17689986810875472271869539)
    ·
      refine ⟨26534980216313208407804309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17689986810875472271869539 26534980216313208407804309)
      ·
        refine ⟨1243827197639681644115827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26534980216313208407804309 1243827197639681644115827)
        ·
          refine ⟨1865740796459522466173741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1243827197639681644115827 1865740796459522466173741)
          ·
            refine ⟨699652798672320924815153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1865740796459522466173741 699652798672320924815153)
            ·
              refine ⟨524739599004240693611365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699652798672320924815153 524739599004240693611365)
              ·
                refine ⟨98388674813295130052131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 524739599004240693611365 98388674813295130052131)
                ·
                  rfl

theorem cell20_646688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_646688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646688 prefixEnd_646688 := by exact prefixLift 646688
  have htrace : WordTrace (prefixWord ++ tailWord_646688) baseStart_646688 baseEnd_646688 := by
    simpa [prefixWord, tailWord_646688, baseEnd_646688] using wordTrace_append hprefix tailTrace_646688
  have hstable : (prefixWord ++ tailWord_646688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646688).length < 2 ^ (prefixWord ++ tailWord_646688).sum := by decide
  have hdescent : baseEnd_646688 < baseStart_646688 := by decide
  rcases family_descends (prefixWord ++ tailWord_646688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646719 : List Nat := [1, 1, 2, 2, 3, 4, 3, 2, 2]
def baseStart_646719 : Nat := 118140960795 + 646719 * 2 ^ 59
def prefixEnd_646719 : Nat := 4983230072969 + 3 ^ 40 * 646719 * 2
def baseEnd_646719 : Nat := 295180173684587060122933

theorem tailTrace_646719 : CollatzResearch.WordTrace tailWord_646719 prefixEnd_646719 295180173684587060122933 := by
  unfold tailWord_646719
  simp only [CollatzResearch.WordTrace]
  refine ⟨23587779744054988656871211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15725186496036659104580807 23587779744054988656871211)
  ·
    refine ⟨35381669616082482985306817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23587779744054988656871211 35381669616082482985306817)
    ·
      refine ⟨26536252212061862238980113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35381669616082482985306817 26536252212061862238980113)
      ·
        refine ⟨19902189159046396679235085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26536252212061862238980113 19902189159046396679235085)
        ·
          refine ⟨7463320934642398754713157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19902189159046396679235085 7463320934642398754713157)
          ·
            refine ⟨1399372675245449766508717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7463320934642398754713157 1399372675245449766508717)
            ·
              refine ⟨524764753217043662440769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1399372675245449766508717 524764753217043662440769)
              ·
                refine ⟨393573564912782746830577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524764753217043662440769 393573564912782746830577)
                ·
                  refine ⟨295180173684587060122933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393573564912782746830577 295180173684587060122933)
                  ·
                    rfl

theorem cell20_646719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 2].length) (baseStart_646719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646719 prefixEnd_646719 := by exact prefixLift 646719
  have htrace : WordTrace (prefixWord ++ tailWord_646719) baseStart_646719 baseEnd_646719 := by
    simpa [prefixWord, tailWord_646719, baseEnd_646719] using wordTrace_append hprefix tailTrace_646719
  have hstable : (prefixWord ++ tailWord_646719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646719).length < 2 ^ (prefixWord ++ tailWord_646719).sum := by decide
  have hdescent : baseEnd_646719 < baseStart_646719 := by decide
  rcases family_descends (prefixWord ++ tailWord_646719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646730 : List Nat := [3, 1, 2, 1, 1, 3, 4, 5]
def baseStart_646730 : Nat := 118140960795 + 646730 * 2 ^ 59
def prefixEnd_646730 : Nat := 4983230072969 + 3 ^ 40 * 646730 * 2
def baseEnd_646730 : Nat := 98395064794773303585407

theorem tailTrace_646730 : CollatzResearch.WordTrace tailWord_646730 prefixEnd_646730 98395064794773303585407 := by
  unfold tailWord_646730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5897045236753784383880411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15725453964676758357014429 5897045236753784383880411)
  ·
    refine ⟨8845567855130676575820617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5897045236753784383880411 8845567855130676575820617)
    ·
      refine ⟨6634175891348007431865463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8845567855130676575820617 6634175891348007431865463)
      ·
        refine ⟨9951263837022011147798195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6634175891348007431865463 9951263837022011147798195)
        ·
          refine ⟨14926895755533016721697293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9951263837022011147798195 14926895755533016721697293)
          ·
            refine ⟨5597585908324881270636485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14926895755533016721697293 5597585908324881270636485)
            ·
              refine ⟨1049547357810915238244341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5597585908324881270636485 1049547357810915238244341)
              ·
                refine ⟨98395064794773303585407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1049547357810915238244341 98395064794773303585407)
                ·
                  rfl

theorem cell20_646730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_646730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646730 prefixEnd_646730 := by exact prefixLift 646730
  have htrace : WordTrace (prefixWord ++ tailWord_646730) baseStart_646730 baseEnd_646730 := by
    simpa [prefixWord, tailWord_646730, baseEnd_646730] using wordTrace_append hprefix tailTrace_646730
  have hstable : (prefixWord ++ tailWord_646730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646730).length < 2 ^ (prefixWord ++ tailWord_646730).sum := by decide
  have hdescent : baseEnd_646730 < baseStart_646730 := by decide
  rcases family_descends (prefixWord ++ tailWord_646730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646744 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_646744 : Nat := 118140960795 + 646744 * 2 ^ 59
def prefixEnd_646744 : Nat := 4983230072969 + 3 ^ 40 * 646744 * 2
def baseEnd_646744 : Nat := 295191584365798084289497

theorem tailTrace_646744 : CollatzResearch.WordTrace tailWord_646744 prefixEnd_646744 295191584365798084289497 := by
  unfold tailWord_646744
  simp only [CollatzResearch.WordTrace]
  refine ⟨11794345784482208963265643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15725794379309611951020857 11794345784482208963265643)
  ·
    refine ⟨17691518676723313444898465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11794345784482208963265643 17691518676723313444898465)
    ·
      refine ⟨13268639007542485083673849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17691518676723313444898465 13268639007542485083673849)
      ·
        refine ⟨9951479255656863812755387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13268639007542485083673849 9951479255656863812755387)
        ·
          refine ⟨14927218883485295719133081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9951479255656863812755387 14927218883485295719133081)
          ·
            refine ⟨11195414162613971789349811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14927218883485295719133081 11195414162613971789349811)
            ·
              refine ⟨16793121243920957684024717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11195414162613971789349811 16793121243920957684024717)
              ·
                refine ⟨6297420466470359131509269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16793121243920957684024717 6297420466470359131509269)
                ·
                  refine ⟨295191584365798084289497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6297420466470359131509269 295191584365798084289497)
                  ·
                    rfl

theorem cell20_646744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_646744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646744 prefixEnd_646744 := by exact prefixLift 646744
  have htrace : WordTrace (prefixWord ++ tailWord_646744) baseStart_646744 baseEnd_646744 := by
    simpa [prefixWord, tailWord_646744, baseEnd_646744] using wordTrace_append hprefix tailTrace_646744
  have hstable : (prefixWord ++ tailWord_646744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646744).length < 2 ^ (prefixWord ++ tailWord_646744).sum := by decide
  have hdescent : baseEnd_646744 < baseStart_646744 := by decide
  rcases family_descends (prefixWord ++ tailWord_646744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646774 : List Nat := [5, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_646774 : Nat := 118140960795 + 646774 * 2 ^ 59
def prefixEnd_646774 : Nat := 4983230072969 + 3 ^ 40 * 646774 * 2
def baseEnd_646774 : Nat := 295205277183251313289375

theorem tailTrace_646774 : CollatzResearch.WordTrace tailWord_646774 prefixEnd_646774 295205277183251313289375 := by
  unfold tailWord_646774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1474361609928483315632711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15726523839237155366748917 1474361609928483315632711)
  ·
    refine ⟨2211542414892724973449067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1474361609928483315632711 2211542414892724973449067)
    ·
      refine ⟨3317313622339087460173601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2211542414892724973449067 3317313622339087460173601)
      ·
        refine ⟨2487985216754315595130201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3317313622339087460173601 2487985216754315595130201)
        ·
          refine ⟨1865988912565736696347651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2487985216754315595130201 1865988912565736696347651)
          ·
            refine ⟨2798983368848605044521477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865988912565736696347651 2798983368848605044521477)
            ·
              refine ⟨524809381659113445847777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2798983368848605044521477 524809381659113445847777)
              ·
                refine ⟨393607036244335084385833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524809381659113445847777 393607036244335084385833)
                ·
                  refine ⟨295205277183251313289375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393607036244335084385833 295205277183251313289375)
                  ·
                    rfl

theorem cell20_646774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_646774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646774 prefixEnd_646774 := by exact prefixLift 646774
  have htrace : WordTrace (prefixWord ++ tailWord_646774) baseStart_646774 baseEnd_646774 := by
    simpa [prefixWord, tailWord_646774, baseEnd_646774] using wordTrace_append hprefix tailTrace_646774
  have hstable : (prefixWord ++ tailWord_646774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646774).length < 2 ^ (prefixWord ++ tailWord_646774).sum := by decide
  have hdescent : baseEnd_646774 < baseStart_646774 := by decide
  rcases family_descends (prefixWord ++ tailWord_646774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646785 : List Nat := [1, 2, 4, 2, 1, 4, 1, 5]
def baseStart_646785 : Nat := 118140960795 + 646785 * 2 ^ 59
def prefixEnd_646785 : Nat := 4983230072969 + 3 ^ 40 * 646785 * 2
def baseEnd_646785 : Nat := 98403432627661387974221

theorem tailTrace_646785 : CollatzResearch.WordTrace tailWord_646785 prefixEnd_646785 98403432627661387974221 := by
  unfold tailWord_646785
  simp only [CollatzResearch.WordTrace]
  refine ⟨23590186961815881928773809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15726791307877254619182539 23590186961815881928773809)
  ·
    refine ⟨17692640221361911446580357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23590186961815881928773809 17692640221361911446580357)
    ·
      refine ⟨3317370041505358396233817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17692640221361911446580357 3317370041505358396233817)
      ·
        refine ⟨2488027531129018797175363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3317370041505358396233817 2488027531129018797175363)
        ·
          refine ⟨3732041296693528195763045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2488027531129018797175363 3732041296693528195763045)
          ·
            refine ⟨699757743130036536705571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3732041296693528195763045 699757743130036536705571)
            ·
              refine ⟨1049636614695054805058357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699757743130036536705571 1049636614695054805058357)
              ·
                refine ⟨98403432627661387974221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1049636614695054805058357 98403432627661387974221)
                ·
                  rfl

theorem cell20_646785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 5].length) (baseStart_646785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646785 prefixEnd_646785 := by exact prefixLift 646785
  have htrace : WordTrace (prefixWord ++ tailWord_646785) baseStart_646785 baseEnd_646785 := by
    simpa [prefixWord, tailWord_646785, baseEnd_646785] using wordTrace_append hprefix tailTrace_646785
  have hstable : (prefixWord ++ tailWord_646785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646785).length < 2 ^ (prefixWord ++ tailWord_646785).sum := by decide
  have hdescent : baseEnd_646785 < baseStart_646785 := by decide
  rcases family_descends (prefixWord ++ tailWord_646785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646802 : List Nat := [3, 2, 3, 1, 3, 1, 3, 4]
def baseStart_646802 : Nat := 118140960795 + 646802 * 2 ^ 59
def prefixEnd_646802 : Nat := 4983230072969 + 3 ^ 40 * 646802 * 2
def baseEnd_646802 : Nat := 98406019048735886785309

theorem tailTrace_646802 : CollatzResearch.WordTrace tailWord_646802 prefixEnd_646802 98406019048735886785309 := by
  unfold tailWord_646802
  simp only [CollatzResearch.WordTrace]
  refine ⟨5897701750688573458035665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15727204668502862554761773 5897701750688573458035665)
  ·
    refine ⟨4423276313016430093526749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5897701750688573458035665 4423276313016430093526749)
    ·
      refine ⟨1658728617381161285072531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4423276313016430093526749 1658728617381161285072531)
      ·
        refine ⟨2488092926071741927608797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1658728617381161285072531 2488092926071741927608797)
        ·
          refine ⟨933034847276903222853299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2488092926071741927608797 933034847276903222853299)
          ·
            refine ⟨1399552270915354834279949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933034847276903222853299 1399552270915354834279949)
            ·
              refine ⟨524832101593258062854981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1399552270915354834279949 524832101593258062854981)
              ·
                refine ⟨98406019048735886785309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 524832101593258062854981 98406019048735886785309)
                ·
                  rfl

theorem cell20_646802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_646802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646802 prefixEnd_646802 := by exact prefixLift 646802
  have htrace : WordTrace (prefixWord ++ tailWord_646802) baseStart_646802 baseEnd_646802 := by
    simpa [prefixWord, tailWord_646802, baseEnd_646802] using wordTrace_append hprefix tailTrace_646802
  have hstable : (prefixWord ++ tailWord_646802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646802).length < 2 ^ (prefixWord ++ tailWord_646802).sum := by decide
  have hdescent : baseEnd_646802 < baseStart_646802 := by decide
  rcases family_descends (prefixWord ++ tailWord_646802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646813 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 5]
def baseStart_646813 : Nat := 118140960795 + 646813 * 2 ^ 59
def prefixEnd_646813 : Nat := 4983230072969 + 3 ^ 40 * 646813 * 2
def baseEnd_646813 : Nat := 295223077845940510989215

theorem tailTrace_646813 : CollatzResearch.WordTrace tailWord_646813 prefixEnd_646813 295223077845940510989215 := by
  unfold tailWord_646813
  simp only [CollatzResearch.WordTrace]
  refine ⟨23591208205714442710793093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15727472137142961807195395 23591208205714442710793093)
  ·
    refine ⟨4423351538571458008273705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23591208205714442710793093 4423351538571458008273705)
    ·
      refine ⟨3317513653928593506205279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4423351538571458008273705 3317513653928593506205279)
      ·
        refine ⟨4976270480892890259307919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3317513653928593506205279 4976270480892890259307919)
        ·
          refine ⟨7464405721339335388961879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4976270480892890259307919 7464405721339335388961879)
          ·
            refine ⟨11196608582009003083442819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7464405721339335388961879 11196608582009003083442819)
            ·
              refine ⟨16794912873013504625164229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11196608582009003083442819 16794912873013504625164229)
              ·
                refine ⟨3149046163690032117218293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16794912873013504625164229 3149046163690032117218293)
                ·
                  refine ⟨295223077845940510989215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3149046163690032117218293 295223077845940510989215)
                  ·
                    rfl

theorem cell20_646813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_646813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646813 prefixEnd_646813 := by exact prefixLift 646813
  have htrace : WordTrace (prefixWord ++ tailWord_646813) baseStart_646813 baseEnd_646813 := by
    simpa [prefixWord, tailWord_646813, baseEnd_646813] using wordTrace_append hprefix tailTrace_646813
  have hstable : (prefixWord ++ tailWord_646813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646813).length < 2 ^ (prefixWord ++ tailWord_646813).sum := by decide
  have hdescent : baseEnd_646813 < baseStart_646813 := by decide
  rcases family_descends (prefixWord ++ tailWord_646813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646816 : List Nat := [2, 1, 1, 4, 3, 1, 1, 5, 2]
def baseStart_646816 : Nat := 118140960795 + 646816 * 2 ^ 59
def prefixEnd_646816 : Nat := 4983230072969 + 3 ^ 40 * 646816 * 2
def baseEnd_646816 : Nat := 295224447127685833889203

theorem tailTrace_646816 : CollatzResearch.WordTrace tailWord_646816 prefixEnd_646816 295224447127685833889203 := by
  unfold tailWord_646816
  simp only [CollatzResearch.WordTrace]
  refine ⟨11795658812351787111576151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15727545083135716148768201 11795658812351787111576151)
  ·
    refine ⟨17693488218527680667364227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11795658812351787111576151 17693488218527680667364227)
    ·
      refine ⟨26540232327791521001046341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17693488218527680667364227 26540232327791521001046341)
      ·
        refine ⟨4976293561460910187696189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26540232327791521001046341 4976293561460910187696189)
        ·
          refine ⟨1866110085547841320386071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4976293561460910187696189 1866110085547841320386071)
          ·
            refine ⟨2799165128321761980579107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1866110085547841320386071 2799165128321761980579107)
            ·
              refine ⟨4198747692482642970868661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799165128321761980579107 4198747692482642970868661)
              ·
                refine ⟨393632596170247778518937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4198747692482642970868661 393632596170247778518937)
                ·
                  refine ⟨295224447127685833889203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393632596170247778518937 295224447127685833889203)
                  ·
                    rfl

theorem cell20_646816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 2].length) (baseStart_646816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646816 prefixEnd_646816 := by exact prefixLift 646816
  have htrace : WordTrace (prefixWord ++ tailWord_646816) baseStart_646816 baseEnd_646816 := by
    simpa [prefixWord, tailWord_646816, baseEnd_646816] using wordTrace_append hprefix tailTrace_646816
  have hstable : (prefixWord ++ tailWord_646816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646816).length < 2 ^ (prefixWord ++ tailWord_646816).sum := by decide
  have hdescent : baseEnd_646816 < baseStart_646816 := by decide
  rcases family_descends (prefixWord ++ tailWord_646816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646868 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_646868 : Nat := 118140960795 + 646868 * 2 ^ 59
def prefixEnd_646868 : Nat := 4983230072969 + 3 ^ 40 * 646868 * 2
def baseEnd_646868 : Nat := 295248181344604764155657

theorem tailTrace_646868 : CollatzResearch.WordTrace tailWord_646868 prefixEnd_646868 295248181344604764155657 := by
  unfold tailWord_646868
  simp only [CollatzResearch.WordTrace]
  refine ⟨11796607110257593552022629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15728809480343458069363505 11796607110257593552022629)
  ·
    refine ⟨2211863833173298791004243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11796607110257593552022629 2211863833173298791004243)
    ·
      refine ⟨3317795749759948186506365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2211863833173298791004243 3317795749759948186506365)
      ·
        refine ⟨1244173406159980569939887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3317795749759948186506365 1244173406159980569939887)
        ·
          refine ⟨1866260109239970854909831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1244173406159980569939887 1866260109239970854909831)
          ·
            refine ⟨2799390163859956282364747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1866260109239970854909831 2799390163859956282364747)
            ·
              refine ⟨4199085245789934423547121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799390163859956282364747 4199085245789934423547121)
              ·
                refine ⟨3149313934342450817660341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4199085245789934423547121 3149313934342450817660341)
                ·
                  refine ⟨295248181344604764155657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3149313934342450817660341 295248181344604764155657)
                  ·
                    rfl

theorem cell20_646868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_646868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646868 prefixEnd_646868 := by exact prefixLift 646868
  have htrace : WordTrace (prefixWord ++ tailWord_646868) baseStart_646868 baseEnd_646868 := by
    simpa [prefixWord, tailWord_646868, baseEnd_646868] using wordTrace_append hprefix tailTrace_646868
  have hstable : (prefixWord ++ tailWord_646868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646868).length < 2 ^ (prefixWord ++ tailWord_646868).sum := by decide
  have hdescent : baseEnd_646868 < baseStart_646868 := by decide
  rcases family_descends (prefixWord ++ tailWord_646868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646889 : List Nat := [1, 2, 1, 1, 1, 2, 3, 6, 3]
def baseStart_646889 : Nat := 118140960795 + 646889 * 2 ^ 59
def prefixEnd_646889 : Nat := 4983230072969 + 3 ^ 40 * 646889 * 2
def baseEnd_646889 : Nat := 295257766316822024455571

theorem tailTrace_646889 : CollatzResearch.WordTrace tailWord_646889 prefixEnd_646889 295257766316822024455571 := by
  unfold tailWord_646889
  simp only [CollatzResearch.WordTrace]
  refine ⟨23593980153439107690559721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15729320102292738460373147 23593980153439107690559721)
  ·
    refine ⟨17695485115079330767919791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23593980153439107690559721 17695485115079330767919791)
    ·
      refine ⟨26543227672618996151879687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17695485115079330767919791 26543227672618996151879687)
      ·
        refine ⟨39814841508928494227819531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26543227672618996151879687 39814841508928494227819531)
        ·
          refine ⟨59722262263392741341729297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39814841508928494227819531 59722262263392741341729297)
          ·
            refine ⟨44791696697544556006296973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59722262263392741341729297 44791696697544556006296973)
            ·
              refine ⟨16796886261579208502361365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44791696697544556006296973 16796886261579208502361365)
              ·
                refine ⟨787354043511525398548189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16796886261579208502361365 787354043511525398548189)
                ·
                  refine ⟨295257766316822024455571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 787354043511525398548189 295257766316822024455571)
                  ·
                    rfl

theorem cell20_646889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_646889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646889 prefixEnd_646889 := by exact prefixLift 646889
  have htrace : WordTrace (prefixWord ++ tailWord_646889) baseStart_646889 baseEnd_646889 := by
    simpa [prefixWord, tailWord_646889, baseEnd_646889] using wordTrace_append hprefix tailTrace_646889
  have hstable : (prefixWord ++ tailWord_646889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646889).length < 2 ^ (prefixWord ++ tailWord_646889).sum := by decide
  have hdescent : baseEnd_646889 < baseStart_646889 := by decide
  rcases family_descends (prefixWord ++ tailWord_646889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646896 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_646896 : Nat := 118140960795 + 646896 * 2 ^ 59
def prefixEnd_646896 : Nat := 4983230072969 + 3 ^ 40 * 646896 * 2
def baseEnd_646896 : Nat := 295260961307561111222209

theorem tailTrace_646896 : CollatzResearch.WordTrace tailWord_646896 prefixEnd_646896 295260961307561111222209 := by
  unfold tailWord_646896
  simp only [CollatzResearch.WordTrace]
  refine ⟨11797117732206873943032271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15729490309609165257376361 11797117732206873943032271)
  ·
    refine ⟨17695676598310310914548407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11797117732206873943032271 17695676598310310914548407)
    ·
      refine ⟨26543514897465466371822611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17695676598310310914548407 26543514897465466371822611)
      ·
        refine ⟨39815272346198199557733917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26543514897465466371822611 39815272346198199557733917)
        ·
          refine ⟨14930727129824324834150219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39815272346198199557733917 14930727129824324834150219)
          ·
            refine ⟨22396090694736487251225329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14930727129824324834150219 22396090694736487251225329)
            ·
              refine ⟨16797068021052365438418997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22396090694736487251225329 16797068021052365438418997)
              ·
                refine ⟨1574725126973659259851781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16797068021052365438418997 1574725126973659259851781)
                ·
                  refine ⟨295260961307561111222209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1574725126973659259851781 295260961307561111222209)
                  ·
                    rfl

theorem cell20_646896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_646896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646896 prefixEnd_646896 := by exact prefixLift 646896
  have htrace : WordTrace (prefixWord ++ tailWord_646896) baseStart_646896 baseEnd_646896 := by
    simpa [prefixWord, tailWord_646896, baseEnd_646896] using wordTrace_append hprefix tailTrace_646896
  have hstable : (prefixWord ++ tailWord_646896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646896).length < 2 ^ (prefixWord ++ tailWord_646896).sum := by decide
  have hdescent : baseEnd_646896 < baseStart_646896 := by decide
  rcases family_descends (prefixWord ++ tailWord_646896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646902 : List Nat := [5, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_646902 : Nat := 118140960795 + 646902 * 2 ^ 59
def prefixEnd_646902 : Nat := 4983230072969 + 3 ^ 40 * 646902 * 2
def baseEnd_646902 : Nat := 295263699871051757022185

theorem tailTrace_646902 : CollatzResearch.WordTrace tailWord_646902 prefixEnd_646902 295263699871051757022185 := by
  unfold tailWord_646902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1474653393899500681923935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15729636201594673940521973 1474653393899500681923935)
  ·
    refine ⟨2211980090849251022885903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1474653393899500681923935 2211980090849251022885903)
    ·
      refine ⟨3317970136273876534328855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2211980090849251022885903 3317970136273876534328855)
      ·
        refine ⟨4976955204410814801493283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3317970136273876534328855 4976955204410814801493283)
        ·
          refine ⟨7465432806616222202239925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4976955204410814801493283 7465432806616222202239925)
          ·
            refine ⟨699884325620270831459993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7465432806616222202239925 699884325620270831459993)
            ·
              refine ⟨524913244215203123594995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699884325620270831459993 524913244215203123594995)
              ·
                refine ⟨787369866322804685392493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524913244215203123594995 787369866322804685392493)
                ·
                  refine ⟨295263699871051757022185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 787369866322804685392493 295263699871051757022185)
                  ·
                    rfl

theorem cell20_646902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_646902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646902 prefixEnd_646902 := by exact prefixLift 646902
  have htrace : WordTrace (prefixWord ++ tailWord_646902) baseStart_646902 baseEnd_646902 := by
    simpa [prefixWord, tailWord_646902, baseEnd_646902] using wordTrace_append hprefix tailTrace_646902
  have hstable : (prefixWord ++ tailWord_646902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646902).length < 2 ^ (prefixWord ++ tailWord_646902).sum := by decide
  have hdescent : baseEnd_646902 < baseStart_646902 := by decide
  rcases family_descends (prefixWord ++ tailWord_646902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646903 : List Nat := [1, 1, 3, 1, 1, 1, 5, 7]
def baseStart_646903 : Nat := 118140960795 + 646903 * 2 ^ 59
def prefixEnd_646903 : Nat := 4983230072969 + 3 ^ 40 * 646903 * 2
def baseEnd_646903 : Nat := 98421385432766732662949

theorem tailTrace_646903 : CollatzResearch.WordTrace tailWord_646903 prefixEnd_646903 98421385432766732662949 := by
  unfold tailWord_646903
  simp only [CollatzResearch.WordTrace]
  refine ⟨23594490775388388081569363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15729660516925592054379575 23594490775388388081569363)
  ·
    refine ⟨35391736163082582122354045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23594490775388388081569363 35391736163082582122354045)
    ·
      refine ⟨13271901061155968295882767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35391736163082582122354045 13271901061155968295882767)
      ·
        refine ⟨19907851591733952443824151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13271901061155968295882767 19907851591733952443824151)
        ·
          refine ⟨29861777387600928665736227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19907851591733952443824151 29861777387600928665736227)
          ·
            refine ⟨44792666081401392998604341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29861777387600928665736227 44792666081401392998604341)
            ·
              refine ⟨4199312445131380593619157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44792666081401392998604341 4199312445131380593619157)
              ·
                refine ⟨98421385432766732662949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4199312445131380593619157 98421385432766732662949)
                ·
                  rfl

theorem cell20_646903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_646903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646903 prefixEnd_646903 := by exact prefixLift 646903
  have htrace : WordTrace (prefixWord ++ tailWord_646903) baseStart_646903 baseEnd_646903 := by
    simpa [prefixWord, tailWord_646903, baseEnd_646903] using wordTrace_append hprefix tailTrace_646903
  have hstable : (prefixWord ++ tailWord_646903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646903).length < 2 ^ (prefixWord ++ tailWord_646903).sum := by decide
  have hdescent : baseEnd_646903 < baseStart_646903 := by decide
  rcases family_descends (prefixWord ++ tailWord_646903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646941 : List Nat := [1, 4, 2, 13]
def baseStart_646941 : Nat := 118140960795 + 646941 * 2 ^ 59
def prefixEnd_646941 : Nat := 4983230072969 + 3 ^ 40 * 646941 * 2
def baseEnd_646941 : Nat := 1215150207957781706675

theorem tailTrace_646941 : CollatzResearch.WordTrace tailWord_646941 prefixEnd_646941 1215150207957781706675 := by
  unfold tailWord_646941
  simp only [CollatzResearch.WordTrace]
  refine ⟨23595876749250720571452677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15730584499500480380968451 23595876749250720571452677)
  ·
    refine ⟨4424226890484510107147377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23595876749250720571452677 4424226890484510107147377)
    ·
      refine ⟨3318170167863382580360533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4424226890484510107147377 3318170167863382580360533)
      ·
        refine ⟨1215150207957781706675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3318170167863382580360533 1215150207957781706675)
        ·
          rfl

theorem cell20_646941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 13].length) (baseStart_646941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646941 prefixEnd_646941 := by exact prefixLift 646941
  have htrace : WordTrace (prefixWord ++ tailWord_646941) baseStart_646941 baseEnd_646941 := by
    simpa [prefixWord, tailWord_646941, baseEnd_646941] using wordTrace_append hprefix tailTrace_646941
  have hstable : (prefixWord ++ tailWord_646941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646941).length < 2 ^ (prefixWord ++ tailWord_646941).sum := by decide
  have hdescent : baseEnd_646941 < baseStart_646941 := by decide
  rcases family_descends (prefixWord ++ tailWord_646941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646944 : List Nat := [2, 1, 1, 5, 1, 1, 4, 2, 3]
def baseStart_646944 : Nat := 118140960795 + 646944 * 2 ^ 59
def prefixEnd_646944 : Nat := 4983230072969 + 3 ^ 40 * 646944 * 2
def baseEnd_646944 : Nat := 295282869815486277622013

theorem tailTrace_646944 : CollatzResearch.WordTrace tailWord_646944 prefixEnd_646944 295282869815486277622013 := by
  unfold tailWord_646944
  simp only [CollatzResearch.WordTrace]
  refine ⟨11797993084119926041905943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15730657445493234722541257 11797993084119926041905943)
  ·
    refine ⟨17696989626179889062858915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11797993084119926041905943 17696989626179889062858915)
    ·
      refine ⟨26545484439269833594288373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17696989626179889062858915 26545484439269833594288373)
      ·
        refine ⟨2488639166181546899464535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26545484439269833594288373 2488639166181546899464535)
        ·
          refine ⟨3732958749272320349196803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2488639166181546899464535 3732958749272320349196803)
          ·
            refine ⟨5599438123908480523795205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3732958749272320349196803 5599438123908480523795205)
            ·
              refine ⟨1049894648232840098211601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5599438123908480523795205 1049894648232840098211601)
              ·
                refine ⟨787420986174630073658701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1049894648232840098211601 787420986174630073658701)
                ·
                  refine ⟨295282869815486277622013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 787420986174630073658701 295282869815486277622013)
                  ·
                    rfl

theorem cell20_646944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_646944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646944 prefixEnd_646944 := by exact prefixLift 646944
  have htrace : WordTrace (prefixWord ++ tailWord_646944) baseStart_646944 baseEnd_646944 := by
    simpa [prefixWord, tailWord_646944, baseEnd_646944] using wordTrace_append hprefix tailTrace_646944
  have hstable : (prefixWord ++ tailWord_646944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646944).length < 2 ^ (prefixWord ++ tailWord_646944).sum := by decide
  have hdescent : baseEnd_646944 < baseStart_646944 := by decide
  rcases family_descends (prefixWord ++ tailWord_646944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646972 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_646972 : Nat := 118140960795 + 646972 * 2 ^ 59
def prefixEnd_646972 : Nat := 4983230072969 + 3 ^ 40 * 646972 * 2
def baseEnd_646972 : Nat := 295295649778442624688565

theorem tailTrace_646972 : CollatzResearch.WordTrace tailWord_646972 prefixEnd_646972 295295649778442624688565 := by
  unfold tailWord_646972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11798503706069206432915585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15731338274758941910554113 11798503706069206432915585)
  ·
    refine ⟨8848877779551904824686689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11798503706069206432915585 8848877779551904824686689)
    ·
      refine ⟨6636658334663928618515017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8848877779551904824686689 6636658334663928618515017)
      ·
        refine ⟨4977493750997946463886263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6636658334663928618515017 4977493750997946463886263)
        ·
          refine ⟨7466240626496919695829395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4977493750997946463886263 7466240626496919695829395)
          ·
            refine ⟨11199360939745379543744093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7466240626496919695829395 11199360939745379543744093)
            ·
              refine ⟨4199760352404517328904035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11199360939745379543744093 4199760352404517328904035)
              ·
                refine ⟨6299640528606775993356053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4199760352404517328904035 6299640528606775993356053)
                ·
                  refine ⟨295295649778442624688565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6299640528606775993356053 295295649778442624688565)
                  ·
                    rfl

theorem cell20_646972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_646972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646972 prefixEnd_646972 := by exact prefixLift 646972
  have htrace : WordTrace (prefixWord ++ tailWord_646972) baseStart_646972 baseEnd_646972 := by
    simpa [prefixWord, tailWord_646972, baseEnd_646972] using wordTrace_append hprefix tailTrace_646972
  have hstable : (prefixWord ++ tailWord_646972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646972).length < 2 ^ (prefixWord ++ tailWord_646972).sum := by decide
  have hdescent : baseEnd_646972 < baseStart_646972 := by decide
  rcases family_descends (prefixWord ++ tailWord_646972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646975 : List Nat := [1, 1, 2, 2, 6, 1, 3, 4]
def baseStart_646975 : Nat := 118140960795 + 646975 * 2 ^ 59
def prefixEnd_646975 : Nat := 4983230072969 + 3 ^ 40 * 646975 * 2
def baseEnd_646975 : Nat := 98432339686729315862851

theorem tailTrace_646975 : CollatzResearch.WordTrace tailWord_646975 prefixEnd_646975 98432339686729315862851 := by
  unfold tailWord_646975
  simp only [CollatzResearch.WordTrace]
  refine ⟨23597116831127544378190379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15731411220751696252126919 23597116831127544378190379)
  ·
    refine ⟨35395675246691316567285569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23597116831127544378190379 35395675246691316567285569)
    ·
      refine ⟨26546756435018487425464177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35395675246691316567285569 26546756435018487425464177)
      ·
        refine ⟨19910067326263865569098133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26546756435018487425464177 19910067326263865569098133)
        ·
          refine ⟨933284405918618698551475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19910067326263865569098133 933284405918618698551475)
          ·
            refine ⟨1399926608877928047827213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933284405918618698551475 1399926608877928047827213)
            ·
              refine ⟨524972478329223017935205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1399926608877928047827213 524972478329223017935205)
              ·
                refine ⟨98432339686729315862851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 524972478329223017935205 98432339686729315862851)
                ·
                  rfl

theorem cell20_646975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 4].length) (baseStart_646975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646975 prefixEnd_646975 := by exact prefixLift 646975
  have htrace : WordTrace (prefixWord ++ tailWord_646975) baseStart_646975 baseEnd_646975 := by
    simpa [prefixWord, tailWord_646975, baseEnd_646975] using wordTrace_append hprefix tailTrace_646975
  have hstable : (prefixWord ++ tailWord_646975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646975).length < 2 ^ (prefixWord ++ tailWord_646975).sum := by decide
  have hdescent : baseEnd_646975 < baseStart_646975 := by decide
  rcases family_descends (prefixWord ++ tailWord_646975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646996 : List Nat := [2, 4, 1, 1, 3, 2, 7]
def baseStart_646996 : Nat := 118140960795 + 646996 * 2 ^ 59
def prefixEnd_646996 : Nat := 4983230072969 + 3 ^ 40 * 646996 * 2
def baseEnd_646996 : Nat := 32811844892489467543163

theorem tailTrace_646996 : CollatzResearch.WordTrace tailWord_646996 prefixEnd_646996 32811844892489467543163 := by
  unfold tailWord_646996
  simp only [CollatzResearch.WordTrace]
  refine ⟨11798941382025732482352421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15731921842700976643136561 11798941382025732482352421)
  ·
    refine ⟨2212301509129824840441079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11798941382025732482352421 2212301509129824840441079)
    ·
      refine ⟨3318452263694737260661619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2212301509129824840441079 3318452263694737260661619)
      ·
        refine ⟨4977678395542105890992429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3318452263694737260661619 4977678395542105890992429)
        ·
          refine ⟨1866629398328289709122161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4977678395542105890992429 1866629398328289709122161)
          ·
            refine ⟨1399972048746217281841621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1866629398328289709122161 1399972048746217281841621)
            ·
              refine ⟨32811844892489467543163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1399972048746217281841621 32811844892489467543163)
              ·
                rfl

theorem cell20_646996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 7].length) (baseStart_646996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646996 prefixEnd_646996 := by exact prefixLift 646996
  have htrace : WordTrace (prefixWord ++ tailWord_646996) baseStart_646996 baseEnd_646996 := by
    simpa [prefixWord, tailWord_646996, baseEnd_646996] using wordTrace_append hprefix tailTrace_646996
  have hstable : (prefixWord ++ tailWord_646996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646996).length < 2 ^ (prefixWord ++ tailWord_646996).sum := by decide
  have hdescent : baseEnd_646996 < baseStart_646996 := by decide
  rcases family_descends (prefixWord ++ tailWord_646996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646999 : List Nat := [1, 1, 3, 2, 5, 2, 1, 2, 3]
def baseStart_646999 : Nat := 118140960795 + 646999 * 2 ^ 59
def prefixEnd_646999 : Nat := 4983230072969 + 3 ^ 40 * 646999 * 2
def baseEnd_646999 : Nat := 295307973314150530788455

theorem tailTrace_646999 : CollatzResearch.WordTrace tailWord_646999 prefixEnd_646999 295307973314150530788455 := by
  unfold tailWord_646999
  simp only [CollatzResearch.WordTrace]
  refine ⟨23597992183040596477064051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15731994788693730984709367 23597992183040596477064051)
  ·
    refine ⟨35396988274560894715596077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23597992183040596477064051 35396988274560894715596077)
    ·
      refine ⟨13273870602960335518348529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35396988274560894715596077 13273870602960335518348529)
      ·
        refine ⟨9955402952220251638761397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13273870602960335518348529 9955402952220251638761397)
        ·
          refine ⟨933319026770648591133881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9955402952220251638761397 933319026770648591133881)
          ·
            refine ⟨699989270077986443350411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 933319026770648591133881 699989270077986443350411)
            ·
              refine ⟨1049983905116979665025617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699989270077986443350411 1049983905116979665025617)
              ·
                refine ⟨787487928837734748769213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1049983905116979665025617 787487928837734748769213)
                ·
                  refine ⟨295307973314150530788455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 787487928837734748769213 295307973314150530788455)
                  ·
                    rfl

theorem cell20_646999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 3].length) (baseStart_646999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_646999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_646999 prefixEnd_646999 := by exact prefixLift 646999
  have htrace : WordTrace (prefixWord ++ tailWord_646999) baseStart_646999 baseEnd_646999 := by
    simpa [prefixWord, tailWord_646999, baseEnd_646999] using wordTrace_append hprefix tailTrace_646999
  have hstable : (prefixWord ++ tailWord_646999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646999).length < 2 ^ (prefixWord ++ tailWord_646999).sum := by decide
  have hdescent : baseEnd_646999 < baseStart_646999 := by decide
  rcases family_descends (prefixWord ++ tailWord_646999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647034 : List Nat := [3, 1, 1, 1, 1, 1, 8, 4]
def baseStart_647034 : Nat := 118140960795 + 647034 * 2 ^ 59
def prefixEnd_647034 : Nat := 4983230072969 + 3 ^ 40 * 647034 * 2
def baseEnd_647034 : Nat := 98441316089281988207215

theorem tailTrace_647034 : CollatzResearch.WordTrace tailWord_647034 prefixEnd_647034 98441316089281988207215 := by
  unfold tailWord_647034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899817184478449363647039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15732845825275864969725437 5899817184478449363647039)
  ·
    refine ⟨8849725776717674045470559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5899817184478449363647039 8849725776717674045470559)
    ·
      refine ⟨13274588665076511068205839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8849725776717674045470559 13274588665076511068205839)
      ·
        refine ⟨19911882997614766602308759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13274588665076511068205839 19911882997614766602308759)
        ·
          refine ⟨29867824496422149903463139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19911882997614766602308759 29867824496422149903463139)
          ·
            refine ⟨44801736744633224855194709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29867824496422149903463139 44801736744633224855194709)
            ·
              refine ⟨525020352476170603771813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 44801736744633224855194709 525020352476170603771813)
              ·
                refine ⟨98441316089281988207215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 525020352476170603771813 98441316089281988207215)
                ·
                  rfl

theorem cell20_647034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_647034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647034 prefixEnd_647034 := by exact prefixLift 647034
  have htrace : WordTrace (prefixWord ++ tailWord_647034) baseStart_647034 baseEnd_647034 := by
    simpa [prefixWord, tailWord_647034, baseEnd_647034] using wordTrace_append hprefix tailTrace_647034
  have hstable : (prefixWord ++ tailWord_647034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647034).length < 2 ^ (prefixWord ++ tailWord_647034).sum := by decide
  have hdescent : baseEnd_647034 < baseStart_647034 := by decide
  rcases family_descends (prefixWord ++ tailWord_647034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647044 : List Nat := [2, 3, 2, 1, 1, 1, 5, 3, 2]
def baseStart_647044 : Nat := 118140960795 + 647044 * 2 ^ 59
def prefixEnd_647044 : Nat := 4983230072969 + 3 ^ 40 * 647044 * 2
def baseEnd_647044 : Nat := 295328512540330374288271

theorem tailTrace_647044 : CollatzResearch.WordTrace tailWord_647044 prefixEnd_647044 295328512540330374288271 := by
  unfold tailWord_647044
  simp only [CollatzResearch.WordTrace]
  refine ⟨11799816733938784581226093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15733088978585046108301457 11799816733938784581226093)
  ·
    refine ⟨4424931275227044217959785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11799816733938784581226093 4424931275227044217959785)
    ·
      refine ⟨3318698456420283163469839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4424931275227044217959785 3318698456420283163469839)
      ·
        refine ⟨4978047684630424745204759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3318698456420283163469839 4978047684630424745204759)
        ·
          refine ⟨7467071526945637117807139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4978047684630424745204759 7467071526945637117807139)
          ·
            refine ⟨11200607290418455676710709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7467071526945637117807139 11200607290418455676710709)
            ·
              refine ⟨1050056933476730219691629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11200607290418455676710709 1050056933476730219691629)
              ·
                refine ⟨393771350053773832384361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1050056933476730219691629 393771350053773832384361)
                ·
                  refine ⟨295328512540330374288271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393771350053773832384361 295328512540330374288271)
                  ·
                    rfl

theorem cell20_647044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_647044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647044 prefixEnd_647044 := by exact prefixLift 647044
  have htrace : WordTrace (prefixWord ++ tailWord_647044) baseStart_647044 baseEnd_647044 := by
    simpa [prefixWord, tailWord_647044, baseEnd_647044] using wordTrace_append hprefix tailTrace_647044
  have hstable : (prefixWord ++ tailWord_647044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647044).length < 2 ^ (prefixWord ++ tailWord_647044).sum := by decide
  have hdescent : baseEnd_647044 < baseStart_647044 := by decide
  rcases family_descends (prefixWord ++ tailWord_647044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647058 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_647058 : Nat := 118140960795 + 647058 * 2 ^ 59
def prefixEnd_647058 : Nat := 4983230072969 + 3 ^ 40 * 647058 * 2
def baseEnd_647058 : Nat := 295334902521808547821547

theorem tailTrace_647058 : CollatzResearch.WordTrace tailWord_647058 prefixEnd_647058 295334902521808547821547 := by
  unfold tailWord_647058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5900036022456712388365457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15733429393217899702307885 5900036022456712388365457)
  ·
    refine ⟨4425027016842534291274093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5900036022456712388365457 4425027016842534291274093)
    ·
      refine ⟨1659385131315950359227785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4425027016842534291274093 1659385131315950359227785)
      ·
        refine ⟨1244538848486962769420839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1659385131315950359227785 1244538848486962769420839)
        ·
          refine ⟨1866808272730444154131259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1244538848486962769420839 1866808272730444154131259)
          ·
            refine ⟨2800212409095666231196889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1866808272730444154131259 2800212409095666231196889)
            ·
              refine ⟨2100159306821749673397667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2800212409095666231196889 2100159306821749673397667)
              ·
                refine ⟨3150238960232624510096501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2100159306821749673397667 3150238960232624510096501)
                ·
                  refine ⟨295334902521808547821547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3150238960232624510096501 295334902521808547821547)
                  ·
                    rfl

theorem cell20_647058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_647058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647058 prefixEnd_647058 := by exact prefixLift 647058
  have htrace : WordTrace (prefixWord ++ tailWord_647058) baseStart_647058 baseEnd_647058 := by
    simpa [prefixWord, tailWord_647058, baseEnd_647058] using wordTrace_append hprefix tailTrace_647058
  have hstable : (prefixWord ++ tailWord_647058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647058).length < 2 ^ (prefixWord ++ tailWord_647058).sum := by decide
  have hdescent : baseEnd_647058 < baseStart_647058 := by decide
  rcases family_descends (prefixWord ++ tailWord_647058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647065 : List Nat := [1, 2, 1, 2, 1, 3, 2, 6, 2]
def baseStart_647065 : Nat := 118140960795 + 647065 * 2 ^ 59
def prefixEnd_647065 : Nat := 4983230072969 + 3 ^ 40 * 647065 * 2
def baseEnd_647065 : Nat := 295338097512547634588185

theorem tailTrace_647065 : CollatzResearch.WordTrace tailWord_647065 prefixEnd_647065 295338097512547634588185 := by
  unfold tailWord_647065
  simp only [CollatzResearch.WordTrace]
  refine ⟨23600399400801489748966649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15733599600534326499311099 23600399400801489748966649)
  ·
    refine ⟨17700299550601117311724987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23600399400801489748966649 17700299550601117311724987)
    ·
      refine ⟨26550449325901675967587481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17700299550601117311724987 26550449325901675967587481)
      ·
        refine ⟨19912836994426256975690611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26550449325901675967587481 19912836994426256975690611)
        ·
          refine ⟨29869255491639385463535917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19912836994426256975690611 29869255491639385463535917)
          ·
            refine ⟨11200970809364769548825969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29869255491639385463535917 11200970809364769548825969)
            ·
              refine ⟨8400728107023577161619477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11200970809364769548825969 8400728107023577161619477)
              ·
                refine ⟨393784130016730179450913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8400728107023577161619477 393784130016730179450913)
                ·
                  refine ⟨295338097512547634588185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393784130016730179450913 295338097512547634588185)
                  ·
                    rfl

theorem cell20_647065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 2].length) (baseStart_647065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647065 prefixEnd_647065 := by exact prefixLift 647065
  have htrace : WordTrace (prefixWord ++ tailWord_647065) baseStart_647065 baseEnd_647065 := by
    simpa [prefixWord, tailWord_647065, baseEnd_647065] using wordTrace_append hprefix tailTrace_647065
  have hstable : (prefixWord ++ tailWord_647065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647065).length < 2 ^ (prefixWord ++ tailWord_647065).sum := by decide
  have hdescent : baseEnd_647065 < baseStart_647065 := by decide
  rcases family_descends (prefixWord ++ tailWord_647065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647103 : List Nat := [1, 1, 2, 2, 2, 1, 4, 5, 2]
def baseStart_647103 : Nat := 118140960795 + 647103 * 2 ^ 59
def prefixEnd_647103 : Nat := 4983230072969 + 3 ^ 40 * 647103 * 2
def baseEnd_647103 : Nat := 295355441747988391321363

theorem tailTrace_647103 : CollatzResearch.WordTrace tailWord_647103 prefixEnd_647103 295355441747988391321363 := by
  unfold tailWord_647103
  simp only [CollatzResearch.WordTrace]
  refine ⟨23601785374663822238849963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15734523583109214825899975 23601785374663822238849963)
  ·
    refine ⟨35402678061995733358274945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23601785374663822238849963 35402678061995733358274945)
    ·
      refine ⟨26552008546496800018706209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35402678061995733358274945 26552008546496800018706209)
      ·
        refine ⟨19914006409872600014029657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26552008546496800018706209 19914006409872600014029657)
        ·
          refine ⟨14935504807404450010522243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19914006409872600014029657 14935504807404450010522243)
          ·
            refine ⟨22403257211106675015783365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14935504807404450010522243 22403257211106675015783365)
            ·
              refine ⟨4200610727082501565459381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22403257211106675015783365 4200610727082501565459381)
              ·
                refine ⟨393807255663984521761817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4200610727082501565459381 393807255663984521761817)
                ·
                  refine ⟨295355441747988391321363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393807255663984521761817 295355441747988391321363)
                  ·
                    rfl

theorem cell20_647103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 2].length) (baseStart_647103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647103 prefixEnd_647103 := by exact prefixLift 647103
  have htrace : WordTrace (prefixWord ++ tailWord_647103) baseStart_647103 baseEnd_647103 := by
    simpa [prefixWord, tailWord_647103, baseEnd_647103] using wordTrace_append hprefix tailTrace_647103
  have hstable : (prefixWord ++ tailWord_647103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647103).length < 2 ^ (prefixWord ++ tailWord_647103).sum := by decide
  have hdescent : baseEnd_647103 < baseStart_647103 := by decide
  rcases family_descends (prefixWord ++ tailWord_647103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647120 : List Nat := [2, 1, 1, 1, 1, 2, 8, 2, 2]
def baseStart_647120 : Nat := 118140960795 + 647120 * 2 ^ 59
def prefixEnd_647120 : Nat := 4983230072969 + 3 ^ 40 * 647120 * 2
def baseEnd_647120 : Nat := 295363201011211887754627

theorem tailTrace_647120 : CollatzResearch.WordTrace tailWord_647120 prefixEnd_647120 295363201011211887754627 := by
  unfold tailWord_647120
  simp only [CollatzResearch.WordTrace]
  refine ⟨11801202707801117071109407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15734936943734822761479209 11801202707801117071109407)
  ·
    refine ⟨17701804061701675606664111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11801202707801117071109407 17701804061701675606664111)
    ·
      refine ⟨26552706092552513409996167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17701804061701675606664111 26552706092552513409996167)
      ·
        refine ⟨39829059138828770114994251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26552706092552513409996167 39829059138828770114994251)
        ·
          refine ⟨59743588708243155172491377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39829059138828770114994251 59743588708243155172491377)
          ·
            refine ⟨44807691531182366379368533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59743588708243155172491377 44807691531182366379368533)
            ·
              refine ⟨525090135131043356008225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 44807691531182366379368533 525090135131043356008225)
              ·
                refine ⟨393817601348282517006169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525090135131043356008225 393817601348282517006169)
                ·
                  refine ⟨295363201011211887754627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393817601348282517006169 295363201011211887754627)
                  ·
                    rfl

theorem cell20_647120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 2].length) (baseStart_647120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647120 prefixEnd_647120 := by exact prefixLift 647120
  have htrace : WordTrace (prefixWord ++ tailWord_647120) baseStart_647120 baseEnd_647120 := by
    simpa [prefixWord, tailWord_647120, baseEnd_647120] using wordTrace_append hprefix tailTrace_647120
  have hstable : (prefixWord ++ tailWord_647120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647120).length < 2 ^ (prefixWord ++ tailWord_647120).sum := by decide
  have hdescent : baseEnd_647120 < baseStart_647120 := by decide
  rcases family_descends (prefixWord ++ tailWord_647120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647169 : List Nat := [1, 2, 4, 1, 2, 1, 9]
def baseStart_647169 : Nat := 118140960795 + 647169 * 2 ^ 59
def prefixEnd_647169 : Nat := 4983230072969 + 3 ^ 40 * 647169 * 2
def baseEnd_647169 : Nat := 32820618438487277235677

theorem tailTrace_647169 : CollatzResearch.WordTrace tailWord_647169 prefixEnd_647169 32820618438487277235677 := by
  unfold tailWord_647169
  simp only [CollatzResearch.WordTrace]
  refine ⟨23604192592424715510752561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15736128394949810340501707 23604192592424715510752561)
  ·
    refine ⟨17703144444318536633064421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23604192592424715510752561 17703144444318536633064421)
    ·
      refine ⟨3319339583309725618699579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17703144444318536633064421 3319339583309725618699579)
      ·
        refine ⟨4979009374964588428049369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3319339583309725618699579 4979009374964588428049369)
        ·
          refine ⟨3734257031223441321037027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4979009374964588428049369 3734257031223441321037027)
          ·
            refine ⟨5601385546835161981555541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3734257031223441321037027 5601385546835161981555541)
            ·
              refine ⟨32820618438487277235677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5601385546835161981555541 32820618438487277235677)
              ·
                rfl

theorem cell20_647169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 9].length) (baseStart_647169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647169 prefixEnd_647169 := by exact prefixLift 647169
  have htrace : WordTrace (prefixWord ++ tailWord_647169) baseStart_647169 baseEnd_647169 := by
    simpa [prefixWord, tailWord_647169, baseEnd_647169] using wordTrace_append hprefix tailTrace_647169
  have hstable : (prefixWord ++ tailWord_647169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647169).length < 2 ^ (prefixWord ++ tailWord_647169).sum := by decide
  have hdescent : baseEnd_647169 < baseStart_647169 := by decide
  rcases family_descends (prefixWord ++ tailWord_647169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647179 : List Nat := [1, 1, 1, 1, 6, 1, 1, 6, 2]
def baseStart_647179 : Nat := 118140960795 + 647179 * 2 ^ 59
def prefixEnd_647179 : Nat := 4983230072969 + 3 ^ 40 * 647179 * 2
def baseEnd_647179 : Nat := 295390130218869904787719

theorem tailTrace_647179 : CollatzResearch.WordTrace tailWord_647179 prefixEnd_647179 295390130218869904787719 := by
  unfold tailWord_647179
  simp only [CollatzResearch.WordTrace]
  refine ⟨23604557322388487218616591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15736371548258991479077727 23604557322388487218616591)
  ·
    refine ⟨35406835983582730827924887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23604557322388487218616591 35406835983582730827924887)
    ·
      refine ⟨53110253975374096241887331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35406835983582730827924887 53110253975374096241887331)
      ·
        refine ⟨79665380963061144362830997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53110253975374096241887331 79665380963061144362830997)
        ·
          refine ⟨3734314732643491142007703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79665380963061144362830997 3734314732643491142007703)
          ·
            refine ⟨5601472098965236713011555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3734314732643491142007703 5601472098965236713011555)
            ·
              refine ⟨8402208148447855069517333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5601472098965236713011555 8402208148447855069517333)
              ·
                refine ⟨393853506958493206383625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8402208148447855069517333 393853506958493206383625)
                ·
                  refine ⟨295390130218869904787719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393853506958493206383625 295390130218869904787719)
                  ·
                    rfl

theorem cell20_647179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 2].length) (baseStart_647179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647179 prefixEnd_647179 := by exact prefixLift 647179
  have htrace : WordTrace (prefixWord ++ tailWord_647179) baseStart_647179 baseEnd_647179 := by
    simpa [prefixWord, tailWord_647179, baseEnd_647179] using wordTrace_append hprefix tailTrace_647179
  have hstable : (prefixWord ++ tailWord_647179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647179).length < 2 ^ (prefixWord ++ tailWord_647179).sum := by decide
  have hdescent : baseEnd_647179 < baseStart_647179 := by decide
  rcases family_descends (prefixWord ++ tailWord_647179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647189 : List Nat := [1, 3, 2, 1, 5, 1, 3, 1, 3]
def baseStart_647189 : Nat := 118140960795 + 647189 * 2 ^ 59
def prefixEnd_647189 : Nat := 4983230072969 + 3 ^ 40 * 647189 * 2
def baseEnd_647189 : Nat := 295394694491354314454345

theorem tailTrace_647189 : CollatzResearch.WordTrace tailWord_647189 prefixEnd_647189 295394694491354314454345 := by
  unfold tailWord_647189
  simp only [CollatzResearch.WordTrace]
  refine ⟨23604922052352258926480621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15736614701568172617653747 23604922052352258926480621)
  ·
    refine ⟨8851845769632097097430233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23604922052352258926480621 8851845769632097097430233)
    ·
      refine ⟨6638884327224072823072675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8851845769632097097430233 6638884327224072823072675)
      ·
        refine ⟨9958326490836109234609013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6638884327224072823072675 9958326490836109234609013)
        ·
          refine ⟨933593108515885240744595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9958326490836109234609013 933593108515885240744595)
          ·
            refine ⟨1400389662773827861116893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933593108515885240744595 1400389662773827861116893)
            ·
              refine ⟨525146123540185447918835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1400389662773827861116893 525146123540185447918835)
              ·
                refine ⟨787719185310278171878253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525146123540185447918835 787719185310278171878253)
                ·
                  refine ⟨295394694491354314454345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 787719185310278171878253 295394694491354314454345)
                  ·
                    rfl

theorem cell20_647189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_647189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647189 prefixEnd_647189 := by exact prefixLift 647189
  have htrace : WordTrace (prefixWord ++ tailWord_647189) baseStart_647189 baseEnd_647189 := by
    simpa [prefixWord, tailWord_647189, baseEnd_647189] using wordTrace_append hprefix tailTrace_647189
  have hstable : (prefixWord ++ tailWord_647189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647189).length < 2 ^ (prefixWord ++ tailWord_647189).sum := by decide
  have hdescent : baseEnd_647189 < baseStart_647189 := by decide
  rcases family_descends (prefixWord ++ tailWord_647189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647220 : List Nat := [2, 5, 1, 2, 3, 1, 6]
def baseStart_647220 : Nat := 118140960795 + 647220 * 2 ^ 59
def prefixEnd_647220 : Nat := 4983230072969 + 3 ^ 40 * 647220 * 2
def baseEnd_647220 : Nat := 32823204859561776046765

theorem tailTrace_647220 : CollatzResearch.WordTrace tailWord_647220 prefixEnd_647220 32823204859561776046765 := by
  unfold tailWord_647220
  simp only [CollatzResearch.WordTrace]
  refine ⟨11803026357619975610429557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15737368476826634147239409 11803026357619975610429557)
  ·
    refine ⟨1106533721026872713477771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11803026357619975610429557 1106533721026872713477771)
    ·
      refine ⟨1659800581540309070216657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1106533721026872713477771 1659800581540309070216657)
      ·
        refine ⟨1244850436155231802662493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1659800581540309070216657 1244850436155231802662493)
        ·
          refine ⟨466818913558211925998435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1244850436155231802662493 466818913558211925998435)
          ·
            refine ⟨700228370337317888997653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466818913558211925998435 700228370337317888997653)
            ·
              refine ⟨32823204859561776046765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 700228370337317888997653 32823204859561776046765)
              ·
                rfl

theorem cell20_647220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 6].length) (baseStart_647220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647220 prefixEnd_647220 := by exact prefixLift 647220
  have htrace : WordTrace (prefixWord ++ tailWord_647220) baseStart_647220 baseEnd_647220 := by
    simpa [prefixWord, tailWord_647220, baseEnd_647220] using wordTrace_append hprefix tailTrace_647220
  have hstable : (prefixWord ++ tailWord_647220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647220).length < 2 ^ (prefixWord ++ tailWord_647220).sum := by decide
  have hdescent : baseEnd_647220 < baseStart_647220 := by decide
  rcases family_descends (prefixWord ++ tailWord_647220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647224 : List Nat := [2, 1, 2, 1, 6, 2, 6]
def baseStart_647224 : Nat := 118140960795 + 647224 * 2 ^ 59
def prefixEnd_647224 : Nat := 4983230072969 + 3 ^ 40 * 647224 * 2
def baseEnd_647224 : Nat := 32823407716116638698615

theorem tailTrace_647224 : CollatzResearch.WordTrace tailWord_647224 prefixEnd_647224 32823407716116638698615 := by
  unfold tailWord_647224
  simp only [CollatzResearch.WordTrace]
  refine ⟨11803099303612729952002363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15737465738150306602669817 11803099303612729952002363)
  ·
    refine ⟨17704648955419094928003545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11803099303612729952002363 17704648955419094928003545)
    ·
      refine ⟨13278486716564321196002659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17704648955419094928003545 13278486716564321196002659)
      ·
        refine ⟨19917730074846481794003989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13278486716564321196002659 19917730074846481794003989)
        ·
          refine ⟨933643597258428834093937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19917730074846481794003989 933643597258428834093937)
          ·
            refine ⟨700232697943821625570453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 933643597258428834093937 700232697943821625570453)
            ·
              refine ⟨32823407716116638698615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 700232697943821625570453 32823407716116638698615)
              ·
                rfl

theorem cell20_647224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 6].length) (baseStart_647224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647224 prefixEnd_647224 := by exact prefixLift 647224
  have htrace : WordTrace (prefixWord ++ tailWord_647224) baseStart_647224 baseEnd_647224 := by
    simpa [prefixWord, tailWord_647224, baseEnd_647224] using wordTrace_append hprefix tailTrace_647224
  have hstable : (prefixWord ++ tailWord_647224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647224).length < 2 ^ (prefixWord ++ tailWord_647224).sum := by decide
  have hdescent : baseEnd_647224 < baseStart_647224 := by decide
  rcases family_descends (prefixWord ++ tailWord_647224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647230 : List Nat := [4, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_647230 : Nat := 118140960795 + 647230 * 2 ^ 59
def prefixEnd_647230 : Nat := 4983230072969 + 3 ^ 40 * 647230 * 2
def baseEnd_647230 : Nat := 295413408008540394087511

theorem tailTrace_647230 : CollatzResearch.WordTrace tailWord_647230 prefixEnd_647230 295413408008540394087511 := by
  unfold tailWord_647230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2950802180650465366090393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15737611630135815285815429 2950802180650465366090393)
  ·
    refine ⟨2213101635487849024567795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2950802180650465366090393 2213101635487849024567795)
    ·
      refine ⟨3319652453231773536851693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2213101635487849024567795 3319652453231773536851693)
      ·
        refine ⟨1244869669961915076319385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3319652453231773536851693 1244869669961915076319385)
        ·
          refine ⟨933652252471436307239539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1244869669961915076319385 933652252471436307239539)
          ·
            refine ⟨1400478378707154460859309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933652252471436307239539 1400478378707154460859309)
            ·
              refine ⟨525179392015182922822241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1400478378707154460859309 525179392015182922822241)
              ·
                refine ⟨393884544011387192116681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525179392015182922822241 393884544011387192116681)
                ·
                  refine ⟨295413408008540394087511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393884544011387192116681 295413408008540394087511)
                  ·
                    rfl

theorem cell20_647230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_647230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647230 prefixEnd_647230 := by exact prefixLift 647230
  have htrace : WordTrace (prefixWord ++ tailWord_647230) baseStart_647230 baseEnd_647230 := by
    simpa [prefixWord, tailWord_647230, baseEnd_647230] using wordTrace_append hprefix tailTrace_647230
  have hstable : (prefixWord ++ tailWord_647230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647230).length < 2 ^ (prefixWord ++ tailWord_647230).sum := by decide
  have hdescent : baseEnd_647230 < baseStart_647230 := by decide
  rcases family_descends (prefixWord ++ tailWord_647230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647286 : List Nat := [5, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_647286 : Nat := 118140960795 + 647286 * 2 ^ 59
def prefixEnd_647286 : Nat := 4983230072969 + 3 ^ 40 * 647286 * 2
def baseEnd_647286 : Nat := 295438967934453088220615

theorem tailTrace_647286 : CollatzResearch.WordTrace tailWord_647286 prefixEnd_647286 295438967934453088220615 := by
  unfold tailWord_647286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1475528745812552780797607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15738973288667229661841141 1475528745812552780797607)
  ·
    refine ⟨2213293118718829171196411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1475528745812552780797607 2213293118718829171196411)
    ·
      refine ⟨3319939678078243756794617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2213293118718829171196411 3319939678078243756794617)
      ·
        refine ⟨2489954758558682817595963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3319939678078243756794617 2489954758558682817595963)
        ·
          refine ⟨3734932137838024226393945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2489954758558682817595963 3734932137838024226393945)
          ·
            refine ⟨2801199103378518169795459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3734932137838024226393945 2801199103378518169795459)
            ·
              refine ⟨4201798655067777254693189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801199103378518169795459 4201798655067777254693189)
              ·
                refine ⟨787837247825208235254973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4201798655067777254693189 787837247825208235254973)
                ·
                  refine ⟨295438967934453088220615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 787837247825208235254973 295438967934453088220615)
                  ·
                    rfl

theorem cell20_647286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_647286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647286 prefixEnd_647286 := by exact prefixLift 647286
  have htrace : WordTrace (prefixWord ++ tailWord_647286) baseStart_647286 baseEnd_647286 := by
    simpa [prefixWord, tailWord_647286, baseEnd_647286] using wordTrace_append hprefix tailTrace_647286
  have hstable : (prefixWord ++ tailWord_647286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647286).length < 2 ^ (prefixWord ++ tailWord_647286).sum := by decide
  have hdescent : baseEnd_647286 < baseStart_647286 := by decide
  rcases family_descends (prefixWord ++ tailWord_647286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647289 : List Nat := [1, 2, 1, 3, 4, 3, 2, 2, 2]
def baseStart_647289 : Nat := 118140960795 + 647289 * 2 ^ 59
def prefixEnd_647289 : Nat := 4983230072969 + 3 ^ 40 * 647289 * 2
def baseEnd_647289 : Nat := 295440337216198411120603

theorem tailTrace_647289 : CollatzResearch.WordTrace tailWord_647289 prefixEnd_647289 295440337216198411120603 := by
  unfold tailWord_647289
  simp only [CollatzResearch.WordTrace]
  refine ⟨23608569351989976005120921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15739046234659984003413947 23608569351989976005120921)
  ·
    refine ⟨17706427013992482003840691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23608569351989976005120921 17706427013992482003840691)
    ·
      refine ⟨26559640520988723005761037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17706427013992482003840691 26559640520988723005761037)
      ·
        refine ⟨9959865195370771127160389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26559640520988723005761037 9959865195370771127160389)
        ·
          refine ⟨1867474724132019586342573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9959865195370771127160389 1867474724132019586342573)
          ·
            refine ⟨700303021549507344878465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1867474724132019586342573 700303021549507344878465)
            ·
              refine ⟨525227266162130508658849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700303021549507344878465 525227266162130508658849)
              ·
                refine ⟨393920449621597881494137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525227266162130508658849 393920449621597881494137)
                ·
                  refine ⟨295440337216198411120603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393920449621597881494137 295440337216198411120603)
                  ·
                    rfl

theorem cell20_647289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 2].length) (baseStart_647289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647289 prefixEnd_647289 := by exact prefixLift 647289
  have htrace : WordTrace (prefixWord ++ tailWord_647289) baseStart_647289 baseEnd_647289 := by
    simpa [prefixWord, tailWord_647289, baseEnd_647289] using wordTrace_append hprefix tailTrace_647289
  have hstable : (prefixWord ++ tailWord_647289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647289).length < 2 ^ (prefixWord ++ tailWord_647289).sum := by decide
  have hdescent : baseEnd_647289 < baseStart_647289 := by decide
  rcases family_descends (prefixWord ++ tailWord_647289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647341 : List Nat := [1, 5, 2, 1, 2, 3, 1, 2, 3]
def baseStart_647341 : Nat := 118140960795 + 647341 * 2 ^ 59
def prefixEnd_647341 : Nat := 4983230072969 + 3 ^ 40 * 647341 * 2
def baseEnd_647341 : Nat := 295464071433117341387057

theorem tailTrace_647341 : CollatzResearch.WordTrace tailWord_647341 prefixEnd_647341 295464071433117341387057 := by
  unfold tailWord_647341
  simp only [CollatzResearch.WordTrace]
  refine ⟨23610465947801588886013877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15740310631867725924009251 23610465947801588886013877)
  ·
    refine ⟨2213481182606398958063801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23610465947801588886013877 2213481182606398958063801)
    ·
      refine ⟨1660110886954799218547851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2213481182606398958063801 1660110886954799218547851)
      ·
        refine ⟨2490166330432198827821777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660110886954799218547851 2490166330432198827821777)
        ·
          refine ⟨1867624747824149120866333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2490166330432198827821777 1867624747824149120866333)
          ·
            refine ⟨700359280434055920324875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1867624747824149120866333 700359280434055920324875)
            ·
              refine ⟨1050538920651083880487313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700359280434055920324875 1050538920651083880487313)
              ·
                refine ⟨787904190488312910365485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1050538920651083880487313 787904190488312910365485)
                ·
                  refine ⟨295464071433117341387057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 787904190488312910365485 295464071433117341387057)
                  ·
                    rfl

theorem cell20_647341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_647341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647341 prefixEnd_647341 := by exact prefixLift 647341
  have htrace : WordTrace (prefixWord ++ tailWord_647341) baseStart_647341 baseEnd_647341 := by
    simpa [prefixWord, tailWord_647341, baseEnd_647341] using wordTrace_append hprefix tailTrace_647341
  have hstable : (prefixWord ++ tailWord_647341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647341).length < 2 ^ (prefixWord ++ tailWord_647341).sum := by decide
  have hdescent : baseEnd_647341 < baseStart_647341 := by decide
  rcases family_descends (prefixWord ++ tailWord_647341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647352 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_647352 : Nat := 118140960795 + 647352 * 2 ^ 59
def prefixEnd_647352 : Nat := 4983230072969 + 3 ^ 40 * 647352 * 2
def baseEnd_647352 : Nat := 295469092132850192020345

theorem tailTrace_647352 : CollatzResearch.WordTrace tailWord_647352 prefixEnd_647352 295469092132850192020345 := by
  unfold tailWord_647352
  simp only [CollatzResearch.WordTrace]
  refine ⟨11805433575380868882332155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15740578100507825176442873 11805433575380868882332155)
  ·
    refine ⟨17708150363071303323498233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11805433575380868882332155 17708150363071303323498233)
    ·
      refine ⟨13281112772303477492623675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17708150363071303323498233 13281112772303477492623675)
      ·
        refine ⟨19921669158455216238935513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13281112772303477492623675 19921669158455216238935513)
        ·
          refine ⟨14941251868841412179201635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19921669158455216238935513 14941251868841412179201635)
          ·
            refine ⟨22411877803262118268802453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14941251868841412179201635 22411877803262118268802453)
            ·
              refine ⟨1050556772027911793850115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22411877803262118268802453 1050556772027911793850115)
              ·
                refine ⟨1575835158041867690775173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050556772027911793850115 1575835158041867690775173)
                ·
                  refine ⟨295469092132850192020345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1575835158041867690775173 295469092132850192020345)
                  ·
                    rfl

theorem cell20_647352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_647352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647352 prefixEnd_647352 := by exact prefixLift 647352
  have htrace : WordTrace (prefixWord ++ tailWord_647352) baseStart_647352 baseEnd_647352 := by
    simpa [prefixWord, tailWord_647352, baseEnd_647352] using wordTrace_append hprefix tailTrace_647352
  have hstable : (prefixWord ++ tailWord_647352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647352).length < 2 ^ (prefixWord ++ tailWord_647352).sum := by decide
  have hdescent : baseEnd_647352 < baseStart_647352 := by decide
  rcases family_descends (prefixWord ++ tailWord_647352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647372 : List Nat := [2, 2, 1, 6, 1, 2, 2, 4]
def baseStart_647372 : Nat := 118140960795 + 647372 * 2 ^ 59
def prefixEnd_647372 : Nat := 4983230072969 + 3 ^ 40 * 647372 * 2
def baseEnd_647372 : Nat := 98492740225939670451199

theorem tailTrace_647372 : CollatzResearch.WordTrace tailWord_647372 prefixEnd_647372 98492740225939670451199 := by
  unfold tailWord_647372
  simp only [CollatzResearch.WordTrace]
  refine ⟨11805798305344640590196185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15741064407126187453594913 11805798305344640590196185)
  ·
    refine ⟨8854348729008480442647139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11805798305344640590196185 8854348729008480442647139)
    ·
      refine ⟨13281523093512720663970709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8854348729008480442647139 13281523093512720663970709)
      ·
        refine ⟨622571395008408781123627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13281523093512720663970709 622571395008408781123627)
        ·
          refine ⟨933857092512613171685441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622571395008408781123627 933857092512613171685441)
          ·
            refine ⟨700392819384459878764081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 933857092512613171685441 700392819384459878764081)
            ·
              refine ⟨525294614538344909073061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700392819384459878764081 525294614538344909073061)
              ·
                refine ⟨98492740225939670451199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 525294614538344909073061 98492740225939670451199)
                ·
                  rfl

theorem cell20_647372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_647372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647372 prefixEnd_647372 := by exact prefixLift 647372
  have htrace : WordTrace (prefixWord ++ tailWord_647372) baseStart_647372 baseEnd_647372 := by
    simpa [prefixWord, tailWord_647372, baseEnd_647372] using wordTrace_append hprefix tailTrace_647372
  have hstable : (prefixWord ++ tailWord_647372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647372).length < 2 ^ (prefixWord ++ tailWord_647372).sum := by decide
  have hdescent : baseEnd_647372 < baseStart_647372 := by decide
  rcases family_descends (prefixWord ++ tailWord_647372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647382 : List Nat := [5, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_647382 : Nat := 118140960795 + 647382 * 2 ^ 59
def prefixEnd_647382 : Nat := 4983230072969 + 3 ^ 40 * 647382 * 2
def baseEnd_647382 : Nat := 295482784950303421020223

theorem tailTrace_647382 : CollatzResearch.WordTrace tailWord_647382 prefixEnd_647382 295482784950303421020223 := by
  unfold tailWord_647382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1475747583790815805516025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15741307560435368592170933 1475747583790815805516025)
  ·
    refine ⟨1106810687843111854137019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1475747583790815805516025 1106810687843111854137019)
    ·
      refine ⟨1660216031764667781205529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1106810687843111854137019 1660216031764667781205529)
      ·
        refine ⟨1245162023823500835904147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1660216031764667781205529 1245162023823500835904147)
        ·
          refine ⟨1867743035735251253856221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245162023823500835904147 1867743035735251253856221)
          ·
            refine ⟨700403638400719220196083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1867743035735251253856221 700403638400719220196083)
            ·
              refine ⟨1050605457601078830294125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700403638400719220196083 1050605457601078830294125)
              ·
                refine ⟨393977046600404561360297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1050605457601078830294125 393977046600404561360297)
                ·
                  refine ⟨295482784950303421020223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393977046600404561360297 295482784950303421020223)
                  ·
                    rfl

theorem cell20_647382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_647382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647382 prefixEnd_647382 := by exact prefixLift 647382
  have htrace : WordTrace (prefixWord ++ tailWord_647382) baseStart_647382 baseEnd_647382 := by
    simpa [prefixWord, tailWord_647382, baseEnd_647382] using wordTrace_append hprefix tailTrace_647382
  have hstable : (prefixWord ++ tailWord_647382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647382).length < 2 ^ (prefixWord ++ tailWord_647382).sum := by decide
  have hdescent : baseEnd_647382 < baseStart_647382 := by decide
  rcases family_descends (prefixWord ++ tailWord_647382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647397 : List Nat := [1, 3, 1, 4, 2, 1, 8]
def baseStart_647397 : Nat := 118140960795 + 647397 * 2 ^ 59
def prefixEnd_647397 : Nat := 4983230072969 + 3 ^ 40 * 647397 * 2
def baseEnd_647397 : Nat := 32832181262114448391129

theorem tailTrace_647397 : CollatzResearch.WordTrace tailWord_647397 prefixEnd_647397 32832181262114448391129 := by
  unfold tailWord_647397
  simp only [CollatzResearch.WordTrace]
  refine ⟨23612508435598710450052445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15741672290399140300034963 23612508435598710450052445)
  ·
    refine ⟨8854690663349516418769667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23612508435598710450052445 8854690663349516418769667)
    ·
      refine ⟨13282035995024274628154501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8854690663349516418769667 13282035995024274628154501)
      ·
        refine ⟨2490381749067051492778969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13282035995024274628154501 2490381749067051492778969)
        ·
          refine ⟨1867786311800288619584227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2490381749067051492778969 1867786311800288619584227)
          ·
            refine ⟨2801679467700432929376341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867786311800288619584227 2801679467700432929376341)
            ·
              refine ⟨32832181262114448391129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2801679467700432929376341 32832181262114448391129)
              ·
                rfl

theorem cell20_647397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 8].length) (baseStart_647397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647397 prefixEnd_647397 := by exact prefixLift 647397
  have htrace : WordTrace (prefixWord ++ tailWord_647397) baseStart_647397 baseEnd_647397 := by
    simpa [prefixWord, tailWord_647397, baseEnd_647397] using wordTrace_append hprefix tailTrace_647397
  have hstable : (prefixWord ++ tailWord_647397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647397).length < 2 ^ (prefixWord ++ tailWord_647397).sum := by decide
  have hdescent : baseEnd_647397 < baseStart_647397 := by decide
  rcases family_descends (prefixWord ++ tailWord_647397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647404 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_647404 : Nat := 118140960795 + 647404 * 2 ^ 59
def prefixEnd_647404 : Nat := 4983230072969 + 3 ^ 40 * 647404 * 2
def baseEnd_647404 : Nat := 295492826349769122286799

theorem tailTrace_647404 : CollatzResearch.WordTrace tailWord_647404 prefixEnd_647404 295492826349769122286799 := by
  unfold tailWord_647404
  simp only [CollatzResearch.WordTrace]
  refine ⟨11806381873286675322778633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15741842497715567097038177 11806381873286675322778633)
  ·
    refine ⟨8854786404965006492083975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11806381873286675322778633 8854786404965006492083975)
    ·
      refine ⟨13282179607447509738125963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8854786404965006492083975 13282179607447509738125963)
      ·
        refine ⟨19923269411171264607188945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13282179607447509738125963 19923269411171264607188945)
        ·
          refine ⟨14942452058378448455391709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19923269411171264607188945 14942452058378448455391709)
          ·
            refine ⟨5603419521891918170771891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14942452058378448455391709 5603419521891918170771891)
            ·
              refine ⟨8405129282837877256157837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5603419521891918170771891 8405129282837877256157837)
              ·
                refine ⟨3151923481064203971059189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8405129282837877256157837 3151923481064203971059189)
                ·
                  refine ⟨295492826349769122286799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3151923481064203971059189 295492826349769122286799)
                  ·
                    rfl

theorem cell20_647404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_647404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647404 prefixEnd_647404 := by exact prefixLift 647404
  have htrace : WordTrace (prefixWord ++ tailWord_647404) baseStart_647404 baseEnd_647404 := by
    simpa [prefixWord, tailWord_647404, baseEnd_647404] using wordTrace_append hprefix tailTrace_647404
  have hstable : (prefixWord ++ tailWord_647404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647404).length < 2 ^ (prefixWord ++ tailWord_647404).sum := by decide
  have hdescent : baseEnd_647404 < baseStart_647404 := by decide
  rcases family_descends (prefixWord ++ tailWord_647404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647407 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 4]
def baseStart_647407 : Nat := 118140960795 + 647407 * 2 ^ 59
def prefixEnd_647407 : Nat := 4983230072969 + 3 ^ 40 * 647407 * 2
def baseEnd_647407 : Nat := 295494195631514445186787

theorem tailTrace_647407 : CollatzResearch.WordTrace tailWord_647407 prefixEnd_647407 295494195631514445186787 := by
  unfold tailWord_647407
  simp only [CollatzResearch.WordTrace]
  refine ⟨23612873165562482157916475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15741915443708321438610983 23612873165562482157916475)
  ·
    refine ⟨35419309748343723236874713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23612873165562482157916475 35419309748343723236874713)
    ·
      refine ⟨26564482311257792427656035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35419309748343723236874713 26564482311257792427656035)
      ·
        refine ⟨39846723466886688641484053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26564482311257792427656035 39846723466886688641484053)
        ·
          refine ⟨1867815162510313530069565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39846723466886688641484053 1867815162510313530069565)
          ·
            refine ⟨700430685941367573776087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1867815162510313530069565 700430685941367573776087)
            ·
              refine ⟨1050646028912051360664131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700430685941367573776087 1050646028912051360664131)
              ·
                refine ⟨1575969043368077040996197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050646028912051360664131 1575969043368077040996197)
                ·
                  refine ⟨295494195631514445186787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1575969043368077040996197 295494195631514445186787)
                  ·
                    rfl

theorem cell20_647407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 4].length) (baseStart_647407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647407 prefixEnd_647407 := by exact prefixLift 647407
  have htrace : WordTrace (prefixWord ++ tailWord_647407) baseStart_647407 baseEnd_647407 := by
    simpa [prefixWord, tailWord_647407, baseEnd_647407] using wordTrace_append hprefix tailTrace_647407
  have hstable : (prefixWord ++ tailWord_647407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647407).length < 2 ^ (prefixWord ++ tailWord_647407).sum := by decide
  have hdescent : baseEnd_647407 < baseStart_647407 := by decide
  rcases family_descends (prefixWord ++ tailWord_647407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647459 : List Nat := [1, 1, 1, 4, 2, 2, 4, 2, 3]
def baseStart_647459 : Nat := 118140960795 + 647459 * 2 ^ 59
def prefixEnd_647459 : Nat := 4983230072969 + 3 ^ 40 * 647459 * 2
def baseEnd_647459 : Nat := 295517929848433375453241

theorem tailTrace_647459 : CollatzResearch.WordTrace tailWord_647459 prefixEnd_647459 295517929848433375453241 := by
  unfold tailWord_647459
  simp only [CollatzResearch.WordTrace]
  refine ⟨23614769761374095038809431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15743179840916063359206287 23614769761374095038809431)
  ·
    refine ⟨35422154642061142558214147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23614769761374095038809431 35422154642061142558214147)
    ·
      refine ⟨53133231963091713837321221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35422154642061142558214147 53133231963091713837321221)
      ·
        refine ⟨9962480993079696344497729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53133231963091713837321221 9962480993079696344497729)
        ·
          refine ⟨7471860744809772258373297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9962480993079696344497729 7471860744809772258373297)
          ·
            refine ⟨5603895558607329193779973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7471860744809772258373297 5603895558607329193779973)
            ·
              refine ⟨1050730417238874223833745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5603895558607329193779973 1050730417238874223833745)
              ·
                refine ⟨788047812929155667875309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1050730417238874223833745 788047812929155667875309)
                ·
                  refine ⟨295517929848433375453241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788047812929155667875309 295517929848433375453241)
                  ·
                    rfl

theorem cell20_647459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 3].length) (baseStart_647459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647459 prefixEnd_647459 := by exact prefixLift 647459
  have htrace : WordTrace (prefixWord ++ tailWord_647459) baseStart_647459 baseEnd_647459 := by
    simpa [prefixWord, tailWord_647459, baseEnd_647459] using wordTrace_append hprefix tailTrace_647459
  have hstable : (prefixWord ++ tailWord_647459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647459).length < 2 ^ (prefixWord ++ tailWord_647459).sum := by decide
  have hdescent : baseEnd_647459 < baseStart_647459 := by decide
  rcases family_descends (prefixWord ++ tailWord_647459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647476 : List Nat := [2, 5, 1, 1, 1, 2, 2, 3, 3]
def baseStart_647476 : Nat := 118140960795 + 647476 * 2 ^ 59
def prefixEnd_647476 : Nat := 4983230072969 + 3 ^ 40 * 647476 * 2
def baseEnd_647476 : Nat := 295525689111656871886505

theorem tailTrace_647476 : CollatzResearch.WordTrace tailWord_647476 prefixEnd_647476 295525689111656871886505 := by
  unfold tailWord_647476
  simp only [CollatzResearch.WordTrace]
  refine ⟨11807694901156253471089141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15743593201541671294785521 11807694901156253471089141)
  ·
    refine ⟨1106971396983398762914607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11807694901156253471089141 1106971396983398762914607)
    ·
      refine ⟨1660457095475098144371911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1106971396983398762914607 1660457095475098144371911)
      ·
        refine ⟨2490685643212647216557867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660457095475098144371911 2490685643212647216557867)
        ·
          refine ⟨3736028464818970824836801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2490685643212647216557867 3736028464818970824836801)
          ·
            refine ⟨2802021348614228118627601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3736028464818970824836801 2802021348614228118627601)
            ·
              refine ⟨2101516011460671088970701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802021348614228118627601 2101516011460671088970701)
              ·
                refine ⟨788068504297751658364013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2101516011460671088970701 788068504297751658364013)
                ·
                  refine ⟨295525689111656871886505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788068504297751658364013 295525689111656871886505)
                  ·
                    rfl

theorem cell20_647476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_647476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647476 prefixEnd_647476 := by exact prefixLift 647476
  have htrace : WordTrace (prefixWord ++ tailWord_647476) baseStart_647476 baseEnd_647476 := by
    simpa [prefixWord, tailWord_647476, baseEnd_647476] using wordTrace_append hprefix tailTrace_647476
  have hstable : (prefixWord ++ tailWord_647476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647476).length < 2 ^ (prefixWord ++ tailWord_647476).sum := by decide
  have hdescent : baseEnd_647476 < baseStart_647476 := by decide
  rcases family_descends (prefixWord ++ tailWord_647476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647549 : List Nat := [1, 4, 1, 1, 2, 4, 1, 6]
def baseStart_647549 : Nat := 118140960795 + 647549 * 2 ^ 59
def prefixEnd_647549 : Nat := 4983230072969 + 3 ^ 40 * 647549 * 2
def baseEnd_647549 : Nat := 98519669433597687484291

theorem tailTrace_647549 : CollatzResearch.WordTrace tailWord_647549 prefixEnd_647549 98519669433597687484291 := by
  unfold tailWord_647549
  simp only [CollatzResearch.WordTrace]
  refine ⟨23618052331048040409585701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15745368220698693606390467 23618052331048040409585701)
  ·
    refine ⟨4428384812071507576797319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23618052331048040409585701 4428384812071507576797319)
    ·
      refine ⟨6642577218107261365195979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4428384812071507576797319 6642577218107261365195979)
      ·
        refine ⟨9963865827160892047793969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6642577218107261365195979 9963865827160892047793969)
        ·
          refine ⟨7472899370370669035845477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9963865827160892047793969 7472899370370669035845477)
          ·
            refine ⟨1401168631944500444221027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7472899370370669035845477 1401168631944500444221027)
            ·
              refine ⟨2101752947916750666331541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401168631944500444221027 2101752947916750666331541)
              ·
                refine ⟨98519669433597687484291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2101752947916750666331541 98519669433597687484291)
                ·
                  rfl

theorem cell20_647549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_647549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647549 prefixEnd_647549 := by exact prefixLift 647549
  have htrace : WordTrace (prefixWord ++ tailWord_647549) baseStart_647549 baseEnd_647549 := by
    simpa [prefixWord, tailWord_647549, baseEnd_647549] using wordTrace_append hprefix tailTrace_647549
  have hstable : (prefixWord ++ tailWord_647549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647549).length < 2 ^ (prefixWord ++ tailWord_647549).sum := by decide
  have hdescent : baseEnd_647549 < baseStart_647549 := by decide
  rcases family_descends (prefixWord ++ tailWord_647549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647555 : List Nat := [1, 1, 1, 3, 7, 1, 1, 3, 2]
def baseStart_647555 : Nat := 118140960795 + 647555 * 2 ^ 59
def prefixEnd_647555 : Nat := 4983230072969 + 3 ^ 40 * 647555 * 2
def baseEnd_647555 : Nat := 295561746864283708252849

theorem tailTrace_647555 : CollatzResearch.WordTrace tailWord_647555 prefixEnd_647555 295561746864283708252849 := by
  unfold tailWord_647555
  simp only [CollatzResearch.WordTrace]
  refine ⟨23618271169026303434304119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15745514112684202289536079 23618271169026303434304119)
  ·
    refine ⟨35427406753539455151456179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23618271169026303434304119 35427406753539455151456179)
    ·
      refine ⟨53141110130309182727184269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35427406753539455151456179 53141110130309182727184269)
      ·
        refine ⟨19927916298865943522694101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53141110130309182727184269 19927916298865943522694101)
        ·
          refine ⟨467060538254670551313143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19927916298865943522694101 467060538254670551313143)
          ·
            refine ⟨700590807382005826969715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467060538254670551313143 700590807382005826969715)
            ·
              refine ⟨1050886211073008740454573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700590807382005826969715 1050886211073008740454573)
              ·
                refine ⟨394082329152378277670465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1050886211073008740454573 394082329152378277670465)
                ·
                  refine ⟨295561746864283708252849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394082329152378277670465 295561746864283708252849)
                  ·
                    rfl

theorem cell20_647555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 2].length) (baseStart_647555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647555 prefixEnd_647555 := by exact prefixLift 647555
  have htrace : WordTrace (prefixWord ++ tailWord_647555) baseStart_647555 baseEnd_647555 := by
    simpa [prefixWord, tailWord_647555, baseEnd_647555] using wordTrace_append hprefix tailTrace_647555
  have hstable : (prefixWord ++ tailWord_647555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647555).length < 2 ^ (prefixWord ++ tailWord_647555).sum := by decide
  have hdescent : baseEnd_647555 < baseStart_647555 := by decide
  rcases family_descends (prefixWord ++ tailWord_647555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647556 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_647556 : Nat := 118140960795 + 647556 * 2 ^ 59
def prefixEnd_647556 : Nat := 4983230072969 + 3 ^ 40 * 647556 * 2
def baseEnd_647556 : Nat := 295562203291532149219511

theorem tailTrace_647556 : CollatzResearch.WordTrace tailWord_647556 prefixEnd_647556 295562203291532149219511 := by
  unfold tailWord_647556
  simp only [CollatzResearch.WordTrace]
  refine ⟨11809153821011340302545261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15745538428015120403393681 11809153821011340302545261)
  ·
    refine ⟨4428432682879252613454473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11809153821011340302545261 4428432682879252613454473)
    ·
      refine ⟨3321324512159439460090855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4428432682879252613454473 3321324512159439460090855)
      ·
        refine ⟨4981986768239159190136283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3321324512159439460090855 4981986768239159190136283)
        ·
          refine ⟨7472980152358738785204425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4981986768239159190136283 7472980152358738785204425)
          ·
            refine ⟨5604735114269054088903319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7472980152358738785204425 5604735114269054088903319)
            ·
              refine ⟨8407102671403581133354979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5604735114269054088903319 8407102671403581133354979)
              ·
                refine ⟨12610654007105371700032469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8407102671403581133354979 12610654007105371700032469)
                ·
                  refine ⟨295562203291532149219511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12610654007105371700032469 295562203291532149219511)
                  ·
                    rfl

theorem cell20_647556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_647556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647556 prefixEnd_647556 := by exact prefixLift 647556
  have htrace : WordTrace (prefixWord ++ tailWord_647556) baseStart_647556 baseEnd_647556 := by
    simpa [prefixWord, tailWord_647556, baseEnd_647556] using wordTrace_append hprefix tailTrace_647556
  have hstable : (prefixWord ++ tailWord_647556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647556).length < 2 ^ (prefixWord ++ tailWord_647556).sum := by decide
  have hdescent : baseEnd_647556 < baseStart_647556 := by decide
  rcases family_descends (prefixWord ++ tailWord_647556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647566 : List Nat := [4, 1, 1, 4, 1, 3, 6]
def baseStart_647566 : Nat := 118140960795 + 647566 * 2 ^ 59
def prefixEnd_647566 : Nat := 4983230072969 + 3 ^ 40 * 647566 * 2
def baseEnd_647566 : Nat := 32840751951557395431793

theorem tailTrace_647566 : CollatzResearch.WordTrace tailWord_647566 prefixEnd_647566 32840751951557395431793 := by
  unfold tailWord_647566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2952334046498306539119319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15745781581324301541969701 2952334046498306539119319)
  ·
    refine ⟨4428501069747459808678979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2952334046498306539119319 4428501069747459808678979)
    ·
      refine ⟨6642751604621189713018469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4428501069747459808678979 6642751604621189713018469)
      ·
        refine ⟨1245515925866473071190963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6642751604621189713018469 1245515925866473071190963)
        ·
          refine ⟨1868273888799709606786445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245515925866473071190963 1868273888799709606786445)
          ·
            refine ⟨700602708299891102544917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1868273888799709606786445 700602708299891102544917)
            ·
              refine ⟨32840751951557395431793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 700602708299891102544917 32840751951557395431793)
              ·
                rfl

theorem cell20_647566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 6].length) (baseStart_647566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647566 prefixEnd_647566 := by exact prefixLift 647566
  have htrace : WordTrace (prefixWord ++ tailWord_647566) baseStart_647566 baseEnd_647566 := by
    simpa [prefixWord, tailWord_647566, baseEnd_647566] using wordTrace_append hprefix tailTrace_647566
  have hstable : (prefixWord ++ tailWord_647566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647566).length < 2 ^ (prefixWord ++ tailWord_647566).sum := by decide
  have hdescent : baseEnd_647566 < baseStart_647566 := by decide
  rcases family_descends (prefixWord ++ tailWord_647566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647587 : List Nat := [1, 1, 1, 4, 1, 5, 2, 5]
def baseStart_647587 : Nat := 118140960795 + 647587 * 2 ^ 59
def prefixEnd_647587 : Nat := 4983230072969 + 3 ^ 40 * 647587 * 2
def baseEnd_647587 : Nat := 98525450845411273062017

theorem tailTrace_647587 : CollatzResearch.WordTrace tailWord_647587 prefixEnd_647587 98525450845411273062017 := by
  unfold tailWord_647587
  simp only [CollatzResearch.WordTrace]
  refine ⟨23619438304910372899469015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15746292203273581932979343 23619438304910372899469015)
  ·
    refine ⟨35429157457365559349203523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23619438304910372899469015 35429157457365559349203523)
    ·
      refine ⟨53143736186048339023805285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35429157457365559349203523 53143736186048339023805285)
      ·
        refine ⟨9964450534884063566963491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53143736186048339023805285 9964450534884063566963491)
        ·
          refine ⟨14946675802326095350445237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9964450534884063566963491 14946675802326095350445237)
          ·
            refine ⟨1401250856468071439104241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14946675802326095350445237 1401250856468071439104241)
            ·
              refine ⟨1050938142351053579328181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1401250856468071439104241 1050938142351053579328181)
              ·
                refine ⟨98525450845411273062017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1050938142351053579328181 98525450845411273062017)
                ·
                  rfl

theorem cell20_647587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_647587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647587 prefixEnd_647587 := by exact prefixLift 647587
  have htrace : WordTrace (prefixWord ++ tailWord_647587) baseStart_647587 baseEnd_647587 := by
    simpa [prefixWord, tailWord_647587, baseEnd_647587] using wordTrace_append hprefix tailTrace_647587
  have hstable : (prefixWord ++ tailWord_647587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647587).length < 2 ^ (prefixWord ++ tailWord_647587).sum := by decide
  have hdescent : baseEnd_647587 < baseStart_647587 := by decide
  rcases family_descends (prefixWord ++ tailWord_647587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647628 : List Nat := [2, 2, 1, 4, 3, 1, 2, 2, 3]
def baseStart_647628 : Nat := 118140960795 + 647628 * 2 ^ 59
def prefixEnd_647628 : Nat := 4983230072969 + 3 ^ 40 * 647628 * 2
def baseEnd_647628 : Nat := 295595066053419898819217

theorem tailTrace_647628 : CollatzResearch.WordTrace tailWord_647628 prefixEnd_647628 295595066053419898819217 := by
  unfold tailWord_647628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11810466848880918450855769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15747289131841224601141025 11810466848880918450855769)
  ·
    refine ⟨8857850136660688838141827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11810466848880918450855769 8857850136660688838141827)
    ·
      refine ⟨13286775204991033257212741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8857850136660688838141827 13286775204991033257212741)
      ·
        refine ⟨2491270350935818735727389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13286775204991033257212741 2491270350935818735727389)
        ·
          refine ⟨934226381600932025897771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2491270350935818735727389 934226381600932025897771)
          ·
            refine ⟨1401339572401398038846657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934226381600932025897771 1401339572401398038846657)
            ·
              refine ⟨1051004679301048529134993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1401339572401398038846657 1051004679301048529134993)
              ·
                refine ⟨788253509475786396851245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051004679301048529134993 788253509475786396851245)
                ·
                  refine ⟨295595066053419898819217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788253509475786396851245 295595066053419898819217)
                  ·
                    rfl

theorem cell20_647628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_647628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647628 prefixEnd_647628 := by exact prefixLift 647628
  have htrace : WordTrace (prefixWord ++ tailWord_647628) baseStart_647628 baseEnd_647628 := by
    simpa [prefixWord, tailWord_647628, baseEnd_647628] using wordTrace_append hprefix tailTrace_647628
  have hstable : (prefixWord ++ tailWord_647628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647628).length < 2 ^ (prefixWord ++ tailWord_647628).sum := by decide
  have hdescent : baseEnd_647628 < baseStart_647628 := by decide
  rcases family_descends (prefixWord ++ tailWord_647628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647656 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_647656 : Nat := 118140960795 + 647656 * 2 ^ 59
def prefixEnd_647656 : Nat := 4983230072969 + 3 ^ 40 * 647656 * 2
def baseEnd_647656 : Nat := 295607846016376245885769

theorem tailTrace_647656 : CollatzResearch.WordTrace tailWord_647656 prefixEnd_647656 295607846016376245885769 := by
  unfold tailWord_647656
  simp only [CollatzResearch.WordTrace]
  refine ⟨11810977470830198841865411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15747969961106931789153881 11810977470830198841865411)
  ·
    refine ⟨17716466206245298262798117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11810977470830198841865411 17716466206245298262798117)
    ·
      refine ⟨3321837413670993424274647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17716466206245298262798117 3321837413670993424274647)
      ·
        refine ⟨4982756120506490136411971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3321837413670993424274647 4982756120506490136411971)
        ·
          refine ⟨7474134180759735204617957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4982756120506490136411971 7474134180759735204617957)
          ·
            refine ⟨1401400158892450350865867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7474134180759735204617957 1401400158892450350865867)
            ·
              refine ⟨2102100238338675526298801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401400158892450350865867 2102100238338675526298801)
              ·
                refine ⟨1576575178754006644724101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2102100238338675526298801 1576575178754006644724101)
                ·
                  refine ⟨295607846016376245885769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1576575178754006644724101 295607846016376245885769)
                  ·
                    rfl

theorem cell20_647656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_647656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647656 prefixEnd_647656 := by exact prefixLift 647656
  have htrace : WordTrace (prefixWord ++ tailWord_647656) baseStart_647656 baseEnd_647656 := by
    simpa [prefixWord, tailWord_647656, baseEnd_647656] using wordTrace_append hprefix tailTrace_647656
  have hstable : (prefixWord ++ tailWord_647656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647656).length < 2 ^ (prefixWord ++ tailWord_647656).sum := by decide
  have hdescent : baseEnd_647656 < baseStart_647656 := by decide
  rcases family_descends (prefixWord ++ tailWord_647656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647669 : List Nat := [1, 3, 5, 1, 2, 1, 2, 3, 2]
def baseStart_647669 : Nat := 118140960795 + 647669 * 2 ^ 59
def prefixEnd_647669 : Nat := 4983230072969 + 3 ^ 40 * 647669 * 2
def baseEnd_647669 : Nat := 295613779570605978452383

theorem tailTrace_647669 : CollatzResearch.WordTrace tailWord_647669 prefixEnd_647669 295613779570605978452383 := by
  unfold tailWord_647669
  simp only [CollatzResearch.WordTrace]
  refine ⟨23622429090613300903954061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15748286060408867269302707 23622429090613300903954061)
  ·
    refine ⟨8858410908979987838982773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23622429090613300903954061 8858410908979987838982773)
    ·
      refine ⟨830476022716873859904635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8858410908979987838982773 830476022716873859904635)
      ·
        refine ⟨1245714034075310789856953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830476022716873859904635 1245714034075310789856953)
        ·
          refine ⟨934285525556483092392715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1245714034075310789856953 934285525556483092392715)
          ·
            refine ⟨1401428288334724638589073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934285525556483092392715 1401428288334724638589073)
            ·
              refine ⟨1051071216251043478941805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1401428288334724638589073 1051071216251043478941805)
              ·
                refine ⟨394151706094141304603177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1051071216251043478941805 394151706094141304603177)
                ·
                  refine ⟨295613779570605978452383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394151706094141304603177 295613779570605978452383)
                  ·
                    rfl

theorem cell20_647669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_647669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647669 prefixEnd_647669 := by exact prefixLift 647669
  have htrace : WordTrace (prefixWord ++ tailWord_647669) baseStart_647669 baseEnd_647669 := by
    simpa [prefixWord, tailWord_647669, baseEnd_647669] using wordTrace_append hprefix tailTrace_647669
  have hstable : (prefixWord ++ tailWord_647669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647669).length < 2 ^ (prefixWord ++ tailWord_647669).sum := by decide
  have hdescent : baseEnd_647669 < baseStart_647669 := by decide
  rcases family_descends (prefixWord ++ tailWord_647669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647677 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 6]
def baseStart_647677 : Nat := 118140960795 + 647677 * 2 ^ 59
def prefixEnd_647677 : Nat := 4983230072969 + 3 ^ 40 * 647677 * 2
def baseEnd_647677 : Nat := 295617430988593506185683

theorem tailTrace_647677 : CollatzResearch.WordTrace tailWord_647677 prefixEnd_647677 295617430988593506185683 := by
  unfold tailWord_647677
  simp only [CollatzResearch.WordTrace]
  refine ⟨23622720874584318270245285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15748480583056212180163523 23622720874584318270245285)
  ·
    refine ⟨4429260163984559675670991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23622720874584318270245285 4429260163984559675670991)
    ·
      refine ⟨6643890245976839513506487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4429260163984559675670991 6643890245976839513506487)
      ·
        refine ⟨9965835368965259270259731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6643890245976839513506487 9965835368965259270259731)
        ·
          refine ⟨14948753053447888905389597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9965835368965259270259731 14948753053447888905389597)
          ·
            refine ⟨5605782395042958339521099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14948753053447888905389597 5605782395042958339521099)
            ·
              refine ⟨8408673592564437509281649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5605782395042958339521099 8408673592564437509281649)
              ·
                refine ⟨6306505194423328131961237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8408673592564437509281649 6306505194423328131961237)
                ·
                  refine ⟨295617430988593506185683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6306505194423328131961237 295617430988593506185683)
                  ·
                    rfl

theorem cell20_647677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_647677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647677 prefixEnd_647677 := by exact prefixLift 647677
  have htrace : WordTrace (prefixWord ++ tailWord_647677) baseStart_647677 baseEnd_647677 := by
    simpa [prefixWord, tailWord_647677, baseEnd_647677] using wordTrace_append hprefix tailTrace_647677
  have hstable : (prefixWord ++ tailWord_647677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647677).length < 2 ^ (prefixWord ++ tailWord_647677).sum := by decide
  have hdescent : baseEnd_647677 < baseStart_647677 := by decide
  rcases family_descends (prefixWord ++ tailWord_647677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647686 : List Nat := [6, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_647686 : Nat := 118140960795 + 647686 * 2 ^ 59
def prefixEnd_647686 : Nat := 4983230072969 + 3 ^ 40 * 647686 * 2
def baseEnd_647686 : Nat := 295621538833829474885647

theorem tailTrace_647686 : CollatzResearch.WordTrace tailWord_647686 prefixEnd_647686 295621538833829474885647 := by
  unfold tailWord_647686
  simp only [CollatzResearch.WordTrace]
  refine ⟨738220285360991025228841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15748699421034475204881941 738220285360991025228841)
  ·
    refine ⟨553665214020743268921631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 738220285360991025228841 553665214020743268921631)
    ·
      refine ⟨830497821031114903382447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 553665214020743268921631 830497821031114903382447)
      ·
        refine ⟨1245746731546672355073671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830497821031114903382447 1245746731546672355073671)
        ·
          refine ⟨1868620097320008532610507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245746731546672355073671 1868620097320008532610507)
          ·
            refine ⟨2802930145980012798915761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868620097320008532610507 2802930145980012798915761)
            ·
              refine ⟨2102197609485009599186821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802930145980012798915761 2102197609485009599186821)
              ·
                refine ⟨394162051778439299847529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2102197609485009599186821 394162051778439299847529)
                ·
                  refine ⟨295621538833829474885647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394162051778439299847529 295621538833829474885647)
                  ·
                    rfl

theorem cell20_647686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_647686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647686 prefixEnd_647686 := by exact prefixLift 647686
  have htrace : WordTrace (prefixWord ++ tailWord_647686) baseStart_647686 baseEnd_647686 := by
    simpa [prefixWord, tailWord_647686, baseEnd_647686] using wordTrace_append hprefix tailTrace_647686
  have hstable : (prefixWord ++ tailWord_647686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647686).length < 2 ^ (prefixWord ++ tailWord_647686).sum := by decide
  have hdescent : baseEnd_647686 < baseStart_647686 := by decide
  rcases family_descends (prefixWord ++ tailWord_647686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647687 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 5]
def baseStart_647687 : Nat := 118140960795 + 647687 * 2 ^ 59
def prefixEnd_647687 : Nat := 4983230072969 + 3 ^ 40 * 647687 * 2
def baseEnd_647687 : Nat := 295621995261077915852309

theorem tailTrace_647687 : CollatzResearch.WordTrace tailWord_647687 prefixEnd_647687 295621995261077915852309 := by
  unfold tailWord_647687
  simp only [CollatzResearch.WordTrace]
  refine ⟨23623085604548089978109315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15748723736365393318739543 23623085604548089978109315)
  ·
    refine ⟨35434628406822134967163973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23623085604548089978109315 35434628406822134967163973)
    ·
      refine ⟨6643992826279150306343245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35434628406822134967163973 6643992826279150306343245)
      ·
        refine ⟨2491497309854681364878717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6643992826279150306343245 2491497309854681364878717)
        ·
          refine ⟨934311491195505511829519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2491497309854681364878717 934311491195505511829519)
          ·
            refine ⟨1401467236793258267744279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934311491195505511829519 1401467236793258267744279)
            ·
              refine ⟨2102200855189887401616419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401467236793258267744279 2102200855189887401616419)
              ·
                refine ⟨3153301282784831102424629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102200855189887401616419 3153301282784831102424629)
                ·
                  refine ⟨295621995261077915852309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3153301282784831102424629 295621995261077915852309)
                  ·
                    rfl

theorem cell20_647687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 5].length) (baseStart_647687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647687 prefixEnd_647687 := by exact prefixLift 647687
  have htrace : WordTrace (prefixWord ++ tailWord_647687) baseStart_647687 baseEnd_647687 := by
    simpa [prefixWord, tailWord_647687, baseEnd_647687] using wordTrace_append hprefix tailTrace_647687
  have hstable : (prefixWord ++ tailWord_647687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647687).length < 2 ^ (prefixWord ++ tailWord_647687).sum := by decide
  have hdescent : baseEnd_647687 < baseStart_647687 := by decide
  rcases family_descends (prefixWord ++ tailWord_647687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647694 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_647694 : Nat := 118140960795 + 647694 * 2 ^ 59
def prefixEnd_647694 : Nat := 4983230072969 + 3 ^ 40 * 647694 * 2
def baseEnd_647694 : Nat := 295625190251817002618947

theorem tailTrace_647694 : CollatzResearch.WordTrace tailWord_647694 prefixEnd_647694 295625190251817002618947 := by
  unfold tailWord_647694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2952917614440341271701767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15748893943681820115742757 2952917614440341271701767)
  ·
    refine ⟨4429376421660511907552651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2952917614440341271701767 4429376421660511907552651)
    ·
      refine ⟨6644064632490767861328977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4429376421660511907552651 6644064632490767861328977)
      ·
        refine ⟨4983048474368075895996733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6644064632490767861328977 4983048474368075895996733)
        ·
          refine ⟨1868643177888028460998775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4983048474368075895996733 1868643177888028460998775)
          ·
            refine ⟨2802964766832042691498163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868643177888028460998775 2802964766832042691498163)
            ·
              refine ⟨4204447150248064037247245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802964766832042691498163 4204447150248064037247245)
              ·
                refine ⟨1576667681343024013967717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4204447150248064037247245 1576667681343024013967717)
                ·
                  refine ⟨295625190251817002618947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1576667681343024013967717 295625190251817002618947)
                  ·
                    rfl

theorem cell20_647694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_647694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647694 prefixEnd_647694 := by exact prefixLift 647694
  have htrace : WordTrace (prefixWord ++ tailWord_647694) baseStart_647694 baseEnd_647694 := by
    simpa [prefixWord, tailWord_647694, baseEnd_647694] using wordTrace_append hprefix tailTrace_647694
  have hstable : (prefixWord ++ tailWord_647694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647694).length < 2 ^ (prefixWord ++ tailWord_647694).sum := by decide
  have hdescent : baseEnd_647694 < baseStart_647694 := by decide
  rcases family_descends (prefixWord ++ tailWord_647694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647704 : List Nat := [2, 1, 2, 3, 3, 2, 3, 1, 3]
def baseStart_647704 : Nat := 118140960795 + 647704 * 2 ^ 59
def prefixEnd_647704 : Nat := 4983230072969 + 3 ^ 40 * 647704 * 2
def baseEnd_647704 : Nat := 295629754524301412285573

theorem tailTrace_647704 : CollatzResearch.WordTrace tailWord_647704 prefixEnd_647704 295629754524301412285573 := by
  unfold tailWord_647704
  simp only [CollatzResearch.WordTrace]
  refine ⟨11811852822743250940739083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15749137096991001254318777 11811852822743250940739083)
  ·
    refine ⟨17717779234114876411108625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11811852822743250940739083 17717779234114876411108625)
    ·
      refine ⟨13288334425586157308331469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17717779234114876411108625 13288334425586157308331469)
      ·
        refine ⟨4983125409594808990624301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13288334425586157308331469 4983125409594808990624301)
        ·
          refine ⟨1868672028598053371484113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4983125409594808990624301 1868672028598053371484113)
          ·
            refine ⟨1401504021448540028613085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1868672028598053371484113 1401504021448540028613085)
            ·
              refine ⟨525564008043202510729907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1401504021448540028613085 525564008043202510729907)
              ·
                refine ⟨788346012064803766094861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525564008043202510729907 788346012064803766094861)
                ·
                  refine ⟨295629754524301412285573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788346012064803766094861 295629754524301412285573)
                  ·
                    rfl

theorem cell20_647704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_647704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647704 prefixEnd_647704 := by exact prefixLift 647704
  have htrace : WordTrace (prefixWord ++ tailWord_647704) baseStart_647704 baseEnd_647704 := by
    simpa [prefixWord, tailWord_647704, baseEnd_647704] using wordTrace_append hprefix tailTrace_647704
  have hstable : (prefixWord ++ tailWord_647704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647704).length < 2 ^ (prefixWord ++ tailWord_647704).sum := by decide
  have hdescent : baseEnd_647704 < baseStart_647704 := by decide
  rcases family_descends (prefixWord ++ tailWord_647704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647801 : List Nat := [1, 2, 1, 3, 3, 3, 2, 2, 3]
def baseStart_647801 : Nat := 118140960795 + 647801 * 2 ^ 59
def prefixEnd_647801 : Nat := 4983230072969 + 3 ^ 40 * 647801 * 2
def baseEnd_647801 : Nat := 295674027967400186051843

theorem tailTrace_647801 : CollatzResearch.WordTrace tailWord_647801 prefixEnd_647801 295674027967400186051843 := by
  unfold tailWord_647801
  simp only [CollatzResearch.WordTrace]
  refine ⟨23627243526135087447759257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15751495684090058298506171 23627243526135087447759257)
  ·
    refine ⟨17720432644601315585819443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23627243526135087447759257 17720432644601315585819443)
    ·
      refine ⟨26580648966901973378729165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17720432644601315585819443 26580648966901973378729165)
      ·
        refine ⟨9967743362588240017023437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26580648966901973378729165 9967743362588240017023437)
        ·
          refine ⟨3737903760970590006383789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9967743362588240017023437 3737903760970590006383789)
          ·
            refine ⟨1401713910363971252393921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3737903760970590006383789 1401713910363971252393921)
            ·
              refine ⟨1051285432772978439295441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1401713910363971252393921 1051285432772978439295441)
              ·
                refine ⟨788464074579733829471581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051285432772978439295441 788464074579733829471581)
                ·
                  refine ⟨295674027967400186051843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788464074579733829471581 295674027967400186051843)
                  ·
                    rfl

theorem cell20_647801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_647801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647801 prefixEnd_647801 := by exact prefixLift 647801
  have htrace : WordTrace (prefixWord ++ tailWord_647801) baseStart_647801 baseEnd_647801 := by
    simpa [prefixWord, tailWord_647801, baseEnd_647801] using wordTrace_append hprefix tailTrace_647801
  have hstable : (prefixWord ++ tailWord_647801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647801).length < 2 ^ (prefixWord ++ tailWord_647801).sum := by decide
  have hdescent : baseEnd_647801 < baseStart_647801 := by decide
  rcases family_descends (prefixWord ++ tailWord_647801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647853 : List Nat := [1, 5, 2, 1, 1, 3, 7]
def baseStart_647853 : Nat := 118140960795 + 647853 * 2 ^ 59
def prefixEnd_647853 : Nat := 4983230072969 + 3 ^ 40 * 647853 * 2
def baseEnd_647853 : Nat := 32855306909368790702033

theorem tailTrace_647853 : CollatzResearch.WordTrace tailWord_647853 prefixEnd_647853 32855306909368790702033 := by
  unfold tailWord_647853
  simp only [CollatzResearch.WordTrace]
  refine ⟨23629140121946700328652213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15752760081297800219101475 23629140121946700328652213)
  ·
    refine ⟨2215231886432503155811145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23629140121946700328652213 2215231886432503155811145)
    ·
      refine ⟨1661423914824377366858359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2215231886432503155811145 1661423914824377366858359)
      ·
        refine ⟨2492135872236566050287539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661423914824377366858359 2492135872236566050287539)
        ·
          refine ⟨3738203808354849075431309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492135872236566050287539 3738203808354849075431309)
          ·
            refine ⟨1401826428133068403286741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3738203808354849075431309 1401826428133068403286741)
            ·
              refine ⟨32855306909368790702033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1401826428133068403286741 32855306909368790702033)
              ·
                rfl

theorem cell20_647853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 7].length) (baseStart_647853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647853 prefixEnd_647853 := by exact prefixLift 647853
  have htrace : WordTrace (prefixWord ++ tailWord_647853) baseStart_647853 baseEnd_647853 := by
    simpa [prefixWord, tailWord_647853, baseEnd_647853] using wordTrace_append hprefix tailTrace_647853
  have hstable : (prefixWord ++ tailWord_647853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647853).length < 2 ^ (prefixWord ++ tailWord_647853).sum := by decide
  have hdescent : baseEnd_647853 < baseStart_647853 := by decide
  rcases family_descends (prefixWord ++ tailWord_647853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647884 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_647884 : Nat := 118140960795 + 647884 * 2 ^ 59
def prefixEnd_647884 : Nat := 4983230072969 + 3 ^ 40 * 647884 * 2
def baseEnd_647884 : Nat := 295711911429020786284837

theorem tailTrace_647884 : CollatzResearch.WordTrace tailWord_647884 prefixEnd_647884 295711911429020786284837 := by
  unfold tailWord_647884
  simp only [CollatzResearch.WordTrace]
  refine ⟨11815135392417196311515353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15753513856556261748687137 11815135392417196311515353)
  ·
    refine ⟨8861351544312897233636515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11815135392417196311515353 8861351544312897233636515)
    ·
      refine ⟨13292027316469345850454773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8861351544312897233636515 13292027316469345850454773)
      ·
        refine ⟨1246127560919001173480135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13292027316469345850454773 1246127560919001173480135)
        ·
          refine ⟨1869191341378501760220203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246127560919001173480135 1869191341378501760220203)
          ·
            refine ⟨2803787012067752640330305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869191341378501760220203 2803787012067752640330305)
            ·
              refine ⟨2102840259050814480247729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2803787012067752640330305 2102840259050814480247729)
              ·
                refine ⟨1577130194288110860185797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2102840259050814480247729 1577130194288110860185797)
                ·
                  refine ⟨295711911429020786284837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577130194288110860185797 295711911429020786284837)
                  ·
                    rfl

theorem cell20_647884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_647884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647884 prefixEnd_647884 := by exact prefixLift 647884
  have htrace : WordTrace (prefixWord ++ tailWord_647884) baseStart_647884 baseEnd_647884 := by
    simpa [prefixWord, tailWord_647884, baseEnd_647884] using wordTrace_append hprefix tailTrace_647884
  have hstable : (prefixWord ++ tailWord_647884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647884).length < 2 ^ (prefixWord ++ tailWord_647884).sum := by decide
  have hdescent : baseEnd_647884 < baseStart_647884 := by decide
  rcases family_descends (prefixWord ++ tailWord_647884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647918 : List Nat := [4, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_647918 : Nat := 118140960795 + 647918 * 2 ^ 59
def prefixEnd_647918 : Nat := 4983230072969 + 3 ^ 40 * 647918 * 2
def baseEnd_647918 : Nat := 295727429955467779151365

theorem tailTrace_647918 : CollatzResearch.WordTrace tailWord_647918 prefixEnd_647918 295727429955467779151365 := by
  unfold tailWord_647918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2953938858338902053721051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15754340577807477619845605 2953938858338902053721051)
  ·
    refine ⟨4430908287508353080581577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2953938858338902053721051 4430908287508353080581577)
    ·
      refine ⟨3323181215631264810436183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4430908287508353080581577 3323181215631264810436183)
      ·
        refine ⟨4984771823446897215654275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3323181215631264810436183 4984771823446897215654275)
        ·
          refine ⟨7477157735170345823481413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4984771823446897215654275 7477157735170345823481413)
          ·
            refine ⟨1401967075344439841902765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7477157735170345823481413 1401967075344439841902765)
            ·
              refine ⟨525737653254164940713537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1401967075344439841902765 525737653254164940713537)
              ·
                refine ⟨394303239940623705535153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525737653254164940713537 394303239940623705535153)
                ·
                  refine ⟨295727429955467779151365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394303239940623705535153 295727429955467779151365)
                  ·
                    rfl

theorem cell20_647918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_647918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647918 prefixEnd_647918 := by exact prefixLift 647918
  have htrace : WordTrace (prefixWord ++ tailWord_647918) baseStart_647918 baseEnd_647918 := by
    simpa [prefixWord, tailWord_647918, baseEnd_647918] using wordTrace_append hprefix tailTrace_647918
  have hstable : (prefixWord ++ tailWord_647918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647918).length < 2 ^ (prefixWord ++ tailWord_647918).sum := by decide
  have hdescent : baseEnd_647918 < baseStart_647918 := by decide
  rcases family_descends (prefixWord ++ tailWord_647918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647922 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_647922 : Nat := 118140960795 + 647922 * 2 ^ 59
def prefixEnd_647922 : Nat := 4983230072969 + 3 ^ 40 * 647922 * 2
def baseEnd_647922 : Nat := 295729255664461543018015

theorem tailTrace_647922 : CollatzResearch.WordTrace tailWord_647922 prefixEnd_647922 295729255664461543018015 := by
  unfold tailWord_647922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5907914189674181278228505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15754437839131150075276013 5907914189674181278228505)
  ·
    refine ⟨4430935642255635958671379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5907914189674181278228505 4430935642255635958671379)
    ·
      refine ⟨6646403463383453938007069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4430935642255635958671379 6646403463383453938007069)
      ·
        refine ⟨2492401298768795226752651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6646403463383453938007069 2492401298768795226752651)
        ·
          refine ⟨3738601948153192840128977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492401298768795226752651 3738601948153192840128977)
          ·
            refine ⟨2803951461114894630096733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3738601948153192840128977 2803951461114894630096733)
            ·
              refine ⟨1051481797918085486286275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2803951461114894630096733 1051481797918085486286275)
              ·
                refine ⟨1577222696877128229429413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051481797918085486286275 1577222696877128229429413)
                ·
                  refine ⟨295729255664461543018015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577222696877128229429413 295729255664461543018015)
                  ·
                    rfl

theorem cell20_647922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_647922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647922 prefixEnd_647922 := by exact prefixLift 647922
  have htrace : WordTrace (prefixWord ++ tailWord_647922) baseStart_647922 baseEnd_647922 := by
    simpa [prefixWord, tailWord_647922, baseEnd_647922] using wordTrace_append hprefix tailTrace_647922
  have hstable : (prefixWord ++ tailWord_647922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647922).length < 2 ^ (prefixWord ++ tailWord_647922).sum := by decide
  have hdescent : baseEnd_647922 < baseStart_647922 := by decide
  rcases family_descends (prefixWord ++ tailWord_647922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647932 : List Nat := [2, 2, 2, 1, 3, 4, 2, 1, 3]
def baseStart_647932 : Nat := 118140960795 + 647932 * 2 ^ 59
def prefixEnd_647932 : Nat := 4983230072969 + 3 ^ 40 * 647932 * 2
def baseEnd_647932 : Nat := 295733819936945952684641

theorem tailTrace_647932 : CollatzResearch.WordTrace tailWord_647932 prefixEnd_647932 295733819936945952684641 := by
  unfold tailWord_647932
  simp only [CollatzResearch.WordTrace]
  refine ⟨11816010744330248410389025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15754680992440331213852033 11816010744330248410389025)
  ·
    refine ⟨8862008058247686307791769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11816010744330248410389025 8862008058247686307791769)
    ·
      refine ⟨6646506043685764730843827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8862008058247686307791769 6646506043685764730843827)
      ·
        refine ⟨9969759065528647096265741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6646506043685764730843827 9969759065528647096265741)
        ·
          refine ⟨3738659649573242661099653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9969759065528647096265741 3738659649573242661099653)
          ·
            refine ⟨700998684294982998956185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3738659649573242661099653 700998684294982998956185)
            ·
              refine ⟨525749013221237249217139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700998684294982998956185 525749013221237249217139)
              ·
                refine ⟨788623519831855873825709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525749013221237249217139 788623519831855873825709)
                ·
                  refine ⟨295733819936945952684641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788623519831855873825709 295733819936945952684641)
                  ·
                    rfl

theorem cell20_647932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_647932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647932 prefixEnd_647932 := by exact prefixLift 647932
  have htrace : WordTrace (prefixWord ++ tailWord_647932) baseStart_647932 baseEnd_647932 := by
    simpa [prefixWord, tailWord_647932, baseEnd_647932] using wordTrace_append hprefix tailTrace_647932
  have hstable : (prefixWord ++ tailWord_647932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647932).length < 2 ^ (prefixWord ++ tailWord_647932).sum := by decide
  have hdescent : baseEnd_647932 < baseStart_647932 := by decide
  rcases family_descends (prefixWord ++ tailWord_647932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647960 : List Nat := [2, 1, 2, 3, 1, 1, 1, 7, 2]
def baseStart_647960 : Nat := 118140960795 + 647960 * 2 ^ 59
def prefixEnd_647960 : Nat := 4983230072969 + 3 ^ 40 * 647960 * 2
def baseEnd_647960 : Nat := 295746599899902299751193

theorem tailTrace_647960 : CollatzResearch.WordTrace tailWord_647960 prefixEnd_647960 295746599899902299751193 := by
  unfold tailWord_647960
  simp only [CollatzResearch.WordTrace]
  refine ⟨11816521366279528801398667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15755361821706038401864889 11816521366279528801398667)
  ·
    refine ⟨17724782049419293202098001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11816521366279528801398667 17724782049419293202098001)
    ·
      refine ⟨13293586537064469901573501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17724782049419293202098001 13293586537064469901573501)
      ·
        refine ⟨4985094951399176213090063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13293586537064469901573501 4985094951399176213090063)
        ·
          refine ⟨7477642427098764319635095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4985094951399176213090063 7477642427098764319635095)
          ·
            refine ⟨11216463640648146479452643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7477642427098764319635095 11216463640648146479452643)
            ·
              refine ⟨16824695460972219719178965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11216463640648146479452643 16824695460972219719178965)
              ·
                refine ⟨394328799866536399668257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16824695460972219719178965 394328799866536399668257)
                ·
                  refine ⟨295746599899902299751193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394328799866536399668257 295746599899902299751193)
                  ·
                    rfl

theorem cell20_647960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 2].length) (baseStart_647960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_647960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_647960 prefixEnd_647960 := by exact prefixLift 647960
  have htrace : WordTrace (prefixWord ++ tailWord_647960) baseStart_647960 baseEnd_647960 := by
    simpa [prefixWord, tailWord_647960, baseEnd_647960] using wordTrace_append hprefix tailTrace_647960
  have hstable : (prefixWord ++ tailWord_647960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647960).length < 2 ^ (prefixWord ++ tailWord_647960).sum := by decide
  have hdescent : baseEnd_647960 < baseStart_647960 := by decide
  rcases family_descends (prefixWord ++ tailWord_647960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648001 : List Nat := [1, 2, 5, 3, 1, 1, 3, 4]
def baseStart_648001 : Nat := 118140960795 + 648001 * 2 ^ 59
def prefixEnd_648001 : Nat := 4983230072969 + 3 ^ 40 * 648001 * 2
def baseEnd_648001 : Nat := 98588437805696126461453

theorem tailTrace_648001 : CollatzResearch.WordTrace tailWord_648001 prefixEnd_648001 98588437805696126461453 := by
  unfold tailWord_648001
  simp only [CollatzResearch.WordTrace]
  refine ⟨23634538125410521605039857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15756358750273681070026571 23634538125410521605039857)
  ·
    refine ⟨17725903594057891203779893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23634538125410521605039857 17725903594057891203779893)
    ·
      refine ⟨1661803461942927300354365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17725903594057891203779893 1661803461942927300354365)
      ·
        refine ⟨623176298228597737632887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1661803461942927300354365 623176298228597737632887)
        ·
          refine ⟨934764447342896606449331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623176298228597737632887 934764447342896606449331)
          ·
            refine ⟨1402146671014344909673997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934764447342896606449331 1402146671014344909673997)
            ·
              refine ⟨525805001630379341127749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1402146671014344909673997 525805001630379341127749)
              ·
                refine ⟨98588437805696126461453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 525805001630379341127749 98588437805696126461453)
                ·
                  rfl

theorem cell20_648001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 4].length) (baseStart_648001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648001 prefixEnd_648001 := by exact prefixLift 648001
  have htrace : WordTrace (prefixWord ++ tailWord_648001) baseStart_648001 baseEnd_648001 := by
    simpa [prefixWord, tailWord_648001, baseEnd_648001] using wordTrace_append hprefix tailTrace_648001
  have hstable : (prefixWord ++ tailWord_648001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648001).length < 2 ^ (prefixWord ++ tailWord_648001).sum := by decide
  have hdescent : baseEnd_648001 < baseStart_648001 := by decide
  rcases family_descends (prefixWord ++ tailWord_648001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648026 : List Nat := [3, 1, 1, 2, 1, 5, 7]
def baseStart_648026 : Nat := 118140960795 + 648026 * 2 ^ 59
def prefixEnd_648026 : Nat := 4983230072969 + 3 ^ 40 * 648026 * 2
def baseEnd_648026 : Nat := 32864080455366600394547

theorem tailTrace_648026 : CollatzResearch.WordTrace tailWord_648026 prefixEnd_648026 32864080455366600394547 := by
  unfold tailWord_648026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5908862487579987718674983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15756966633546633916466621 5908862487579987718674983)
  ·
    refine ⟨8863293731369981578012475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5908862487579987718674983 8863293731369981578012475)
    ·
      refine ⟨13294940597054972367018713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8863293731369981578012475 13294940597054972367018713)
      ·
        refine ⟨9971205447791229275264035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13294940597054972367018713 9971205447791229275264035)
        ·
          refine ⟨14956808171686843912896053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9971205447791229275264035 14956808171686843912896053)
          ·
            refine ⟨1402200766095641616834005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14956808171686843912896053 1402200766095641616834005)
            ·
              refine ⟨32864080455366600394547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1402200766095641616834005 32864080455366600394547)
              ·
                rfl

theorem cell20_648026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 7].length) (baseStart_648026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648026 prefixEnd_648026 := by exact prefixLift 648026
  have htrace : WordTrace (prefixWord ++ tailWord_648026) baseStart_648026 baseEnd_648026 := by
    simpa [prefixWord, tailWord_648026, baseEnd_648026] using wordTrace_append hprefix tailTrace_648026
  have hstable : (prefixWord ++ tailWord_648026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648026).length < 2 ^ (prefixWord ++ tailWord_648026).sum := by decide
  have hdescent : baseEnd_648026 < baseStart_648026 := by decide
  rcases family_descends (prefixWord ++ tailWord_648026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648036 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_648036 : Nat := 118140960795 + 648036 * 2 ^ 59
def prefixEnd_648036 : Nat := 4983230072969 + 3 ^ 40 * 648036 * 2
def baseEnd_648036 : Nat := 295781288370783813217549

theorem tailTrace_648036 : CollatzResearch.WordTrace tailWord_648036 prefixEnd_648036 295781288370783813217549 := by
  unfold tailWord_648036
  simp only [CollatzResearch.WordTrace]
  refine ⟨11817907340141861291281981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15757209786855815055042641 11817907340141861291281981)
  ·
    refine ⟨4431715252553197984230743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11817907340141861291281981 4431715252553197984230743)
    ·
      refine ⟨6647572878829796976346115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4431715252553197984230743 6647572878829796976346115)
      ·
        refine ⟨9971359318244695464519173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6647572878829796976346115 9971359318244695464519173)
        ·
          refine ⟨1869629872170880399597345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9971359318244695464519173 1869629872170880399597345)
          ·
            refine ⟨1402222404128160299698009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1869629872170880399597345 1402222404128160299698009)
            ·
              refine ⟨1051666803096120224773507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402222404128160299698009 1051666803096120224773507)
              ·
                refine ⟨1577500204644180337160261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051666803096120224773507 1577500204644180337160261)
                ·
                  refine ⟨295781288370783813217549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577500204644180337160261 295781288370783813217549)
                  ·
                    rfl

theorem cell20_648036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_648036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648036 prefixEnd_648036 := by exact prefixLift 648036
  have htrace : WordTrace (prefixWord ++ tailWord_648036) baseStart_648036 baseEnd_648036 := by
    simpa [prefixWord, tailWord_648036, baseEnd_648036] using wordTrace_append hprefix tailTrace_648036
  have hstable : (prefixWord ++ tailWord_648036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648036).length < 2 ^ (prefixWord ++ tailWord_648036).sum := by decide
  have hdescent : baseEnd_648036 < baseStart_648036 := by decide
  rcases family_descends (prefixWord ++ tailWord_648036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648050 : List Nat := [3, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_648050 : Nat := 118140960795 + 648050 * 2 ^ 59
def prefixEnd_648050 : Nat := 4983230072969 + 3 ^ 40 * 648050 * 2
def baseEnd_648050 : Nat := 295787678352261986750825

theorem tailTrace_648050 : CollatzResearch.WordTrace tailWord_648050 prefixEnd_648050 295787678352261986750825 := by
  unfold tailWord_648050
  simp only [CollatzResearch.WordTrace]
  refine ⟨5909081325558250743393401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15757550201488668649049069 5909081325558250743393401)
  ·
    refine ⟨4431810994168688057545051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5909081325558250743393401 4431810994168688057545051)
    ·
      refine ⟨6647716491253032086317577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4431810994168688057545051 6647716491253032086317577)
      ·
        refine ⟨4985787368439774064738183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6647716491253032086317577 4985787368439774064738183)
        ·
          refine ⟨7478681052659661097107275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4985787368439774064738183 7478681052659661097107275)
          ·
            refine ⟨11218021578989491645660913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7478681052659661097107275 11218021578989491645660913)
            ·
              refine ⟨8413516184242118734245685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11218021578989491645660913 8413516184242118734245685)
              ·
                refine ⟨788767142272698631335533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8413516184242118734245685 788767142272698631335533)
                ·
                  refine ⟨295787678352261986750825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788767142272698631335533 295787678352261986750825)
                  ·
                    rfl

theorem cell20_648050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_648050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648050 prefixEnd_648050 := by exact prefixLift 648050
  have htrace : WordTrace (prefixWord ++ tailWord_648050) baseStart_648050 baseEnd_648050 := by
    simpa [prefixWord, tailWord_648050, baseEnd_648050] using wordTrace_append hprefix tailTrace_648050
  have hstable : (prefixWord ++ tailWord_648050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648050).length < 2 ^ (prefixWord ++ tailWord_648050).sum := by decide
  have hdescent : baseEnd_648050 < baseStart_648050 := by decide
  rcases family_descends (prefixWord ++ tailWord_648050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648057 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 4]
def baseStart_648057 : Nat := 118140960795 + 648057 * 2 ^ 59
def prefixEnd_648057 : Nat := 4983230072969 + 3 ^ 40 * 648057 * 2
def baseEnd_648057 : Nat := 295790873343001073517463

theorem tailTrace_648057 : CollatzResearch.WordTrace tailWord_648057 prefixEnd_648057 295790873343001073517463 := by
  unfold tailWord_648057
  simp only [CollatzResearch.WordTrace]
  refine ⟨23636580613207643169078425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15757720408805095446052283 23636580613207643169078425)
  ·
    refine ⟨17727435459905732376808819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23636580613207643169078425 17727435459905732376808819)
    ·
      refine ⟨26591153189858598565213229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17727435459905732376808819 26591153189858598565213229)
      ·
        refine ⟨9971682446196974461954961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26591153189858598565213229 9971682446196974461954961)
        ·
          refine ⟨7478761834647730846466221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9971682446196974461954961 7478761834647730846466221)
          ·
            refine ⟨2804535687992899067424833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7478761834647730846466221 2804535687992899067424833)
            ·
              refine ⟨2103401765994674300568625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2804535687992899067424833 2103401765994674300568625)
              ·
                refine ⟨1577551324496005725426469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103401765994674300568625 1577551324496005725426469)
                ·
                  refine ⟨295790873343001073517463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577551324496005725426469 295790873343001073517463)
                  ·
                    rfl

theorem cell20_648057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_648057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648057 prefixEnd_648057 := by exact prefixLift 648057
  have htrace : WordTrace (prefixWord ++ tailWord_648057) baseStart_648057 baseEnd_648057 := by
    simpa [prefixWord, tailWord_648057, baseEnd_648057] using wordTrace_append hprefix tailTrace_648057
  have hstable : (prefixWord ++ tailWord_648057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648057).length < 2 ^ (prefixWord ++ tailWord_648057).sum := by decide
  have hdescent : baseEnd_648057 < baseStart_648057 := by decide
  rcases family_descends (prefixWord ++ tailWord_648057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648066 : List Nat := [3, 4, 2, 2, 1, 2, 1, 3, 2]
def baseStart_648066 : Nat := 118140960795 + 648066 * 2 ^ 59
def prefixEnd_648066 : Nat := 4983230072969 + 3 ^ 40 * 648066 * 2
def baseEnd_648066 : Nat := 295794981188237042217427

theorem tailTrace_648066 : CollatzResearch.WordTrace tailWord_648066 prefixEnd_648066 295794981188237042217427 := by
  unfold tailWord_648066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5909227217543759426539013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15757939246783358470770701 5909227217543759426539013)
  ·
    refine ⟨1107980103289454892476065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5909227217543759426539013 1107980103289454892476065)
    ·
      refine ⟨830985077467091169357049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1107980103289454892476065 830985077467091169357049)
      ·
        refine ⟨623238808100318377017787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 830985077467091169357049 623238808100318377017787)
        ·
          refine ⟨934858212150477565526681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623238808100318377017787 934858212150477565526681)
          ·
            refine ⟨701143659112858174145011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 934858212150477565526681 701143659112858174145011)
            ·
              refine ⟨1051715488669287261217517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701143659112858174145011 1051715488669287261217517)
              ·
                refine ⟨394393308250982722956569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1051715488669287261217517 394393308250982722956569)
                ·
                  refine ⟨295794981188237042217427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394393308250982722956569 295794981188237042217427)
                  ·
                    rfl

theorem cell20_648066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_648066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648066 prefixEnd_648066 := by exact prefixLift 648066
  have htrace : WordTrace (prefixWord ++ tailWord_648066) baseStart_648066 baseEnd_648066 := by
    simpa [prefixWord, tailWord_648066, baseEnd_648066] using wordTrace_append hprefix tailTrace_648066
  have hstable : (prefixWord ++ tailWord_648066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648066).length < 2 ^ (prefixWord ++ tailWord_648066).sum := by decide
  have hdescent : baseEnd_648066 < baseStart_648066 := by decide
  rcases family_descends (prefixWord ++ tailWord_648066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648146 : List Nat := [3, 2, 2, 3, 1, 1, 4, 2, 2]
def baseStart_648146 : Nat := 118140960795 + 648146 * 2 ^ 59
def prefixEnd_648146 : Nat := 4983230072969 + 3 ^ 40 * 648146 * 2
def baseEnd_648146 : Nat := 295831495368112319550433

theorem tailTrace_648146 : CollatzResearch.WordTrace tailWord_648146 prefixEnd_648146 295831495368112319550433 := by
  unfold tailWord_648146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5909956677471302842267073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15759884473256807579378861 5909956677471302842267073)
  ·
    refine ⟨4432467508103477131700305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5909956677471302842267073 4432467508103477131700305)
    ·
      refine ⟨3324350631077607848775229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4432467508103477131700305 3324350631077607848775229)
      ·
        refine ⟨1246631486654102943290711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3324350631077607848775229 1246631486654102943290711)
        ·
          refine ⟨1869947229981154414936067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246631486654102943290711 1869947229981154414936067)
          ·
            refine ⟨2804920844971731622404101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869947229981154414936067 2804920844971731622404101)
            ·
              refine ⟨525922658432199679200769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2804920844971731622404101 525922658432199679200769)
              ·
                refine ⟨394441993824149759400577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525922658432199679200769 394441993824149759400577)
                ·
                  refine ⟨295831495368112319550433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394441993824149759400577 295831495368112319550433)
                  ·
                    rfl

theorem cell20_648146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_648146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648146 prefixEnd_648146 := by exact prefixLift 648146
  have htrace : WordTrace (prefixWord ++ tailWord_648146) baseStart_648146 baseEnd_648146 := by
    simpa [prefixWord, tailWord_648146, baseEnd_648146] using wordTrace_append hprefix tailTrace_648146
  have hstable : (prefixWord ++ tailWord_648146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648146).length < 2 ^ (prefixWord ++ tailWord_648146).sum := by decide
  have hdescent : baseEnd_648146 < baseStart_648146 := by decide
  rcases family_descends (prefixWord ++ tailWord_648146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648157 : List Nat := [1, 4, 3, 1, 2, 1, 3, 5]
def baseStart_648157 : Nat := 118140960795 + 648157 * 2 ^ 59
def prefixEnd_648157 : Nat := 4983230072969 + 3 ^ 40 * 648157 * 2
def baseEnd_648157 : Nat := 98612172022615056727907

theorem tailTrace_648157 : CollatzResearch.WordTrace tailWord_648157 prefixEnd_648157 98612172022615056727907 := by
  unfold tailWord_648157
  simp only [CollatzResearch.WordTrace]
  refine ⟨23640227912845360247718725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15760151941896906831812483 23640227912845360247718725)
  ·
    refine ⟨4432542733658505046447261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23640227912845360247718725 4432542733658505046447261)
    ·
      refine ⟨1662203525121939392417723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4432542733658505046447261 1662203525121939392417723)
      ·
        refine ⟨2493305287682909088626585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1662203525121939392417723 2493305287682909088626585)
        ·
          refine ⟨1869978965762181816469939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2493305287682909088626585 1869978965762181816469939)
          ·
            refine ⟨2804968448643272724704909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869978965762181816469939 2804968448643272724704909)
            ·
              refine ⟨1051863168241227271764341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2804968448643272724704909 1051863168241227271764341)
              ·
                refine ⟨98612172022615056727907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1051863168241227271764341 98612172022615056727907)
                ·
                  rfl

theorem cell20_648157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_648157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648157 prefixEnd_648157 := by exact prefixLift 648157
  have htrace : WordTrace (prefixWord ++ tailWord_648157) baseStart_648157 baseEnd_648157 := by
    simpa [prefixWord, tailWord_648157, baseEnd_648157] using wordTrace_append hprefix tailTrace_648157
  have hstable : (prefixWord ++ tailWord_648157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648157).length < 2 ^ (prefixWord ++ tailWord_648157).sum := by decide
  have hdescent : baseEnd_648157 < baseStart_648157 := by decide
  rcases family_descends (prefixWord ++ tailWord_648157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648174 : List Nat := [4, 1, 2, 1, 4, 1, 3, 4]
def baseStart_648174 : Nat := 118140960795 + 648174 * 2 ^ 59
def prefixEnd_648174 : Nat := 4983230072969 + 3 ^ 40 * 648174 * 2
def baseEnd_648174 : Nat := 98614758443689555538995

theorem tailTrace_648174 : CollatzResearch.WordTrace tailWord_648174 prefixEnd_648174 98614758443689555538995 := by
  unfold tailWord_648174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955105994222971518885947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15760565302522514767391717 2955105994222971518885947)
  ·
    refine ⟨4432658991334457278328921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2955105994222971518885947 4432658991334457278328921)
    ·
      refine ⟨3324494243500842958746691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4432658991334457278328921 3324494243500842958746691)
      ·
        refine ⟨4986741365251264438120037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3324494243500842958746691 4986741365251264438120037)
        ·
          refine ⟨935014005984612082147507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4986741365251264438120037 935014005984612082147507)
          ·
            refine ⟨1402521008976918123221261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935014005984612082147507 1402521008976918123221261)
            ·
              refine ⟨525945378366344296207973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1402521008976918123221261 525945378366344296207973)
              ·
                refine ⟨98614758443689555538995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 525945378366344296207973 98614758443689555538995)
                ·
                  rfl

theorem cell20_648174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_648174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648174 prefixEnd_648174 := by exact prefixLift 648174
  have htrace : WordTrace (prefixWord ++ tailWord_648174) baseStart_648174 baseEnd_648174 := by
    simpa [prefixWord, tailWord_648174, baseEnd_648174] using wordTrace_append hprefix tailTrace_648174
  have hstable : (prefixWord ++ tailWord_648174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648174).length < 2 ^ (prefixWord ++ tailWord_648174).sum := by decide
  have hdescent : baseEnd_648174 < baseStart_648174 := by decide
  rcases family_descends (prefixWord ++ tailWord_648174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648185 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 5]
def baseStart_648185 : Nat := 118140960795 + 648185 * 2 ^ 59
def prefixEnd_648185 : Nat := 4983230072969 + 3 ^ 40 * 648185 * 2
def baseEnd_648185 : Nat := 295849296030801517250273

theorem tailTrace_648185 : CollatzResearch.WordTrace tailWord_648185 prefixEnd_648185 295849296030801517250273 := by
  unfold tailWord_648185
  simp only [CollatzResearch.WordTrace]
  refine ⟨23641249156743921029738009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15760832771162614019825339 23641249156743921029738009)
  ·
    refine ⟨17730936867557940772303507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23641249156743921029738009 17730936867557940772303507)
    ·
      refine ⟨26596405301336911158455261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17730936867557940772303507 26596405301336911158455261)
      ·
        refine ⟨9973651988001341684420723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26596405301336911158455261 9973651988001341684420723)
        ·
          refine ⟨14960477982002012526631085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9973651988001341684420723 14960477982002012526631085)
          ·
            refine ⟨5610179243250754697486657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14960477982002012526631085 5610179243250754697486657)
            ·
              refine ⟨4207634432438066023114993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5610179243250754697486657 4207634432438066023114993)
              ·
                refine ⟨3155725824328549517336245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4207634432438066023114993 3155725824328549517336245)
                ·
                  refine ⟨295849296030801517250273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3155725824328549517336245 295849296030801517250273)
                  ·
                    rfl

theorem cell20_648185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_648185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648185 prefixEnd_648185 := by exact prefixLift 648185
  have htrace : WordTrace (prefixWord ++ tailWord_648185) baseStart_648185 baseEnd_648185 := by
    simpa [prefixWord, tailWord_648185, baseEnd_648185] using wordTrace_append hprefix tailTrace_648185
  have hstable : (prefixWord ++ tailWord_648185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648185).length < 2 ^ (prefixWord ++ tailWord_648185).sum := by decide
  have hdescent : baseEnd_648185 < baseStart_648185 := by decide
  rcases family_descends (prefixWord ++ tailWord_648185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648188 : List Nat := [2, 2, 2, 1, 2, 3, 1, 5, 2]
def baseStart_648188 : Nat := 118140960795 + 648188 * 2 ^ 59
def prefixEnd_648188 : Nat := 4983230072969 + 3 ^ 40 * 648188 * 2
def baseEnd_648188 : Nat := 295850665312546840150261

theorem tailTrace_648188 : CollatzResearch.WordTrace tailWord_648188 prefixEnd_648188 295850665312546840150261 := by
  unfold tailWord_648188
  simp only [CollatzResearch.WordTrace]
  refine ⟨11820679287866526271048609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15760905717155368361398145 11820679287866526271048609)
  ·
    refine ⟨8865509465899894703286457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11820679287866526271048609 8865509465899894703286457)
    ·
      refine ⟨6649132099424921027464843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8865509465899894703286457 6649132099424921027464843)
      ·
        refine ⟨9973698149137381541197265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6649132099424921027464843 9973698149137381541197265)
        ·
          refine ⟨7480273611853036155897949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9973698149137381541197265 7480273611853036155897949)
          ·
            refine ⟨2805102604444888558461731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7480273611853036155897949 2805102604444888558461731)
            ·
              refine ⟨4207653906667332837692597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2805102604444888558461731 4207653906667332837692597)
              ·
                refine ⟨394467553750062453533681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4207653906667332837692597 394467553750062453533681)
                ·
                  refine ⟨295850665312546840150261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394467553750062453533681 295850665312546840150261)
                  ·
                    rfl

theorem cell20_648188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_648188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648188 prefixEnd_648188 := by exact prefixLift 648188
  have htrace : WordTrace (prefixWord ++ tailWord_648188) baseStart_648188 baseEnd_648188 := by
    simpa [prefixWord, tailWord_648188, baseEnd_648188] using wordTrace_append hprefix tailTrace_648188
  have hstable : (prefixWord ++ tailWord_648188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648188).length < 2 ^ (prefixWord ++ tailWord_648188).sum := by decide
  have hdescent : baseEnd_648188 < baseStart_648188 := by decide
  rcases family_descends (prefixWord ++ tailWord_648188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648194 : List Nat := [3, 4, 1, 3, 2, 1, 1, 2, 3]
def baseStart_648194 : Nat := 118140960795 + 648194 * 2 ^ 59
def prefixEnd_648194 : Nat := 4983230072969 + 3 ^ 40 * 648194 * 2
def baseEnd_648194 : Nat := 295853403876037485950237

theorem tailTrace_648194 : CollatzResearch.WordTrace tailWord_648194 prefixEnd_648194 295853403876037485950237 := by
  unfold tailWord_648194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5910394353427828891703909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15761051609140877044543757 5910394353427828891703909)
  ·
    refine ⟨1108198941267717917194483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5910394353427828891703909 1108198941267717917194483)
    ·
      refine ⟨1662298411901576875791725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1108198941267717917194483 1662298411901576875791725)
      ·
        refine ⟨623361904463091328421897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1662298411901576875791725 623361904463091328421897)
        ·
          refine ⟨467521428347318496316423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623361904463091328421897 467521428347318496316423)
          ·
            refine ⟨701282142520977744474635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467521428347318496316423 701282142520977744474635)
            ·
              refine ⟨1051923213781466616711953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701282142520977744474635 1051923213781466616711953)
              ·
                refine ⟨788942410336099962533965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051923213781466616711953 788942410336099962533965)
                ·
                  refine ⟨295853403876037485950237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788942410336099962533965 295853403876037485950237)
                  ·
                    rfl

theorem cell20_648194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_648194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648194 prefixEnd_648194 := by exact prefixLift 648194
  have htrace : WordTrace (prefixWord ++ tailWord_648194) baseStart_648194 baseEnd_648194 := by
    simpa [prefixWord, tailWord_648194, baseEnd_648194] using wordTrace_append hprefix tailTrace_648194
  have hstable : (prefixWord ++ tailWord_648194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648194).length < 2 ^ (prefixWord ++ tailWord_648194).sum := by decide
  have hdescent : baseEnd_648194 < baseStart_648194 := by decide
  rcases family_descends (prefixWord ++ tailWord_648194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648202 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_648202 : Nat := 118140960795 + 648202 * 2 ^ 59
def prefixEnd_648202 : Nat := 4983230072969 + 3 ^ 40 * 648202 * 2
def baseEnd_648202 : Nat := 295857055294025013683537

theorem tailTrace_648202 : CollatzResearch.WordTrace tailWord_648202 prefixEnd_648202 295857055294025013683537 := by
  unfold tailWord_648202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5910467299420583233276715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15761246131788221955404573 5910467299420583233276715)
  ·
    refine ⟨8865700949130874849915073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5910467299420583233276715 8865700949130874849915073)
    ·
      refine ⟨6649275711848156137436305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8865700949130874849915073 6649275711848156137436305)
      ·
        refine ⟨4986956783886117103077229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6649275711848156137436305 4986956783886117103077229)
        ·
          refine ⟨1870108793957293913653961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4986956783886117103077229 1870108793957293913653961)
          ·
            refine ⟨1402581595467970435240471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1870108793957293913653961 1402581595467970435240471)
            ·
              refine ⟨2103872393201955652860707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402581595467970435240471 2103872393201955652860707)
              ·
                refine ⟨3155808589802933479291061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103872393201955652860707 3155808589802933479291061)
                ·
                  refine ⟨295857055294025013683537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3155808589802933479291061 295857055294025013683537)
                  ·
                    rfl

theorem cell20_648202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_648202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648202 prefixEnd_648202 := by exact prefixLift 648202
  have htrace : WordTrace (prefixWord ++ tailWord_648202) baseStart_648202 baseEnd_648202 := by
    simpa [prefixWord, tailWord_648202, baseEnd_648202] using wordTrace_append hprefix tailTrace_648202
  have hstable : (prefixWord ++ tailWord_648202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648202).length < 2 ^ (prefixWord ++ tailWord_648202).sum := by decide
  have hdescent : baseEnd_648202 < baseStart_648202 := by decide
  rcases family_descends (prefixWord ++ tailWord_648202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648261 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 5]
def baseStart_648261 : Nat := 118140960795 + 648261 * 2 ^ 59
def prefixEnd_648261 : Nat := 4983230072969 + 3 ^ 40 * 648261 * 2
def baseEnd_648261 : Nat := 295883984501683030716629

theorem tailTrace_648261 : CollatzResearch.WordTrace tailWord_648261 prefixEnd_648261 295883984501683030716629 := by
  unfold tailWord_648261
  simp only [CollatzResearch.WordTrace]
  refine ⟨23644021104468586009504637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15762680736312390673003091 23644021104468586009504637)
  ·
    refine ⟨8866507914175719753564239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23644021104468586009504637 8866507914175719753564239)
    ·
      refine ⟨13299761871263579630346359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8866507914175719753564239 13299761871263579630346359)
      ·
        refine ⟨19949642806895369445519539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13299761871263579630346359 19949642806895369445519539)
        ·
          refine ⟨29924464210343054168279309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19949642806895369445519539 29924464210343054168279309)
          ·
            refine ⟨11221674078878645313104741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29924464210343054168279309 11221674078878645313104741)
            ·
              refine ⟨2104063889789745996207139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11221674078878645313104741 2104063889789745996207139)
              ·
                refine ⟨3156095834684618994310709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104063889789745996207139 3156095834684618994310709)
                ·
                  refine ⟨295883984501683030716629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3156095834684618994310709 295883984501683030716629)
                  ·
                    rfl

theorem cell20_648261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_648261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648261 prefixEnd_648261 := by exact prefixLift 648261
  have htrace : WordTrace (prefixWord ++ tailWord_648261) baseStart_648261 baseEnd_648261 := by
    simpa [prefixWord, tailWord_648261, baseEnd_648261] using wordTrace_append hprefix tailTrace_648261
  have hstable : (prefixWord ++ tailWord_648261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648261).length < 2 ^ (prefixWord ++ tailWord_648261).sum := by decide
  have hdescent : baseEnd_648261 < baseStart_648261 := by decide
  rcases family_descends (prefixWord ++ tailWord_648261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648274 : List Nat := [3, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_648274 : Nat := 118140960795 + 648274 * 2 ^ 59
def prefixEnd_648274 : Nat := 4983230072969 + 3 ^ 40 * 648274 * 2
def baseEnd_648274 : Nat := 295889918055912763283243

theorem tailTrace_648274 : CollatzResearch.WordTrace tailWord_648274 prefixEnd_648274 295889918055912763283243 := by
  unfold tailWord_648274
  simp only [CollatzResearch.WordTrace]
  refine ⟨5911123813355372307431969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15762996835614326153151917 5911123813355372307431969)
  ·
    refine ⟨4433342860016529230573977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5911123813355372307431969 4433342860016529230573977)
    ·
      refine ⟨3325007145012396922930483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4433342860016529230573977 3325007145012396922930483)
      ·
        refine ⟨4987510717518595384395725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3325007145012396922930483 4987510717518595384395725)
        ·
          refine ⟨1870316519069473269148397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4987510717518595384395725 1870316519069473269148397)
          ·
            refine ⟨701368694651052475930649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1870316519069473269148397 701368694651052475930649)
            ·
              refine ⟨526026520988289356947987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701368694651052475930649 526026520988289356947987)
              ·
                refine ⟨789039781482434035421981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526026520988289356947987 789039781482434035421981)
                ·
                  refine ⟨295889918055912763283243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789039781482434035421981 295889918055912763283243)
                  ·
                    rfl

theorem cell20_648274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_648274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648274 prefixEnd_648274 := by exact prefixLift 648274
  have htrace : WordTrace (prefixWord ++ tailWord_648274) baseStart_648274 baseEnd_648274 := by
    simpa [prefixWord, tailWord_648274, baseEnd_648274] using wordTrace_append hprefix tailTrace_648274
  have hstable : (prefixWord ++ tailWord_648274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648274).length < 2 ^ (prefixWord ++ tailWord_648274).sum := by decide
  have hdescent : baseEnd_648274 < baseStart_648274 := by decide
  rcases family_descends (prefixWord ++ tailWord_648274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648275 : List Nat := [1, 1, 1, 2, 1, 1, 2, 11]
def baseStart_648275 : Nat := 118140960795 + 648275 * 2 ^ 59
def prefixEnd_648275 : Nat := 4983230072969 + 3 ^ 40 * 648275 * 2
def baseEnd_648275 : Nat := 98630124827720401416635

theorem tailTrace_648275 : CollatzResearch.WordTrace tailWord_648275 prefixEnd_648275 98630124827720401416635 := by
  unfold tailWord_648275
  simp only [CollatzResearch.WordTrace]
  refine ⟨23644531726417866400514279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15763021150945244267009519 23644531726417866400514279)
  ·
    refine ⟨35466797589626799600771419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23644531726417866400514279 35466797589626799600771419)
    ·
      refine ⟨53200196384440199401157129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35466797589626799600771419 53200196384440199401157129)
      ·
        refine ⟨39900147288330149550867847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53200196384440199401157129 39900147288330149550867847)
        ·
          refine ⟨59850220932495224326301771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39900147288330149550867847 59850220932495224326301771)
          ·
            refine ⟨89775331398742836489452657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59850220932495224326301771 89775331398742836489452657)
            ·
              refine ⟨67331498549057127367089493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89775331398742836489452657 67331498549057127367089493)
              ·
                refine ⟨98630124827720401416635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 67331498549057127367089493 98630124827720401416635)
                ·
                  rfl

theorem cell20_648275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_648275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648275 prefixEnd_648275 := by exact prefixLift 648275
  have htrace : WordTrace (prefixWord ++ tailWord_648275) baseStart_648275 baseEnd_648275 := by
    simpa [prefixWord, tailWord_648275, baseEnd_648275] using wordTrace_append hprefix tailTrace_648275
  have hstable : (prefixWord ++ tailWord_648275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648275).length < 2 ^ (prefixWord ++ tailWord_648275).sum := by decide
  have hdescent : baseEnd_648275 < baseStart_648275 := by decide
  rcases family_descends (prefixWord ++ tailWord_648275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648309 : List Nat := [1, 3, 4, 3, 1, 8]
def baseStart_648309 : Nat := 118140960795 + 648309 * 2 ^ 59
def prefixEnd_648309 : Nat := 4983230072969 + 3 ^ 40 * 648309 * 2
def baseEnd_648309 : Nat := 10959477518874377670979

theorem tailTrace_648309 : CollatzResearch.WordTrace tailWord_648309 prefixEnd_648309 10959477518874377670979 := by
  unfold tailWord_648309
  simp only [CollatzResearch.WordTrace]
  refine ⟨23645771808294690207251981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15763847872196460138167987 23645771808294690207251981)
  ·
    refine ⟨8867164428110508827719493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23645771808294690207251981 8867164428110508827719493)
    ·
      refine ⟨1662593330270720405197405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8867164428110508827719493 1662593330270720405197405)
      ·
        refine ⟨623472498851520151949027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1662593330270720405197405 623472498851520151949027)
        ·
          refine ⟨935208748277280227923541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623472498851520151949027 935208748277280227923541)
          ·
            refine ⟨10959477518874377670979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 935208748277280227923541 10959477518874377670979)
            ·
              rfl

theorem cell20_648309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 8].length) (baseStart_648309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648309 prefixEnd_648309 := by exact prefixLift 648309
  have htrace : WordTrace (prefixWord ++ tailWord_648309) baseStart_648309 baseEnd_648309 := by
    simpa [prefixWord, tailWord_648309, baseEnd_648309] using wordTrace_append hprefix tailTrace_648309
  have hstable : (prefixWord ++ tailWord_648309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648309).length < 2 ^ (prefixWord ++ tailWord_648309).sum := by decide
  have hdescent : baseEnd_648309 < baseStart_648309 := by decide
  rcases family_descends (prefixWord ++ tailWord_648309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648313 : List Nat := [1, 2, 1, 3, 13]
def baseStart_648313 : Nat := 118140960795 + 648313 * 2 ^ 59
def prefixEnd_648313 : Nat := 4983230072969 + 3 ^ 40 * 648313 * 2
def baseEnd_648313 : Nat := 3653181712575332851643

theorem tailTrace_648313 : CollatzResearch.WordTrace tailWord_648313 prefixEnd_648313 3653181712575332851643 := by
  unfold tailWord_648313
  simp only [CollatzResearch.WordTrace]
  refine ⟨23645917700280198890397593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15763945133520132593598395 23645917700280198890397593)
  ·
    refine ⟨17734438275210149167798195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23645917700280198890397593 17734438275210149167798195)
    ·
      refine ⟨26601657412815223751697293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17734438275210149167798195 26601657412815223751697293)
      ·
        refine ⟨9975621529805708906886485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26601657412815223751697293 9975621529805708906886485)
        ·
          refine ⟨3653181712575332851643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9975621529805708906886485 3653181712575332851643)
          ·
            rfl

theorem cell20_648313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 13].length) (baseStart_648313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648313 prefixEnd_648313 := by exact prefixLift 648313
  have htrace : WordTrace (prefixWord ++ tailWord_648313) baseStart_648313 baseEnd_648313 := by
    simpa [prefixWord, tailWord_648313, baseEnd_648313] using wordTrace_append hprefix tailTrace_648313
  have hstable : (prefixWord ++ tailWord_648313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648313).length < 2 ^ (prefixWord ++ tailWord_648313).sum := by decide
  have hdescent : baseEnd_648313 < baseStart_648313 := by decide
  rcases family_descends (prefixWord ++ tailWord_648313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648316 : List Nat := [2, 2, 2, 1, 1, 3, 4, 2, 3]
def baseStart_648316 : Nat := 118140960795 + 648316 * 2 ^ 59
def prefixEnd_648316 : Nat := 4983230072969 + 3 ^ 40 * 648316 * 2
def baseEnd_648316 : Nat := 295909088000347283883071

theorem tailTrace_648316 : CollatzResearch.WordTrace tailWord_648316 prefixEnd_648316 295909088000347283883071 := by
  unfold tailWord_648316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11823013559634665201378401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15764018079512886935171201 11823013559634665201378401)
  ·
    refine ⟨8867260169725998901033801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11823013559634665201378401 8867260169725998901033801)
    ·
      refine ⟨6650445127294499175775351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8867260169725998901033801 6650445127294499175775351)
      ·
        refine ⟨9975667690941748763663027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6650445127294499175775351 9975667690941748763663027)
        ·
          refine ⟨14963501536412623145494541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9975667690941748763663027 14963501536412623145494541)
          ·
            refine ⟨5611313076154733679560453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14963501536412623145494541 5611313076154733679560453)
            ·
              refine ⟨1052121201779012564917585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5611313076154733679560453 1052121201779012564917585)
              ·
                refine ⟨789090901334259423688189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052121201779012564917585 789090901334259423688189)
                ·
                  refine ⟨295909088000347283883071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789090901334259423688189 295909088000347283883071)
                  ·
                    rfl

theorem cell20_648316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_648316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648316 prefixEnd_648316 := by exact prefixLift 648316
  have htrace : WordTrace (prefixWord ++ tailWord_648316) baseStart_648316 baseEnd_648316 := by
    simpa [prefixWord, tailWord_648316, baseEnd_648316] using wordTrace_append hprefix tailTrace_648316
  have hstable : (prefixWord ++ tailWord_648316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648316).length < 2 ^ (prefixWord ++ tailWord_648316).sum := by decide
  have hdescent : baseEnd_648316 < baseStart_648316 := by decide
  rcases family_descends (prefixWord ++ tailWord_648316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648374 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_648374 : Nat := 118140960795 + 648374 * 2 ^ 59
def prefixEnd_648374 : Nat := 4983230072969 + 3 ^ 40 * 648374 * 2
def baseEnd_648374 : Nat := 295935560780756859949501

theorem tailTrace_648374 : CollatzResearch.WordTrace tailWord_648374 prefixEnd_648374 295935560780756859949501 := by
  unfold tailWord_648374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1478008909566200394273011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15765428368706137538912117 1478008909566200394273011)
  ·
    refine ⟨2217013364349300591409517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1478008909566200394273011 2217013364349300591409517)
    ·
      refine ⟨831380011630987721778569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2217013364349300591409517 831380011630987721778569)
      ·
        refine ⟨623535008723240791333927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 831380011630987721778569 623535008723240791333927)
        ·
          refine ⟨935302513084861187000891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623535008723240791333927 935302513084861187000891)
          ·
            refine ⟨1402953769627291780501337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935302513084861187000891 1402953769627291780501337)
            ·
              refine ⟨1052215327220468835376003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402953769627291780501337 1052215327220468835376003)
              ·
                refine ⟨1578322990830703253064005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052215327220468835376003 1578322990830703253064005)
                ·
                  refine ⟨295935560780756859949501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1578322990830703253064005 295935560780756859949501)
                  ·
                    rfl

theorem cell20_648374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_648374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648374 prefixEnd_648374 := by exact prefixLift 648374
  have htrace : WordTrace (prefixWord ++ tailWord_648374) baseStart_648374 baseEnd_648374 := by
    simpa [prefixWord, tailWord_648374, baseEnd_648374] using wordTrace_append hprefix tailTrace_648374
  have hstable : (prefixWord ++ tailWord_648374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648374).length < 2 ^ (prefixWord ++ tailWord_648374).sum := by decide
  have hdescent : baseEnd_648374 < baseStart_648374 := by decide
  rcases family_descends (prefixWord ++ tailWord_648374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648375 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 5]
def baseStart_648375 : Nat := 118140960795 + 648375 * 2 ^ 59
def prefixEnd_648375 : Nat := 4983230072969 + 3 ^ 40 * 648375 * 2
def baseEnd_648375 : Nat := 295936017208005300916163

theorem tailTrace_648375 : CollatzResearch.WordTrace tailWord_648375 prefixEnd_648375 295936017208005300916163 := by
  unfold tailWord_648375
  simp only [CollatzResearch.WordTrace]
  refine ⟨23648179026055583479154579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15765452684037055652769719 23648179026055583479154579)
  ·
    refine ⟨35472268539083375218731869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23648179026055583479154579 35472268539083375218731869)
    ·
      refine ⟨13302100702156265707024451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35472268539083375218731869 13302100702156265707024451)
      ·
        refine ⟨19953151053234398560536677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13302100702156265707024451 19953151053234398560536677)
        ·
          refine ⟨3741215822481449730100627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19953151053234398560536677 3741215822481449730100627)
          ·
            refine ⟨5611823733722174595150941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3741215822481449730100627 5611823733722174595150941)
            ·
              refine ⟨2104433900145815473181603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5611823733722174595150941 2104433900145815473181603)
              ·
                refine ⟨3156650850218723209772405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104433900145815473181603 3156650850218723209772405)
                ·
                  refine ⟨295936017208005300916163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3156650850218723209772405 295936017208005300916163)
                  ·
                    rfl

theorem cell20_648375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_648375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648375 prefixEnd_648375 := by exact prefixLift 648375
  have htrace : WordTrace (prefixWord ++ tailWord_648375) baseStart_648375 baseEnd_648375 := by
    simpa [prefixWord, tailWord_648375, baseEnd_648375] using wordTrace_append hprefix tailTrace_648375
  have hstable : (prefixWord ++ tailWord_648375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648375).length < 2 ^ (prefixWord ++ tailWord_648375).sum := by decide
  have hdescent : baseEnd_648375 < baseStart_648375 := by decide
  rcases family_descends (prefixWord ++ tailWord_648375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648388 : List Nat := [2, 3, 3, 1, 3, 1, 3, 1, 3]
def baseStart_648388 : Nat := 118140960795 + 648388 * 2 ^ 59
def prefixEnd_648388 : Nat := 4983230072969 + 3 ^ 40 * 648388 * 2
def baseEnd_648388 : Nat := 295941950762235033482777

theorem tailTrace_648388 : CollatzResearch.WordTrace tailWord_648388 prefixEnd_648388 295941950762235033482777 := by
  unfold tailWord_648388
  simp only [CollatzResearch.WordTrace]
  refine ⟨11824326587504243349688909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15765768783338991132918545 11824326587504243349688909)
  ·
    refine ⟨4434122470314091256133341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11824326587504243349688909 4434122470314091256133341)
    ·
      refine ⟨1662795926367784221050003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4434122470314091256133341 1662795926367784221050003)
      ·
        refine ⟨2494193889551676331575005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1662795926367784221050003 2494193889551676331575005)
        ·
          refine ⟨935322708581878624340627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2494193889551676331575005 935322708581878624340627)
          ·
            refine ⟨1402984062872817936510941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935322708581878624340627 1402984062872817936510941)
            ·
              refine ⟨526119023577306726191603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1402984062872817936510941 526119023577306726191603)
              ·
                refine ⟨789178535365960089287405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526119023577306726191603 789178535365960089287405)
                ·
                  refine ⟨295941950762235033482777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789178535365960089287405 295941950762235033482777)
                  ·
                    rfl

theorem cell20_648388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_648388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648388 prefixEnd_648388 := by exact prefixLift 648388
  have htrace : WordTrace (prefixWord ++ tailWord_648388) baseStart_648388 baseEnd_648388 := by
    simpa [prefixWord, tailWord_648388, baseEnd_648388] using wordTrace_append hprefix tailTrace_648388
  have hstable : (prefixWord ++ tailWord_648388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648388).length < 2 ^ (prefixWord ++ tailWord_648388).sum := by decide
  have hdescent : baseEnd_648388 < baseStart_648388 := by decide
  rcases family_descends (prefixWord ++ tailWord_648388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648389 : List Nat := [1, 3, 1, 1, 1, 1, 3, 9]
def baseStart_648389 : Nat := 118140960795 + 648389 * 2 ^ 59
def prefixEnd_648389 : Nat := 4983230072969 + 3 ^ 40 * 648389 * 2
def baseEnd_648389 : Nat := 98647469063161158149813

theorem tailTrace_648389 : CollatzResearch.WordTrace tailWord_648389 prefixEnd_648389 98647469063161158149813 := by
  unfold tailWord_648389
  simp only [CollatzResearch.WordTrace]
  refine ⟨23648689648004863870164221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15765793098669909246776147 23648689648004863870164221)
  ·
    refine ⟨8868258618001823951311583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23648689648004863870164221 8868258618001823951311583)
    ·
      refine ⟨13302387927002735926967375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8868258618001823951311583 13302387927002735926967375)
      ·
        refine ⟨19953581890504103890451063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13302387927002735926967375 19953581890504103890451063)
        ·
          refine ⟨29930372835756155835676595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19953581890504103890451063 29930372835756155835676595)
          ·
            refine ⟨44895559253634233753514893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29930372835756155835676595 44895559253634233753514893)
            ·
              refine ⟨16835834720112837657568085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44895559253634233753514893 16835834720112837657568085)
              ·
                refine ⟨98647469063161158149813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16835834720112837657568085 98647469063161158149813)
                ·
                  rfl

theorem cell20_648389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_648389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648389 prefixEnd_648389 := by exact prefixLift 648389
  have htrace : WordTrace (prefixWord ++ tailWord_648389) baseStart_648389 baseEnd_648389 := by
    simpa [prefixWord, tailWord_648389, baseEnd_648389] using wordTrace_append hprefix tailTrace_648389
  have hstable : (prefixWord ++ tailWord_648389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648389).length < 2 ^ (prefixWord ++ tailWord_648389).sum := by decide
  have hdescent : baseEnd_648389 < baseStart_648389 := by decide
  rcases family_descends (prefixWord ++ tailWord_648389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648416 : List Nat := [2, 1, 1, 3, 1, 4, 3, 3, 2]
def baseStart_648416 : Nat := 118140960795 + 648416 * 2 ^ 59
def prefixEnd_648416 : Nat := 4983230072969 + 3 ^ 40 * 648416 * 2
def baseEnd_648416 : Nat := 295954730725191380549329

theorem tailTrace_648416 : CollatzResearch.WordTrace tailWord_648416 prefixEnd_648416 295954730725191380549329 := by
  unfold tailWord_648416
  simp only [CollatzResearch.WordTrace]
  refine ⟨11824837209453523740698551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15766449612604698320931401 11824837209453523740698551)
  ·
    refine ⟨17737255814180285611047827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11824837209453523740698551 17737255814180285611047827)
    ·
      refine ⟨26605883721270428416571741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17737255814180285611047827 26605883721270428416571741)
      ·
        refine ⟨9977206395476410656214403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26605883721270428416571741 9977206395476410656214403)
        ·
          refine ⟨14965809593214615984321605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9977206395476410656214403 14965809593214615984321605)
          ·
            refine ⟨2806089298727740497060301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14965809593214615984321605 2806089298727740497060301)
            ·
              refine ⟨1052283487022902686397613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2806089298727740497060301 1052283487022902686397613)
              ·
                refine ⟨394606307633588507399105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1052283487022902686397613 394606307633588507399105)
                ·
                  refine ⟨295954730725191380549329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394606307633588507399105 295954730725191380549329)
                  ·
                    rfl

theorem cell20_648416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 2].length) (baseStart_648416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648416 prefixEnd_648416 := by exact prefixLift 648416
  have htrace : WordTrace (prefixWord ++ tailWord_648416) baseStart_648416 baseEnd_648416 := by
    simpa [prefixWord, tailWord_648416, baseEnd_648416] using wordTrace_append hprefix tailTrace_648416
  have hstable : (prefixWord ++ tailWord_648416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648416).length < 2 ^ (prefixWord ++ tailWord_648416).sum := by decide
  have hdescent : baseEnd_648416 < baseStart_648416 := by decide
  rcases family_descends (prefixWord ++ tailWord_648416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648420 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_648420 : Nat := 118140960795 + 648420 * 2 ^ 59
def prefixEnd_648420 : Nat := 4983230072969 + 3 ^ 40 * 648420 * 2
def baseEnd_648420 : Nat := 295956556434185144415979

theorem tailTrace_648420 : CollatzResearch.WordTrace tailWord_648420 prefixEnd_648420 295956556434185144415979 := by
  unfold tailWord_648420
  simp only [CollatzResearch.WordTrace]
  refine ⟨11824910155446278082271357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15766546873928370776361809 11824910155446278082271357)
  ·
    refine ⟨4434341308292354280851759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11824910155446278082271357 4434341308292354280851759)
    ·
      refine ⟨6651511962438531421277639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4434341308292354280851759 6651511962438531421277639)
      ·
        refine ⟨9977267943657797131916459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6651511962438531421277639 9977267943657797131916459)
        ·
          refine ⟨14965901915486695697874689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9977267943657797131916459 14965901915486695697874689)
          ·
            refine ⟨11224426436615021773406017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14965901915486695697874689 11224426436615021773406017)
            ·
              refine ⟨8418319827461266330054513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11224426436615021773406017 8418319827461266330054513)
              ·
                refine ⟨6313739870595949747540885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8418319827461266330054513 6313739870595949747540885)
                ·
                  refine ⟨295956556434185144415979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6313739870595949747540885 295956556434185144415979)
                  ·
                    rfl

theorem cell20_648420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_648420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648420 prefixEnd_648420 := by exact prefixLift 648420
  have htrace : WordTrace (prefixWord ++ tailWord_648420) baseStart_648420 baseEnd_648420 := by
    simpa [prefixWord, tailWord_648420, baseEnd_648420] using wordTrace_append hprefix tailTrace_648420
  have hstable : (prefixWord ++ tailWord_648420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648420).length < 2 ^ (prefixWord ++ tailWord_648420).sum := by decide
  have hdescent : baseEnd_648420 < baseStart_648420 := by decide
  rcases family_descends (prefixWord ++ tailWord_648420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648423 : List Nat := [1, 1, 5, 3, 2, 2, 6]
def baseStart_648423 : Nat := 118140960795 + 648423 * 2 ^ 59
def prefixEnd_648423 : Nat := 4983230072969 + 3 ^ 40 * 648423 * 2
def baseEnd_648423 : Nat := 32884213968436718590663

theorem tailTrace_648423 : CollatzResearch.WordTrace tailWord_648423 prefixEnd_648423 32884213968436718590663 := by
  unfold tailWord_648423
  simp only [CollatzResearch.WordTrace]
  refine ⟨23649929729881687676901923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15766619819921125117934615 23649929729881687676901923)
  ·
    refine ⟨35474894594822531515352885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23649929729881687676901923 35474894594822531515352885)
    ·
      refine ⟨3325771368264612329564333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35474894594822531515352885 3325771368264612329564333)
      ·
        refine ⟨1247164263099229623586625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3325771368264612329564333 1247164263099229623586625)
        ·
          refine ⟨935373197324422217689969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1247164263099229623586625 935373197324422217689969)
          ·
            refine ⟨701529897993316663267477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 935373197324422217689969 701529897993316663267477)
            ·
              refine ⟨32884213968436718590663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 701529897993316663267477 32884213968436718590663)
              ·
                rfl

theorem cell20_648423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 6].length) (baseStart_648423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648423 prefixEnd_648423 := by exact prefixLift 648423
  have htrace : WordTrace (prefixWord ++ tailWord_648423) baseStart_648423 baseEnd_648423 := by
    simpa [prefixWord, tailWord_648423, baseEnd_648423] using wordTrace_append hprefix tailTrace_648423
  have hstable : (prefixWord ++ tailWord_648423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648423).length < 2 ^ (prefixWord ++ tailWord_648423).sum := by decide
  have hdescent : baseEnd_648423 < baseStart_648423 := by decide
  rcases family_descends (prefixWord ++ tailWord_648423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648427 : List Nat := [1, 1, 1, 1, 2, 6, 8]
def baseStart_648427 : Nat := 118140960795 + 648427 * 2 ^ 59
def prefixEnd_648427 : Nat := 4983230072969 + 3 ^ 40 * 648427 * 2
def baseEnd_648427 : Nat := 32884416824991581242513

theorem tailTrace_648427 : CollatzResearch.WordTrace tailWord_648427 prefixEnd_648427 32884416824991581242513 := by
  unfold tailWord_648427
  simp only [CollatzResearch.WordTrace]
  refine ⟨23650075621867196360047535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15766717081244797573365023 23650075621867196360047535)
  ·
    refine ⟨35475113432800794540071303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23650075621867196360047535 35475113432800794540071303)
    ·
      refine ⟨53212670149201191810106955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35475113432800794540071303 53212670149201191810106955)
      ·
        refine ⟨79819005223801787715160433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53212670149201191810106955 79819005223801787715160433)
        ·
          refine ⟨59864253917851340786370325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79819005223801787715160433 59864253917851340786370325)
          ·
            refine ⟨2806136902399281599361109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59864253917851340786370325 2806136902399281599361109)
            ·
              refine ⟨32884416824991581242513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2806136902399281599361109 32884416824991581242513)
              ·
                rfl

theorem cell20_648427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 8].length) (baseStart_648427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648427 prefixEnd_648427 := by exact prefixLift 648427
  have htrace : WordTrace (prefixWord ++ tailWord_648427) baseStart_648427 baseEnd_648427 := by
    simpa [prefixWord, tailWord_648427, baseEnd_648427] using wordTrace_append hprefix tailTrace_648427
  have hstable : (prefixWord ++ tailWord_648427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648427).length < 2 ^ (prefixWord ++ tailWord_648427).sum := by decide
  have hdescent : baseEnd_648427 < baseStart_648427 := by decide
  rcases family_descends (prefixWord ++ tailWord_648427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648447 : List Nat := [1, 1, 2, 2, 1, 7, 2, 1, 3]
def baseStart_648447 : Nat := 118140960795 + 648447 * 2 ^ 59
def prefixEnd_648447 : Nat := 4983230072969 + 3 ^ 40 * 648447 * 2
def baseEnd_648447 : Nat := 295968879969893050515869

theorem tailTrace_648447 : CollatzResearch.WordTrace tailWord_648447 prefixEnd_648447 295968879969893050515869 := by
  unfold tailWord_648447
  simp only [CollatzResearch.WordTrace]
  refine ⟨23650805081794739775775595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15767203387863159850517063 23650805081794739775775595)
  ·
    refine ⟨35476207622692109663663393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23650805081794739775775595 35476207622692109663663393)
    ·
      refine ⟨26607155717019082247747545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35476207622692109663663393 26607155717019082247747545)
      ·
        refine ⟨19955366787764311685810659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26607155717019082247747545 19955366787764311685810659)
        ·
          refine ⟨29933050181646467528715989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19955366787764311685810659 29933050181646467528715989)
          ·
            refine ⟨701555863632339082704281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29933050181646467528715989 701555863632339082704281)
            ·
              refine ⟨526166897724254312028211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701555863632339082704281 526166897724254312028211)
              ·
                refine ⟨789250346586381468042317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526166897724254312028211 789250346586381468042317)
                ·
                  refine ⟨295968879969893050515869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789250346586381468042317 295968879969893050515869)
                  ·
                    rfl

theorem cell20_648447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 3].length) (baseStart_648447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648447 prefixEnd_648447 := by exact prefixLift 648447
  have htrace : WordTrace (prefixWord ++ tailWord_648447) baseStart_648447 baseEnd_648447 := by
    simpa [prefixWord, tailWord_648447, baseEnd_648447] using wordTrace_append hprefix tailTrace_648447
  have hstable : (prefixWord ++ tailWord_648447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648447).length < 2 ^ (prefixWord ++ tailWord_648447).sum := by decide
  have hdescent : baseEnd_648447 < baseStart_648447 := by decide
  rcases family_descends (prefixWord ++ tailWord_648447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648458 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_648458 : Nat := 118140960795 + 648458 * 2 ^ 59
def prefixEnd_648458 : Nat := 4983230072969 + 3 ^ 40 * 648458 * 2
def baseEnd_648458 : Nat := 295973900669625901149157

theorem tailTrace_648458 : CollatzResearch.WordTrace tailWord_648458 prefixEnd_648458 295973900669625901149157 := by
  unfold tailWord_648458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5912801571188722163606507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15767470856503259102950685 5912801571188722163606507)
  ·
    refine ⟨8869202356783083245409761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5912801571188722163606507 8869202356783083245409761)
    ·
      refine ⟨6651901767587312434057321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8869202356783083245409761 6651901767587312434057321)
      ·
        refine ⟨4988926325690484325542991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6651901767587312434057321 4988926325690484325542991)
        ·
          refine ⟨7483389488535726488314487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4988926325690484325542991 7483389488535726488314487)
          ·
            refine ⟨11225084232803589732471731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7483389488535726488314487 11225084232803589732471731)
            ·
              refine ⟨16837626349205384598707597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11225084232803589732471731 16837626349205384598707597)
              ·
                refine ⟨6314109880952019224515349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16837626349205384598707597 6314109880952019224515349)
                ·
                  refine ⟨295973900669625901149157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6314109880952019224515349 295973900669625901149157)
                  ·
                    rfl

theorem cell20_648458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_648458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648458 prefixEnd_648458 := by exact prefixLift 648458
  have htrace : WordTrace (prefixWord ++ tailWord_648458) baseStart_648458 baseEnd_648458 := by
    simpa [prefixWord, tailWord_648458, baseEnd_648458] using wordTrace_append hprefix tailTrace_648458
  have hstable : (prefixWord ++ tailWord_648458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648458).length < 2 ^ (prefixWord ++ tailWord_648458).sum := by decide
  have hdescent : baseEnd_648458 < baseStart_648458 := by decide
  rcases family_descends (prefixWord ++ tailWord_648458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648465 : List Nat := [1, 2, 2, 1, 1, 4, 1, 8]
def baseStart_648465 : Nat := 118140960795 + 648465 * 2 ^ 59
def prefixEnd_648465 : Nat := 4983230072969 + 3 ^ 40 * 648465 * 2
def baseEnd_648465 : Nat := 98659031886788329305265

theorem tailTrace_648465 : CollatzResearch.WordTrace tailWord_648465 prefixEnd_648465 98659031886788329305265 := by
  unfold tailWord_648465
  simp only [CollatzResearch.WordTrace]
  refine ⟨23651461595729528849930849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15767641063819685899953899 23651461595729528849930849)
  ·
    refine ⟨17738596196797146637448137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23651461595729528849930849 17738596196797146637448137)
    ·
      refine ⟨13303947147597859978086103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17738596196797146637448137 13303947147597859978086103)
      ·
        refine ⟨19955920721396789967129155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13303947147597859978086103 19955920721396789967129155)
        ·
          refine ⟨29933881082095184950693733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19955920721396789967129155 29933881082095184950693733)
          ·
            refine ⟨5612602702892847178255075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29933881082095184950693733 5612602702892847178255075)
            ·
              refine ⟨8418904054339270767382613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5612602702892847178255075 8418904054339270767382613)
              ·
                refine ⟨98659031886788329305265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8418904054339270767382613 98659031886788329305265)
                ·
                  rfl

theorem cell20_648465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_648465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648465 prefixEnd_648465 := by exact prefixLift 648465
  have htrace : WordTrace (prefixWord ++ tailWord_648465) baseStart_648465 baseEnd_648465 := by
    simpa [prefixWord, tailWord_648465, baseEnd_648465] using wordTrace_append hprefix tailTrace_648465
  have hstable : (prefixWord ++ tailWord_648465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648465).length < 2 ^ (prefixWord ++ tailWord_648465).sum := by decide
  have hdescent : baseEnd_648465 < baseStart_648465 := by decide
  rcases family_descends (prefixWord ++ tailWord_648465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648475 : List Nat := [1, 1, 1, 1, 1, 1, 5, 7, 2]
def baseStart_648475 : Nat := 118140960795 + 648475 * 2 ^ 59
def prefixEnd_648475 : Nat := 4983230072969 + 3 ^ 40 * 648475 * 2
def baseEnd_648475 : Nat := 295981659932849397582421

theorem tailTrace_648475 : CollatzResearch.WordTrace tailWord_648475 prefixEnd_648475 295981659932849397582421 := by
  unfold tailWord_648475
  simp only [CollatzResearch.WordTrace]
  refine ⟨23651826325693300557794879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15767884217128867038529919 23651826325693300557794879)
  ·
    refine ⟨35477739488539950836692319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23651826325693300557794879 35477739488539950836692319)
    ·
      refine ⟨53216609232809926255038479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35477739488539950836692319 53216609232809926255038479)
      ·
        refine ⟨79824913849214889382557719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53216609232809926255038479 79824913849214889382557719)
        ·
          refine ⟨119737370773822334073836579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79824913849214889382557719 119737370773822334073836579)
          ·
            refine ⟨179606056160733501110754869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119737370773822334073836579 179606056160733501110754869)
            ·
              refine ⟨16838067765068765729133269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179606056160733501110754869 16838067765068765729133269)
              ·
                refine ⟨394642213243799196776561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16838067765068765729133269 394642213243799196776561)
                ·
                  refine ⟨295981659932849397582421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394642213243799196776561 295981659932849397582421)
                  ·
                    rfl

theorem cell20_648475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 2].length) (baseStart_648475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648475 prefixEnd_648475 := by exact prefixLift 648475
  have htrace : WordTrace (prefixWord ++ tailWord_648475) baseStart_648475 baseEnd_648475 := by
    simpa [prefixWord, tailWord_648475, baseEnd_648475] using wordTrace_append hprefix tailTrace_648475
  have hstable : (prefixWord ++ tailWord_648475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648475).length < 2 ^ (prefixWord ++ tailWord_648475).sum := by decide
  have hdescent : baseEnd_648475 < baseStart_648475 := by decide
  rcases family_descends (prefixWord ++ tailWord_648475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648478 : List Nat := [4, 3, 2, 1, 3, 7]
def baseStart_648478 : Nat := 118140960795 + 648478 * 2 ^ 59
def prefixEnd_648478 : Nat := 4983230072969 + 3 ^ 40 * 648478 * 2
def baseEnd_648478 : Nat := 10962334415355360017867

theorem tailTrace_648478 : CollatzResearch.WordTrace tailWord_648478 prefixEnd_648478 10962334415355360017867 := by
  unfold tailWord_648478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2956491968085304008769261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15767957163121621380102725 2956491968085304008769261)
  ·
    refine ⟨1108684488031989003288473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2956491968085304008769261 1108684488031989003288473)
    ·
      refine ⟨831513366023991752466355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1108684488031989003288473 831513366023991752466355)
      ·
        refine ⟨1247270049035987628699533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831513366023991752466355 1247270049035987628699533)
        ·
          refine ⟨467726268388495360762325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1247270049035987628699533 467726268388495360762325)
          ·
            refine ⟨10962334415355360017867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 467726268388495360762325 10962334415355360017867)
            ·
              rfl

theorem cell20_648478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 7].length) (baseStart_648478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648478 prefixEnd_648478 := by exact prefixLift 648478
  have htrace : WordTrace (prefixWord ++ tailWord_648478) baseStart_648478 baseEnd_648478 := by
    simpa [prefixWord, tailWord_648478, baseEnd_648478] using wordTrace_append hprefix tailTrace_648478
  have hstable : (prefixWord ++ tailWord_648478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648478).length < 2 ^ (prefixWord ++ tailWord_648478).sum := by decide
  have hdescent : baseEnd_648478 < baseStart_648478 := by decide
  rcases family_descends (prefixWord ++ tailWord_648478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648482 : List Nat := [3, 3, 1, 1, 4, 8]
def baseStart_648482 : Nat := 118140960795 + 648482 * 2 ^ 59
def prefixEnd_648482 : Nat := 4983230072969 + 3 ^ 40 * 648482 * 2
def baseEnd_648482 : Nat := 10962402034206980901817

theorem tailTrace_648482 : CollatzResearch.WordTrace tailWord_648482 prefixEnd_648482 10962402034206980901817 := by
  unfold tailWord_648482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5913020409166985188324925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15768054424445293835533133 5913020409166985188324925)
  ·
    refine ⟨2217382653437619445621847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5913020409166985188324925 2217382653437619445621847)
    ·
      refine ⟨3326073980156429168432771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2217382653437619445621847 3326073980156429168432771)
      ·
        refine ⟨4989110970234643752649157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3326073980156429168432771 4989110970234643752649157)
        ·
          refine ⟨935458306918995703621717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4989110970234643752649157 935458306918995703621717)
          ·
            refine ⟨10962402034206980901817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 935458306918995703621717 10962402034206980901817)
            ·
              rfl

theorem cell20_648482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 8].length) (baseStart_648482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648482 prefixEnd_648482 := by exact prefixLift 648482
  have htrace : WordTrace (prefixWord ++ tailWord_648482) baseStart_648482 baseEnd_648482 := by
    simpa [prefixWord, tailWord_648482, baseEnd_648482] using wordTrace_append hprefix tailTrace_648482
  have hstable : (prefixWord ++ tailWord_648482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648482).length < 2 ^ (prefixWord ++ tailWord_648482).sum := by decide
  have hdescent : baseEnd_648482 < baseStart_648482 := by decide
  rcases family_descends (prefixWord ++ tailWord_648482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648488 : List Nat := [2, 1, 5, 1, 2, 3, 2, 2, 2]
def baseStart_648488 : Nat := 118140960795 + 648488 * 2 ^ 59
def prefixEnd_648488 : Nat := 4983230072969 + 3 ^ 40 * 648488 * 2
def baseEnd_648488 : Nat := 295987593487079130149035

theorem tailTrace_648488 : CollatzResearch.WordTrace tailWord_648488 prefixEnd_648488 295987593487079130149035 := by
  unfold tailWord_648488
  simp only [CollatzResearch.WordTrace]
  refine ⟨11826150237323101889009059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15768200316430802518678745 11826150237323101889009059)
  ·
    refine ⟨17739225355984652833513589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11826150237323101889009059 17739225355984652833513589)
    ·
      refine ⟨1663052377123561203141899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17739225355984652833513589 1663052377123561203141899)
      ·
        refine ⟨2494578565685341804712849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663052377123561203141899 2494578565685341804712849)
        ·
          refine ⟨1870933924264006353534637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2494578565685341804712849 1870933924264006353534637)
          ·
            refine ⟨701600221599002382575489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1870933924264006353534637 701600221599002382575489)
            ·
              refine ⟨526200166199251786931617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701600221599002382575489 526200166199251786931617)
              ·
                refine ⟨394650124649438840198713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526200166199251786931617 394650124649438840198713)
                ·
                  refine ⟨295987593487079130149035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394650124649438840198713 295987593487079130149035)
                  ·
                    rfl

theorem cell20_648488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 2].length) (baseStart_648488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648488 prefixEnd_648488 := by exact prefixLift 648488
  have htrace : WordTrace (prefixWord ++ tailWord_648488) baseStart_648488 baseEnd_648488 := by
    simpa [prefixWord, tailWord_648488, baseEnd_648488] using wordTrace_append hprefix tailTrace_648488
  have hstable : (prefixWord ++ tailWord_648488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648488).length < 2 ^ (prefixWord ++ tailWord_648488).sum := by decide
  have hdescent : baseEnd_648488 < baseStart_648488 := by decide
  rcases family_descends (prefixWord ++ tailWord_648488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648496 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_648496 : Nat := 118140960795 + 648496 * 2 ^ 59
def prefixEnd_648496 : Nat := 4983230072969 + 3 ^ 40 * 648496 * 2
def baseEnd_648496 : Nat := 295991244905066657882335

theorem tailTrace_648496 : CollatzResearch.WordTrace tailWord_648496 prefixEnd_648496 295991244905066657882335 := by
  unfold tailWord_648496
  simp only [CollatzResearch.WordTrace]
  refine ⟨11826296129308610572154671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15768394839078147429539561 11826296129308610572154671)
  ·
    refine ⟨17739444193962915858232007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11826296129308610572154671 17739444193962915858232007)
    ·
      refine ⟨26609166290944373787348011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17739444193962915858232007 26609166290944373787348011)
      ·
        refine ⟨39913749436416560681022017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26609166290944373787348011 39913749436416560681022017)
        ·
          refine ⟨29935312077312420510766513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39913749436416560681022017 29935312077312420510766513)
          ·
            refine ⟨22451484057984315383074885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29935312077312420510766513 22451484057984315383074885)
            ·
              refine ⟨4209653260872059134326541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22451484057984315383074885 4209653260872059134326541)
              ·
                refine ⟨1578619972827022175372453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4209653260872059134326541 1578619972827022175372453)
                ·
                  refine ⟨295991244905066657882335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1578619972827022175372453 295991244905066657882335)
                  ·
                    rfl

theorem cell20_648496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_648496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648496 prefixEnd_648496 := by exact prefixLift 648496
  have htrace : WordTrace (prefixWord ++ tailWord_648496) baseStart_648496 baseEnd_648496 := by
    simpa [prefixWord, tailWord_648496, baseEnd_648496] using wordTrace_append hprefix tailTrace_648496
  have hstable : (prefixWord ++ tailWord_648496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648496).length < 2 ^ (prefixWord ++ tailWord_648496).sum := by decide
  have hdescent : baseEnd_648496 < baseStart_648496 := by decide
  rcases family_descends (prefixWord ++ tailWord_648496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648513 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 6]
def baseStart_648513 : Nat := 118140960795 + 648513 * 2 ^ 59
def prefixEnd_648513 : Nat := 4983230072969 + 3 ^ 40 * 648513 * 2
def baseEnd_648513 : Nat := 295999004168290154315599

theorem tailTrace_648513 : CollatzResearch.WordTrace tailWord_648513 prefixEnd_648513 295999004168290154315599 := by
  unfold tailWord_648513
  simp only [CollatzResearch.WordTrace]
  refine ⟨23653212299555633047678193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15768808199703755365118795 23653212299555633047678193)
  ·
    refine ⟨17739909224666724785758645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23653212299555633047678193 17739909224666724785758645)
    ·
      refine ⟨1663116489812505448664873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17739909224666724785758645 1663116489812505448664873)
      ·
        refine ⟨1247337367359379086498655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1663116489812505448664873 1247337367359379086498655)
        ·
          refine ⟨1871006051039068629747983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1247337367359379086498655 1871006051039068629747983)
          ·
            refine ⟨2806509076558602944621975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871006051039068629747983 2806509076558602944621975)
            ·
              refine ⟨4209763614837904416932963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806509076558602944621975 4209763614837904416932963)
              ·
                refine ⟨6314645422256856625399445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4209763614837904416932963 6314645422256856625399445)
                ·
                  refine ⟨295999004168290154315599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6314645422256856625399445 295999004168290154315599)
                  ·
                    rfl

theorem cell20_648513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_648513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648513 prefixEnd_648513 := by exact prefixLift 648513
  have htrace : WordTrace (prefixWord ++ tailWord_648513) baseStart_648513 baseEnd_648513 := by
    simpa [prefixWord, tailWord_648513, baseEnd_648513] using wordTrace_append hprefix tailTrace_648513
  have hstable : (prefixWord ++ tailWord_648513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648513).length < 2 ^ (prefixWord ++ tailWord_648513).sum := by decide
  have hdescent : baseEnd_648513 < baseStart_648513 := by decide
  rcases family_descends (prefixWord ++ tailWord_648513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648516 : List Nat := [2, 3, 4, 1, 1, 2, 3, 4]
def baseStart_648516 : Nat := 118140960795 + 648516 * 2 ^ 59
def prefixEnd_648516 : Nat := 4983230072969 + 3 ^ 40 * 648516 * 2
def baseEnd_648516 : Nat := 98666791150011825738529

theorem tailTrace_648516 : CollatzResearch.WordTrace tailWord_648516 prefixEnd_648516 98666791150011825738529 := by
  unfold tailWord_648516
  simp only [CollatzResearch.WordTrace]
  refine ⟨11826660859272382280018701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15768881145696509706691601 11826660859272382280018701)
  ·
    refine ⟨4434997822227143355007013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11826660859272382280018701 4434997822227143355007013)
    ·
      refine ⟨831562091667589379063815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4434997822227143355007013 831562091667589379063815)
      ·
        refine ⟨1247343137501384068595723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831562091667589379063815 1247343137501384068595723)
        ·
          refine ⟨1871014706252076102893585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1247343137501384068595723 1871014706252076102893585)
          ·
            refine ⟨1403261029689057077170189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1871014706252076102893585 1403261029689057077170189)
            ·
              refine ⟨526222886133396403938821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1403261029689057077170189 526222886133396403938821)
              ·
                refine ⟨98666791150011825738529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 526222886133396403938821 98666791150011825738529)
                ·
                  rfl

theorem cell20_648516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_648516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648516 prefixEnd_648516 := by exact prefixLift 648516
  have htrace : WordTrace (prefixWord ++ tailWord_648516) baseStart_648516 baseEnd_648516 := by
    simpa [prefixWord, tailWord_648516, baseEnd_648516] using wordTrace_append hprefix tailTrace_648516
  have hstable : (prefixWord ++ tailWord_648516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648516).length < 2 ^ (prefixWord ++ tailWord_648516).sum := by decide
  have hdescent : baseEnd_648516 < baseStart_648516 := by decide
  rcases family_descends (prefixWord ++ tailWord_648516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648544 : List Nat := [2, 1, 1, 3, 4, 1, 3, 2, 3]
def baseStart_648544 : Nat := 118140960795 + 648544 * 2 ^ 59
def prefixEnd_648544 : Nat := 4983230072969 + 3 ^ 40 * 648544 * 2
def baseEnd_648544 : Nat := 296013153412991824282139

theorem tailTrace_648544 : CollatzResearch.WordTrace tailWord_648544 prefixEnd_648544 296013153412991824282139 := by
  unfold tailWord_648544
  simp only [CollatzResearch.WordTrace]
  refine ⟨11827171481221662671028343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15769561974962216894704457 11827171481221662671028343)
  ·
    refine ⟨17740757221832494006542515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11827171481221662671028343 17740757221832494006542515)
    ·
      refine ⟨26611135832748741009813773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17740757221832494006542515 26611135832748741009813773)
      ·
        refine ⟨9979175937280777878680165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26611135832748741009813773 9979175937280777878680165)
        ·
          refine ⟨1871095488240145852252531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9979175937280777878680165 1871095488240145852252531)
          ·
            refine ⟨2806643232360218778378797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871095488240145852252531 2806643232360218778378797)
            ·
              refine ⟨1052491212135082041892049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2806643232360218778378797 1052491212135082041892049)
              ·
                refine ⟨789368409101311531419037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052491212135082041892049 789368409101311531419037)
                ·
                  refine ⟨296013153412991824282139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789368409101311531419037 296013153412991824282139)
                  ·
                    rfl

theorem cell20_648544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_648544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648544 prefixEnd_648544 := by exact prefixLift 648544
  have htrace : WordTrace (prefixWord ++ tailWord_648544) baseStart_648544 baseEnd_648544 := by
    simpa [prefixWord, tailWord_648544, baseEnd_648544] using wordTrace_append hprefix tailTrace_648544
  have hstable : (prefixWord ++ tailWord_648544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648544).length < 2 ^ (prefixWord ++ tailWord_648544).sum := by decide
  have hdescent : baseEnd_648544 < baseStart_648544 := by decide
  rcases family_descends (prefixWord ++ tailWord_648544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648572 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_648572 : Nat := 118140960795 + 648572 * 2 ^ 59
def prefixEnd_648572 : Nat := 4983230072969 + 3 ^ 40 * 648572 * 2
def baseEnd_648572 : Nat := 296025933375948171348691

theorem tailTrace_648572 : CollatzResearch.WordTrace tailWord_648572 prefixEnd_648572 296025933375948171348691 := by
  unfold tailWord_648572
  simp only [CollatzResearch.WordTrace]
  refine ⟨11827682103170943062037985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15770242804227924082717313 11827682103170943062037985)
  ·
    refine ⟨8870761577378207296528489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11827682103170943062037985 8870761577378207296528489)
    ·
      refine ⟨6653071183033655472396367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8870761577378207296528489 6653071183033655472396367)
      ·
        refine ⟨9979606774550483208594551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6653071183033655472396367 9979606774550483208594551)
        ·
          refine ⟨14969410161825724812891827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9979606774550483208594551 14969410161825724812891827)
          ·
            refine ⟨22454115242738587219337741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14969410161825724812891827 22454115242738587219337741)
            ·
              refine ⟨8420293216026970207251653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22454115242738587219337741 8420293216026970207251653)
              ·
                refine ⟨1578804978005056913859685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8420293216026970207251653 1578804978005056913859685)
                ·
                  refine ⟨296025933375948171348691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1578804978005056913859685 296025933375948171348691)
                  ·
                    rfl

theorem cell20_648572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_648572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648572 prefixEnd_648572 := by exact prefixLift 648572
  have htrace : WordTrace (prefixWord ++ tailWord_648572) baseStart_648572 baseEnd_648572 := by
    simpa [prefixWord, tailWord_648572, baseEnd_648572] using wordTrace_append hprefix tailTrace_648572
  have hstable : (prefixWord ++ tailWord_648572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648572).length < 2 ^ (prefixWord ++ tailWord_648572).sum := by decide
  have hdescent : baseEnd_648572 < baseStart_648572 := by decide
  rcases family_descends (prefixWord ++ tailWord_648572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648585 : List Nat := [1, 2, 1, 1, 7, 2, 1, 3, 2]
def baseStart_648585 : Nat := 118140960795 + 648585 * 2 ^ 59
def prefixEnd_648585 : Nat := 4983230072969 + 3 ^ 40 * 648585 * 2
def baseEnd_648585 : Nat := 296031866930177903915305

theorem tailTrace_648585 : CollatzResearch.WordTrace tailWord_648585 prefixEnd_648585 296031866930177903915305 := by
  unfold tailWord_648585
  simp only [CollatzResearch.WordTrace]
  refine ⟨23655838355294789344299209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15770558903529859562866139 23655838355294789344299209)
  ·
    refine ⟨17741878766471092008224407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23655838355294789344299209 17741878766471092008224407)
    ·
      refine ⟨26612818149706638012336611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17741878766471092008224407 26612818149706638012336611)
      ·
        refine ⟨39919227224559957018504917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26612818149706638012336611 39919227224559957018504917)
        ·
          refine ⟨935606888075623992621209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 39919227224559957018504917 935606888075623992621209)
          ·
            refine ⟨701705166056717994465907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 935606888075623992621209 701705166056717994465907)
            ·
              refine ⟨1052557749085076991698861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701705166056717994465907 1052557749085076991698861)
              ·
                refine ⟨394709155906903871887073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1052557749085076991698861 394709155906903871887073)
                ·
                  refine ⟨296031866930177903915305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394709155906903871887073 296031866930177903915305)
                  ·
                    rfl

theorem cell20_648585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 2].length) (baseStart_648585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648585 prefixEnd_648585 := by exact prefixLift 648585
  have htrace : WordTrace (prefixWord ++ tailWord_648585) baseStart_648585 baseEnd_648585 := by
    simpa [prefixWord, tailWord_648585, baseEnd_648585] using wordTrace_append hprefix tailTrace_648585
  have hstable : (prefixWord ++ tailWord_648585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648585).length < 2 ^ (prefixWord ++ tailWord_648585).sum := by decide
  have hdescent : baseEnd_648585 < baseStart_648585 := by decide
  rcases family_descends (prefixWord ++ tailWord_648585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648596 : List Nat := [2, 4, 2, 1, 2, 1, 8]
def baseStart_648596 : Nat := 118140960795 + 648596 * 2 ^ 59
def prefixEnd_648596 : Nat := 4983230072969 + 3 ^ 40 * 648596 * 2
def baseEnd_648596 : Nat := 32892987514434528283177

theorem tailTrace_648596 : CollatzResearch.WordTrace tailWord_648596 prefixEnd_648596 32892987514434528283177 := by
  unfold tailWord_648596
  simp only [CollatzResearch.WordTrace]
  refine ⟨11828119779127469111474821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15770826372169958815299761 11828119779127469111474821)
  ·
    refine ⟨2217772458586400458401529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11828119779127469111474821 2217772458586400458401529)
    ·
      refine ⟨1663329343939800343801147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2217772458586400458401529 1663329343939800343801147)
      ·
        refine ⟨2494994015909700515701721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663329343939800343801147 2494994015909700515701721)
        ·
          refine ⟨1871245511932275386776291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2494994015909700515701721 1871245511932275386776291)
          ·
            refine ⟨2806868267898413080164437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871245511932275386776291 2806868267898413080164437)
            ·
              refine ⟨32892987514434528283177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2806868267898413080164437 32892987514434528283177)
              ·
                rfl

theorem cell20_648596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 8].length) (baseStart_648596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648596 prefixEnd_648596 := by exact prefixLift 648596
  have htrace : WordTrace (prefixWord ++ tailWord_648596) baseStart_648596 baseEnd_648596 := by
    simpa [prefixWord, tailWord_648596, baseEnd_648596] using wordTrace_append hprefix tailTrace_648596
  have hstable : (prefixWord ++ tailWord_648596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648596).length < 2 ^ (prefixWord ++ tailWord_648596).sum := by decide
  have hdescent : baseEnd_648596 < baseStart_648596 := by decide
  rcases family_descends (prefixWord ++ tailWord_648596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648620 : List Nat := [2, 2, 1, 1, 1, 1, 8, 1, 3]
def baseStart_648620 : Nat := 118140960795 + 648620 * 2 ^ 59
def prefixEnd_648620 : Nat := 4983230072969 + 3 ^ 40 * 648620 * 2
def baseEnd_648620 : Nat := 296047841883873337748495

theorem tailTrace_648620 : CollatzResearch.WordTrace tailWord_648620 prefixEnd_648620 296047841883873337748495 := by
  unfold tailWord_648620
  simp only [CollatzResearch.WordTrace]
  refine ⟨11828557455083995160911657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15771409940111993547882209 11828557455083995160911657)
  ·
    refine ⟨8871418091312996370683743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11828557455083995160911657 8871418091312996370683743)
    ·
      refine ⟨13307127136969494556025615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8871418091312996370683743 13307127136969494556025615)
      ·
        refine ⟨19960690705454241834038423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13307127136969494556025615 19960690705454241834038423)
        ·
          refine ⟨29941036058181362751057635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19960690705454241834038423 29941036058181362751057635)
          ·
            refine ⟨44911554087272044126586453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29941036058181362751057635 44911554087272044126586453)
            ·
              refine ⟨526307274460219267108435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 44911554087272044126586453 526307274460219267108435)
              ·
                refine ⟨789460911690328900662653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526307274460219267108435 789460911690328900662653)
                ·
                  refine ⟨296047841883873337748495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789460911690328900662653 296047841883873337748495)
                  ·
                    rfl

theorem cell20_648620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_648620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648620 prefixEnd_648620 := by exact prefixLift 648620
  have htrace : WordTrace (prefixWord ++ tailWord_648620) baseStart_648620 baseEnd_648620 := by
    simpa [prefixWord, tailWord_648620, baseEnd_648620] using wordTrace_append hprefix tailTrace_648620
  have hstable : (prefixWord ++ tailWord_648620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648620).length < 2 ^ (prefixWord ++ tailWord_648620).sum := by decide
  have hdescent : baseEnd_648620 < baseStart_648620 := by decide
  rcases family_descends (prefixWord ++ tailWord_648620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648624 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_648624 : Nat := 118140960795 + 648624 * 2 ^ 59
def prefixEnd_648624 : Nat := 4983230072969 + 3 ^ 40 * 648624 * 2
def baseEnd_648624 : Nat := 296049667592867101615145

theorem tailTrace_648624 : CollatzResearch.WordTrace tailWord_648624 prefixEnd_648624 296049667592867101615145 := by
  unfold tailWord_648624
  simp only [CollatzResearch.WordTrace]
  refine ⟨11828630401076749502484463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15771507201435666003312617 11828630401076749502484463)
  ·
    refine ⟨17742945601615124253726695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11828630401076749502484463 17742945601615124253726695)
    ·
      refine ⟨26614418402422686380590043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17742945601615124253726695 26614418402422686380590043)
      ·
        refine ⟨39921627603634029570885065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26614418402422686380590043 39921627603634029570885065)
        ·
          refine ⟨29941220702725522178163799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39921627603634029570885065 29941220702725522178163799)
          ·
            refine ⟨44911831054088283267245699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29941220702725522178163799 44911831054088283267245699)
            ·
              refine ⟨67367746581132424900868549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44911831054088283267245699 67367746581132424900868549)
              ·
                refine ⟨12631452483962329668912853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67367746581132424900868549 12631452483962329668912853)
                ·
                  refine ⟨296049667592867101615145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12631452483962329668912853 296049667592867101615145)
                  ·
                    rfl

theorem cell20_648624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_648624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648624 prefixEnd_648624 := by exact prefixLift 648624
  have htrace : WordTrace (prefixWord ++ tailWord_648624) baseStart_648624 baseEnd_648624 := by
    simpa [prefixWord, tailWord_648624, baseEnd_648624] using wordTrace_append hprefix tailTrace_648624
  have hstable : (prefixWord ++ tailWord_648624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648624).length < 2 ^ (prefixWord ++ tailWord_648624).sum := by decide
  have hdescent : baseEnd_648624 < baseStart_648624 := by decide
  rcases family_descends (prefixWord ++ tailWord_648624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648744 : List Nat := [2, 1, 5, 2, 2, 2, 2, 4]
def baseStart_648744 : Nat := 118140960795 + 648744 * 2 ^ 59
def prefixEnd_648744 : Nat := 4983230072969 + 3 ^ 40 * 648744 * 2
def baseEnd_648744 : Nat := 98701479620893339204885

theorem tailTrace_648744 : CollatzResearch.WordTrace tailWord_648744 prefixEnd_648744 98701479620893339204885 := by
  unfold tailWord_648744
  simp only [CollatzResearch.WordTrace]
  refine ⟨11830818780859379749668643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15774425041145839666224857 11830818780859379749668643)
  ·
    refine ⟨17746228171289069624502965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11830818780859379749668643 17746228171289069624502965)
    ·
      refine ⟨1663708891058350277297153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17746228171289069624502965 1663708891058350277297153)
      ·
        refine ⟨1247781668293762707972865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1663708891058350277297153 1247781668293762707972865)
        ·
          refine ⟨935836251220322030979649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1247781668293762707972865 935836251220322030979649)
          ·
            refine ⟨701877188415241523234737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 935836251220322030979649 701877188415241523234737)
            ·
              refine ⟨526407891311431142426053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701877188415241523234737 526407891311431142426053)
              ·
                refine ⟨98701479620893339204885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 526407891311431142426053 98701479620893339204885)
                ·
                  rfl

theorem cell20_648744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_648744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648744 prefixEnd_648744 := by exact prefixLift 648744
  have htrace : WordTrace (prefixWord ++ tailWord_648744) baseStart_648744 baseEnd_648744 := by
    simpa [prefixWord, tailWord_648744, baseEnd_648744] using wordTrace_append hprefix tailTrace_648744
  have hstable : (prefixWord ++ tailWord_648744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648744).length < 2 ^ (prefixWord ++ tailWord_648744).sum := by decide
  have hdescent : baseEnd_648744 < baseStart_648744 := by decide
  rcases family_descends (prefixWord ++ tailWord_648744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648765 : List Nat := [1, 4, 1, 3, 4, 1, 6]
def baseStart_648765 : Nat := 118140960795 + 648765 * 2 ^ 59
def prefixEnd_648765 : Nat := 4983230072969 + 3 ^ 40 * 648765 * 2
def baseEnd_648765 : Nat := 32901558203877475323841

theorem tailTrace_648765 : CollatzResearch.WordTrace tailWord_648765 prefixEnd_648765 32901558203877475323841 := by
  unfold tailWord_648765
  simp only [CollatzResearch.WordTrace]
  refine ⟨23662403494642680085851749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15774935663095120057234499 23662403494642680085851749)
  ·
    refine ⟨4436700655245502516097203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23662403494642680085851749 4436700655245502516097203)
    ·
      refine ⟨6655050982868253774145805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4436700655245502516097203 6655050982868253774145805)
      ·
        refine ⟨2495644118575595165304677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6655050982868253774145805 2495644118575595165304677)
        ·
          refine ⟨467933272232924093494627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2495644118575595165304677 467933272232924093494627)
          ·
            refine ⟨701899908349386140241941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467933272232924093494627 701899908349386140241941)
            ·
              refine ⟨32901558203877475323841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 701899908349386140241941 32901558203877475323841)
              ·
                rfl

theorem cell20_648765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 6].length) (baseStart_648765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648765 prefixEnd_648765 := by exact prefixLift 648765
  have htrace : WordTrace (prefixWord ++ tailWord_648765) baseStart_648765 baseEnd_648765 := by
    simpa [prefixWord, tailWord_648765, baseEnd_648765] using wordTrace_append hprefix tailTrace_648765
  have hstable : (prefixWord ++ tailWord_648765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648765).length < 2 ^ (prefixWord ++ tailWord_648765).sum := by decide
  have hdescent : baseEnd_648765 < baseStart_648765 := by decide
  rcases family_descends (prefixWord ++ tailWord_648765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648775 : List Nat := [1, 1, 4, 1, 5, 1, 3, 2, 2]
def baseStart_648775 : Nat := 118140960795 + 648775 * 2 ^ 59
def prefixEnd_648775 : Nat := 4983230072969 + 3 ^ 40 * 648775 * 2
def baseEnd_648775 : Nat := 296118588107381687581195

theorem tailTrace_648775 : CollatzResearch.WordTrace tailWord_648775 prefixEnd_648775 296118588107381687581195 := by
  unfold tailWord_648775
  simp only [CollatzResearch.WordTrace]
  refine ⟨23662768224606451793715779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15775178816404301195810519 23662768224606451793715779)
  ·
    refine ⟨35494152336909677690573669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23662768224606451793715779 35494152336909677690573669)
    ·
      refine ⟨6655153563170564566982563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35494152336909677690573669 6655153563170564566982563)
      ·
        refine ⟨9982730344755846850473845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6655153563170564566982563 9982730344755846850473845)
        ·
          refine ⟨935880969820860642231923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9982730344755846850473845 935880969820860642231923)
          ·
            refine ⟨1403821454731290963347885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935880969820860642231923 1403821454731290963347885)
            ·
              refine ⟨526433045524234111255457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1403821454731290963347885 526433045524234111255457)
              ·
                refine ⟨394824784143175583441593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526433045524234111255457 394824784143175583441593)
                ·
                  refine ⟨296118588107381687581195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394824784143175583441593 296118588107381687581195)
                  ·
                    rfl

theorem cell20_648775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 2].length) (baseStart_648775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648775 prefixEnd_648775 := by exact prefixLift 648775
  have htrace : WordTrace (prefixWord ++ tailWord_648775) baseStart_648775 baseEnd_648775 := by
    simpa [prefixWord, tailWord_648775, baseEnd_648775] using wordTrace_append hprefix tailTrace_648775
  have hstable : (prefixWord ++ tailWord_648775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648775).length < 2 ^ (prefixWord ++ tailWord_648775).sum := by decide
  have hdescent : baseEnd_648775 < baseStart_648775 := by decide
  rcases family_descends (prefixWord ++ tailWord_648775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648786 : List Nat := [3, 2, 2, 1, 2, 3, 2, 5]
def baseStart_648786 : Nat := 118140960795 + 648786 * 2 ^ 59
def prefixEnd_648786 : Nat := 4983230072969 + 3 ^ 40 * 648786 * 2
def baseEnd_648786 : Nat := 98707869602371512738161

theorem tailTrace_648786 : CollatzResearch.WordTrace tailWord_648786 prefixEnd_648786 98707869602371512738161 := by
  unfold tailWord_648786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5915792356891650168091553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15775446285044400448244141 5915792356891650168091553)
  ·
    refine ⟨4436844267668737626068665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5915792356891650168091553 4436844267668737626068665)
    ·
      refine ⟨3327633200751553219551499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4436844267668737626068665 3327633200751553219551499)
      ·
        refine ⟨4991449801127329829327249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3327633200751553219551499 4991449801127329829327249)
        ·
          refine ⟨3743587350845497371995437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4991449801127329829327249 3743587350845497371995437)
          ·
            refine ⟨1403845256567061514498289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3743587350845497371995437 1403845256567061514498289)
            ·
              refine ⟨1052883942425296135873717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1403845256567061514498289 1052883942425296135873717)
              ·
                refine ⟨98707869602371512738161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1052883942425296135873717 98707869602371512738161)
                ·
                  rfl

theorem cell20_648786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_648786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648786 prefixEnd_648786 := by exact prefixLift 648786
  have htrace : WordTrace (prefixWord ++ tailWord_648786) baseStart_648786 baseEnd_648786 := by
    simpa [prefixWord, tailWord_648786, baseEnd_648786] using wordTrace_append hprefix tailTrace_648786
  have hstable : (prefixWord ++ tailWord_648786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648786).length < 2 ^ (prefixWord ++ tailWord_648786).sum := by decide
  have hdescent : baseEnd_648786 < baseStart_648786 := by decide
  rcases family_descends (prefixWord ++ tailWord_648786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648807 : List Nat := [1, 1, 5, 1, 1, 1, 4, 6]
def baseStart_648807 : Nat := 118140960795 + 648807 * 2 ^ 59
def prefixEnd_648807 : Nat := 4983230072969 + 3 ^ 40 * 648807 * 2
def baseEnd_648807 : Nat := 98711064593110599504799

theorem tailTrace_648807 : CollatzResearch.WordTrace tailWord_648807 prefixEnd_648807 98711064593110599504799 := by
  unfold tailWord_648807
  simp only [CollatzResearch.WordTrace]
  refine ⟨23663935360490521258880675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15775956906993680839253783 23663935360490521258880675)
  ·
    refine ⟨35495903040735781888321013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23663935360490521258880675 35495903040735781888321013)
    ·
      refine ⟨3327740910068979552030095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35495903040735781888321013 3327740910068979552030095)
      ·
        refine ⟨4991611365103469328045143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3327740910068979552030095 4991611365103469328045143)
        ·
          refine ⟨7487417047655203992067715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4991611365103469328045143 7487417047655203992067715)
          ·
            refine ⟨11231125571482805988101573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7487417047655203992067715 11231125571482805988101573)
            ·
              refine ⟨2105836044653026122769045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11231125571482805988101573 2105836044653026122769045)
              ·
                refine ⟨98711064593110599504799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2105836044653026122769045 98711064593110599504799)
                ·
                  rfl

theorem cell20_648807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_648807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648807 prefixEnd_648807 := by exact prefixLift 648807
  have htrace : WordTrace (prefixWord ++ tailWord_648807) baseStart_648807 baseEnd_648807 := by
    simpa [prefixWord, tailWord_648807, baseEnd_648807] using wordTrace_append hprefix tailTrace_648807
  have hstable : (prefixWord ++ tailWord_648807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648807).length < 2 ^ (prefixWord ++ tailWord_648807).sum := by decide
  have hdescent : baseEnd_648807 < baseStart_648807 := by decide
  rcases family_descends (prefixWord ++ tailWord_648807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648893 : List Nat := [1, 4, 1, 2, 1, 2, 1, 6, 2]
def baseStart_648893 : Nat := 118140960795 + 648893 * 2 ^ 59
def prefixEnd_648893 : Nat := 4983230072969 + 3 ^ 40 * 648893 * 2
def baseEnd_648893 : Nat := 296172446522697721647379

theorem tailTrace_648893 : CollatzResearch.WordTrace tailWord_648893 prefixEnd_648893 296172446522697721647379 := by
  unfold tailWord_648893
  simp only [CollatzResearch.WordTrace]
  refine ⟨23667072038178957946511333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15778048025452638631007555 23667072038178957946511333)
  ·
    refine ⟨4437576007158554614970875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23667072038178957946511333 4437576007158554614970875)
    ·
      refine ⟨6656364010737831922456313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4437576007158554614970875 6656364010737831922456313)
      ·
        refine ⟨4992273008053373941842235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6656364010737831922456313 4992273008053373941842235)
        ·
          refine ⟨7488409512080060912763353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4992273008053373941842235 7488409512080060912763353)
          ·
            refine ⟨5616307134060045684572515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7488409512080060912763353 5616307134060045684572515)
            ·
              refine ⟨8424460701090068526858773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5616307134060045684572515 8424460701090068526858773)
              ·
                refine ⟨394896595363596962196505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8424460701090068526858773 394896595363596962196505)
                ·
                  refine ⟨296172446522697721647379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394896595363596962196505 296172446522697721647379)
                  ·
                    rfl

theorem cell20_648893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_648893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648893 prefixEnd_648893 := by exact prefixLift 648893
  have htrace : WordTrace (prefixWord ++ tailWord_648893) baseStart_648893 baseEnd_648893 := by
    simpa [prefixWord, tailWord_648893, baseEnd_648893] using wordTrace_append hprefix tailTrace_648893
  have hstable : (prefixWord ++ tailWord_648893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648893).length < 2 ^ (prefixWord ++ tailWord_648893).sum := by decide
  have hdescent : baseEnd_648893 < baseStart_648893 := by decide
  rcases family_descends (prefixWord ++ tailWord_648893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648921 : List Nat := [1, 2, 1, 2, 3, 4, 1, 6]
def baseStart_648921 : Nat := 118140960795 + 648921 * 2 ^ 59
def prefixEnd_648921 : Nat := 4983230072969 + 3 ^ 40 * 648921 * 2
def baseEnd_648921 : Nat := 98728408828551356237977

theorem tailTrace_648921 : CollatzResearch.WordTrace tailWord_648921 prefixEnd_648921 98728408828551356237977 := by
  unfold tailWord_648921
  simp only [CollatzResearch.WordTrace]
  refine ⟨23668093282077518728530617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15778728854718345819020411 23668093282077518728530617)
  ·
    refine ⟨17751069961558139046397963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23668093282077518728530617 17751069961558139046397963)
    ·
      refine ⟨26626604942337208569596945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17751069961558139046397963 26626604942337208569596945)
      ·
        refine ⟨19969953706752906427197709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26626604942337208569596945 19969953706752906427197709)
        ·
          refine ⟨7488732640032339910199141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19969953706752906427197709 7488732640032339910199141)
          ·
            refine ⟨1404137370006063733162339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7488732640032339910199141 1404137370006063733162339)
            ·
              refine ⟨2106206055009095599743509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404137370006063733162339 2106206055009095599743509)
              ·
                refine ⟨98728408828551356237977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2106206055009095599743509 98728408828551356237977)
                ·
                  rfl

theorem cell20_648921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_648921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648921 prefixEnd_648921 := by exact prefixLift 648921
  have htrace : WordTrace (prefixWord ++ tailWord_648921) baseStart_648921 baseEnd_648921 := by
    simpa [prefixWord, tailWord_648921, baseEnd_648921] using wordTrace_append hprefix tailTrace_648921
  have hstable : (prefixWord ++ tailWord_648921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648921).length < 2 ^ (prefixWord ++ tailWord_648921).sum := by decide
  have hdescent : baseEnd_648921 < baseStart_648921 := by decide
  rcases family_descends (prefixWord ++ tailWord_648921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648928 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_648928 : Nat := 118140960795 + 648928 * 2 ^ 59
def prefixEnd_648928 : Nat := 4983230072969 + 3 ^ 40 * 648928 * 2
def baseEnd_648928 : Nat := 296188421476393155480569

theorem tailTrace_648928 : CollatzResearch.WordTrace tailWord_648928 prefixEnd_648928 296188421476393155480569 := by
  unfold tailWord_648928
  simp only [CollatzResearch.WordTrace]
  refine ⟨11834174296526079462017719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15778899062034772616023625 11834174296526079462017719)
  ·
    refine ⟨17751261444789119193026579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11834174296526079462017719 17751261444789119193026579)
    ·
      refine ⟨26626892167183678789539869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17751261444789119193026579 26626892167183678789539869)
      ·
        refine ⟨9985084562693879546077451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26626892167183678789539869 9985084562693879546077451)
        ·
          refine ⟨14977626844040819319116177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9985084562693879546077451 14977626844040819319116177)
          ·
            refine ⟨11233220133030614489337133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14977626844040819319116177 11233220133030614489337133)
            ·
              refine ⟨4212457549886480433501425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11233220133030614489337133 4212457549886480433501425)
              ·
                refine ⟨3159343162414860325126069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4212457549886480433501425 3159343162414860325126069)
                ·
                  refine ⟨296188421476393155480569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3159343162414860325126069 296188421476393155480569)
                  ·
                    rfl

theorem cell20_648928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_648928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648928 prefixEnd_648928 := by exact prefixLift 648928
  have htrace : WordTrace (prefixWord ++ tailWord_648928) baseStart_648928 baseEnd_648928 := by
    simpa [prefixWord, tailWord_648928, baseEnd_648928] using wordTrace_append hprefix tailTrace_648928
  have hstable : (prefixWord ++ tailWord_648928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648928).length < 2 ^ (prefixWord ++ tailWord_648928).sum := by decide
  have hdescent : baseEnd_648928 < baseStart_648928 := by decide
  rcases family_descends (prefixWord ++ tailWord_648928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648958 : List Nat := [4, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_648958 : Nat := 118140960795 + 648958 * 2 ^ 59
def prefixEnd_648958 : Nat := 4983230072969 + 3 ^ 40 * 648958 * 2
def baseEnd_648958 : Nat := 296202114293846384480447

theorem tailTrace_648958 : CollatzResearch.WordTrace tailWord_648958 prefixEnd_648958 296202114293846384480447 := by
  unfold tailWord_648958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2958680347867934255953441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15779628521962316031751685 2958680347867934255953441)
  ·
    refine ⟨2219010260900950691965081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2958680347867934255953441 2219010260900950691965081)
    ·
      refine ⟨1664257695675713018973811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2219010260900950691965081 1664257695675713018973811)
      ·
        refine ⟨2496386543513569528460717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1664257695675713018973811 2496386543513569528460717)
        ·
          refine ⟨936144953817588573172769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2496386543513569528460717 936144953817588573172769)
          ·
            refine ⟨702108715363191429879577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 936144953817588573172769 702108715363191429879577)
            ·
              refine ⟨526581536522393572409683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702108715363191429879577 526581536522393572409683)
              ·
                refine ⟨789872304783590358614525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526581536522393572409683 789872304783590358614525)
                ·
                  refine ⟨296202114293846384480447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789872304783590358614525 296202114293846384480447)
                  ·
                    rfl

theorem cell20_648958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_648958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648958 prefixEnd_648958 := by exact prefixLift 648958
  have htrace : WordTrace (prefixWord ++ tailWord_648958) baseStart_648958 baseEnd_648958 := by
    simpa [prefixWord, tailWord_648958, baseEnd_648958] using wordTrace_append hprefix tailTrace_648958
  have hstable : (prefixWord ++ tailWord_648958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648958).length < 2 ^ (prefixWord ++ tailWord_648958).sum := by decide
  have hdescent : baseEnd_648958 < baseStart_648958 := by decide
  rcases family_descends (prefixWord ++ tailWord_648958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648962 : List Nat := [3, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_648962 : Nat := 118140960795 + 648962 * 2 ^ 59
def prefixEnd_648962 : Nat := 4983230072969 + 3 ^ 40 * 648962 * 2
def baseEnd_648962 : Nat := 296203940002840148347097

theorem tailTrace_648962 : CollatzResearch.WordTrace tailWord_648962 prefixEnd_648962 296203940002840148347097 := by
  unfold tailWord_648962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5917397168732245682693285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15779725783285988487182093 5917397168732245682693285)
  ·
    refine ⟨1109511969137296065504991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5917397168732245682693285 1109511969137296065504991)
    ·
      refine ⟨1664267953705944098257487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1109511969137296065504991 1664267953705944098257487)
      ·
        refine ⟨2496401930558916147386231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1664267953705944098257487 2496401930558916147386231)
        ·
          refine ⟨3744602895838374221079347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2496401930558916147386231 3744602895838374221079347)
          ·
            refine ⟨5616904343757561331619021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3744602895838374221079347 5616904343757561331619021)
            ·
              refine ⟨2106339128909085499357133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5616904343757561331619021 2106339128909085499357133)
              ·
                refine ⟨789877173340907062258925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2106339128909085499357133 789877173340907062258925)
                ·
                  refine ⟨296203940002840148347097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789877173340907062258925 296203940002840148347097)
                  ·
                    rfl

theorem cell20_648962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_648962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_648962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_648962 prefixEnd_648962 := by exact prefixLift 648962
  have htrace : WordTrace (prefixWord ++ tailWord_648962) baseStart_648962 baseEnd_648962 := by
    simpa [prefixWord, tailWord_648962, baseEnd_648962] using wordTrace_append hprefix tailTrace_648962
  have hstable : (prefixWord ++ tailWord_648962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648962).length < 2 ^ (prefixWord ++ tailWord_648962).sum := by decide
  have hdescent : baseEnd_648962 < baseStart_648962 := by decide
  rcases family_descends (prefixWord ++ tailWord_648962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649000 : List Nat := [2, 1, 5, 1, 1, 3, 2, 2, 3]
def baseStart_649000 : Nat := 118140960795 + 649000 * 2 ^ 59
def prefixEnd_649000 : Nat := 4983230072969 + 3 ^ 40 * 649000 * 2
def baseEnd_649000 : Nat := 296221284238280905080275

theorem tailTrace_649000 : CollatzResearch.WordTrace tailWord_649000 prefixEnd_649000 296221284238280905080275 := by
  unfold tailWord_649000
  simp only [CollatzResearch.WordTrace]
  refine ⟨11835487324395657610328227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15780649765860876813770969 11835487324395657610328227)
  ·
    refine ⟨17753230986593486415492341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11835487324395657610328227 17753230986593486415492341)
    ·
      refine ⟨1664365404993139351452407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17753230986593486415492341 1664365404993139351452407)
      ·
        refine ⟨2496548107489709027178611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1664365404993139351452407 2496548107489709027178611)
        ·
          refine ⟨3744822161234563540767917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2496548107489709027178611 3744822161234563540767917)
          ·
            refine ⟨1404308310462961327787969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3744822161234563540767917 1404308310462961327787969)
            ·
              refine ⟨1053231232847220995840977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404308310462961327787969 1053231232847220995840977)
              ·
                refine ⟨789923424635415746880733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1053231232847220995840977 789923424635415746880733)
                ·
                  refine ⟨296221284238280905080275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789923424635415746880733 296221284238280905080275)
                  ·
                    rfl

theorem cell20_649000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_649000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649000 prefixEnd_649000 := by exact prefixLift 649000
  have htrace : WordTrace (prefixWord ++ tailWord_649000) baseStart_649000 baseEnd_649000 := by
    simpa [prefixWord, tailWord_649000, baseEnd_649000] using wordTrace_append hprefix tailTrace_649000
  have hstable : (prefixWord ++ tailWord_649000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649000).length < 2 ^ (prefixWord ++ tailWord_649000).sum := by decide
  have hdescent : baseEnd_649000 < baseStart_649000 := by decide
  rcases family_descends (prefixWord ++ tailWord_649000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649045 : List Nat := [1, 3, 2, 2, 2, 2, 1, 5, 2]
def baseStart_649045 : Nat := 118140960795 + 649045 * 2 ^ 59
def prefixEnd_649045 : Nat := 4983230072969 + 3 ^ 40 * 649045 * 2
def baseEnd_649045 : Nat := 296241823464460748580091

theorem tailTrace_649045 : CollatzResearch.WordTrace tailWord_649045 prefixEnd_649045 296241823464460748580091 := by
  unfold tailWord_649045
  simp only [CollatzResearch.WordTrace]
  refine ⟨23672615933628287906044589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15781743955752191937363059 23672615933628287906044589)
  ·
    refine ⟨8877230975110607964766721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23672615933628287906044589 8877230975110607964766721)
    ·
      refine ⟨6657923231332955973575041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8877230975110607964766721 6657923231332955973575041)
      ·
        refine ⟨4993442423499716980181281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6657923231332955973575041 4993442423499716980181281)
        ·
          refine ⟨3745081817624787735135961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4993442423499716980181281 3745081817624787735135961)
          ·
            refine ⟨2808811363218590801351971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3745081817624787735135961 2808811363218590801351971)
            ·
              refine ⟨4213217044827886202027957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2808811363218590801351971 4213217044827886202027957)
              ·
                refine ⟨394989097952614331440121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4213217044827886202027957 394989097952614331440121)
                ·
                  refine ⟨296241823464460748580091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394989097952614331440121 296241823464460748580091)
                  ·
                    rfl

theorem cell20_649045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_649045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649045 prefixEnd_649045 := by exact prefixLift 649045
  have htrace : WordTrace (prefixWord ++ tailWord_649045) baseStart_649045 baseEnd_649045 := by
    simpa [prefixWord, tailWord_649045, baseEnd_649045] using wordTrace_append hprefix tailTrace_649045
  have hstable : (prefixWord ++ tailWord_649045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649045).length < 2 ^ (prefixWord ++ tailWord_649045).sum := by decide
  have hdescent : baseEnd_649045 < baseStart_649045 := by decide
  rcases family_descends (prefixWord ++ tailWord_649045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649049 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 6]
def baseStart_649049 : Nat := 118140960795 + 649049 * 2 ^ 59
def prefixEnd_649049 : Nat := 4983230072969 + 3 ^ 40 * 649049 * 2
def baseEnd_649049 : Nat := 296243649173454512446741

theorem tailTrace_649049 : CollatzResearch.WordTrace tailWord_649049 prefixEnd_649049 296243649173454512446741 := by
  unfold tailWord_649049
  simp only [CollatzResearch.WordTrace]
  refine ⟨23672761825613796589190201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15781841217075864392793467 23672761825613796589190201)
  ·
    refine ⟨17754571369210347441892651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23672761825613796589190201 17754571369210347441892651)
    ·
      refine ⟨26631857053815521162838977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17754571369210347441892651 26631857053815521162838977)
      ·
        refine ⟨19973892790361640872129233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26631857053815521162838977 19973892790361640872129233)
        ·
          refine ⟨14980419592771230654096925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19973892790361640872129233 14980419592771230654096925)
          ·
            refine ⟨5617657347289211495286347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14980419592771230654096925 5617657347289211495286347)
            ·
              refine ⟨8426486020933817242929521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5617657347289211495286347 8426486020933817242929521)
              ·
                refine ⟨6319864515700362932197141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8426486020933817242929521 6319864515700362932197141)
                ·
                  refine ⟨296243649173454512446741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6319864515700362932197141 296243649173454512446741)
                  ·
                    rfl

theorem cell20_649049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_649049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649049 prefixEnd_649049 := by exact prefixLift 649049
  have htrace : WordTrace (prefixWord ++ tailWord_649049) baseStart_649049 baseEnd_649049 := by
    simpa [prefixWord, tailWord_649049, baseEnd_649049] using wordTrace_append hprefix tailTrace_649049
  have hstable : (prefixWord ++ tailWord_649049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649049).length < 2 ^ (prefixWord ++ tailWord_649049).sum := by decide
  have hdescent : baseEnd_649049 < baseStart_649049 := by decide
  rcases family_descends (prefixWord ++ tailWord_649049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649052 : List Nat := [2, 2, 4, 2, 2, 1, 7]
def baseStart_649052 : Nat := 118140960795 + 649052 * 2 ^ 59
def prefixEnd_649052 : Nat := 4983230072969 + 3 ^ 40 * 649052 * 2
def baseEnd_649052 : Nat := 32916113161688870594081

theorem tailTrace_649052 : CollatzResearch.WordTrace tailWord_649052 prefixEnd_649052 32916113161688870594081 := by
  unfold tailWord_649052
  simp only [CollatzResearch.WordTrace]
  refine ⟨11836435622301464050774705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15781914163068618734366273 11836435622301464050774705)
  ·
    refine ⟨8877326716726098038081029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11836435622301464050774705 8877326716726098038081029)
    ·
      refine ⟨1664498759386143382140193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8877326716726098038081029 1664498759386143382140193)
      ·
        refine ⟨1248374069539607536605145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1664498759386143382140193 1248374069539607536605145)
        ·
          refine ⟨936280552154705652453859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1248374069539607536605145 936280552154705652453859)
          ·
            refine ⟨1404420828232058478680789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936280552154705652453859 1404420828232058478680789)
            ·
              refine ⟨32916113161688870594081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1404420828232058478680789 32916113161688870594081)
              ·
                rfl

theorem cell20_649052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 7].length) (baseStart_649052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649052 prefixEnd_649052 := by exact prefixLift 649052
  have htrace : WordTrace (prefixWord ++ tailWord_649052) baseStart_649052 baseEnd_649052 := by
    simpa [prefixWord, tailWord_649052, baseEnd_649052] using wordTrace_append hprefix tailTrace_649052
  have hstable : (prefixWord ++ tailWord_649052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649052).length < 2 ^ (prefixWord ++ tailWord_649052).sum := by decide
  have hdescent : baseEnd_649052 < baseStart_649052 := by decide
  rcases family_descends (prefixWord ++ tailWord_649052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649059 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 5]
def baseStart_649059 : Nat := 118140960795 + 649059 * 2 ^ 59
def prefixEnd_649059 : Nat := 4983230072969 + 3 ^ 40 * 649059 * 2
def baseEnd_649059 : Nat := 296248213445938922113367

theorem tailTrace_649059 : CollatzResearch.WordTrace tailWord_649059 prefixEnd_649059 296248213445938922113367 := by
  unfold tailWord_649059
  simp only [CollatzResearch.WordTrace]
  refine ⟨23673126555577568297054231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15782084370385045531369487 23673126555577568297054231)
  ·
    refine ⟨35509689833366352445581347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23673126555577568297054231 35509689833366352445581347)
    ·
      refine ⟨53264534750049528668372021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35509689833366352445581347 53264534750049528668372021)
      ·
        refine ⟨4993550132817143312659877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53264534750049528668372021 4993550132817143312659877)
        ·
          refine ⟨936290649903214371123727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4993550132817143312659877 936290649903214371123727)
          ·
            refine ⟨1404435974854821556685591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936290649903214371123727 1404435974854821556685591)
            ·
              refine ⟨2106653962282232335028387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404435974854821556685591 2106653962282232335028387)
              ·
                refine ⟨3159980943423348502542581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106653962282232335028387 3159980943423348502542581)
                ·
                  refine ⟨296248213445938922113367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3159980943423348502542581 296248213445938922113367)
                  ·
                    rfl

theorem cell20_649059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 5].length) (baseStart_649059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649059 prefixEnd_649059 := by exact prefixLift 649059
  have htrace : WordTrace (prefixWord ++ tailWord_649059) baseStart_649059 baseEnd_649059 := by
    simpa [prefixWord, tailWord_649059, baseEnd_649059] using wordTrace_append hprefix tailTrace_649059
  have hstable : (prefixWord ++ tailWord_649059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649059).length < 2 ^ (prefixWord ++ tailWord_649059).sum := by decide
  have hdescent : baseEnd_649059 < baseStart_649059 := by decide
  rcases family_descends (prefixWord ++ tailWord_649059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649086 : List Nat := [4, 2, 3, 1, 1, 3, 2, 4]
def baseStart_649086 : Nat := 118140960795 + 649086 * 2 ^ 59
def prefixEnd_649086 : Nat := 4983230072969 + 3 ^ 40 * 649086 * 2
def baseEnd_649086 : Nat := 98753512327215609404419

theorem tailTrace_649086 : CollatzResearch.WordTrace tailWord_649086 prefixEnd_649086 98753512327215609404419 := by
  unfold tailWord_649086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959263915809968988535889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15782740884319834605524741 2959263915809968988535889)
  ·
    refine ⟨2219447936857476741401917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2959263915809968988535889 2219447936857476741401917)
    ·
      refine ⟨832292976321553778025719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2219447936857476741401917 832292976321553778025719)
      ·
        refine ⟨1248439464482330667038579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832292976321553778025719 1248439464482330667038579)
        ·
          refine ⟨1872659196723496000557869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248439464482330667038579 1872659196723496000557869)
          ·
            refine ⟨702247198771311000209201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1872659196723496000557869 702247198771311000209201)
            ·
              refine ⟨526685399078483250156901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702247198771311000209201 526685399078483250156901)
              ·
                refine ⟨98753512327215609404419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 526685399078483250156901 98753512327215609404419)
                ·
                  rfl

theorem cell20_649086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_649086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649086 prefixEnd_649086 := by exact prefixLift 649086
  have htrace : WordTrace (prefixWord ++ tailWord_649086) baseStart_649086 baseEnd_649086 := by
    simpa [prefixWord, tailWord_649086, baseEnd_649086] using wordTrace_append hprefix tailTrace_649086
  have hstable : (prefixWord ++ tailWord_649086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649086).length < 2 ^ (prefixWord ++ tailWord_649086).sum := by decide
  have hdescent : baseEnd_649086 < baseStart_649086 := by decide
  rcases family_descends (prefixWord ++ tailWord_649086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649111 : List Nat := [1, 1, 3, 3, 1, 5, 6]
def baseStart_649111 : Nat := 118140960795 + 649111 * 2 ^ 59
def prefixEnd_649111 : Nat := 4983230072969 + 3 ^ 40 * 649111 * 2
def baseEnd_649111 : Nat := 32919105295873094708869

theorem tailTrace_649111 : CollatzResearch.WordTrace tailWord_649111 prefixEnd_649111 32919105295873094708869 := by
  unfold tailWord_649111
  simp only [CollatzResearch.WordTrace]
  refine ⟨23675023151389181177947187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15783348767592787451964791 23675023151389181177947187)
  ·
    refine ⟨35512534727083771766920781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23675023151389181177947187 35512534727083771766920781)
    ·
      refine ⟨13317200522656414412595293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35512534727083771766920781 13317200522656414412595293)
      ·
        refine ⟨4993950195996155404723235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13317200522656414412595293 4993950195996155404723235)
        ·
          refine ⟨7490925293994233107084853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4993950195996155404723235 7490925293994233107084853)
          ·
            refine ⟨702274246311959353789205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7490925293994233107084853 702274246311959353789205)
            ·
              refine ⟨32919105295873094708869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 702274246311959353789205 32919105295873094708869)
              ·
                rfl

theorem cell20_649111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 6].length) (baseStart_649111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649111 prefixEnd_649111 := by exact prefixLift 649111
  have htrace : WordTrace (prefixWord ++ tailWord_649111) baseStart_649111 baseEnd_649111 := by
    simpa [prefixWord, tailWord_649111, baseEnd_649111] using wordTrace_append hprefix tailTrace_649111
  have hstable : (prefixWord ++ tailWord_649111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649111).length < 2 ^ (prefixWord ++ tailWord_649111).sum := by decide
  have hdescent : baseEnd_649111 < baseStart_649111 := by decide
  rcases family_descends (prefixWord ++ tailWord_649111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649149 : List Nat := [1, 4, 1, 2, 3, 1, 2, 6]
def baseStart_649149 : Nat := 118140960795 + 649149 * 2 ^ 59
def prefixEnd_649149 : Nat := 4983230072969 + 3 ^ 40 * 649149 * 2
def baseEnd_649149 : Nat := 98763097299432869704333

theorem tailTrace_649149 : CollatzResearch.WordTrace tailWord_649149 prefixEnd_649149 98763097299432869704333 := by
  unfold tailWord_649149
  simp only [CollatzResearch.WordTrace]
  refine ⟨23676409125251513667830501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15784272750167675778553667 23676409125251513667830501)
  ·
    refine ⟨4439326710984658812718219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23676409125251513667830501 4439326710984658812718219)
    ·
      refine ⟨6658990066476988219077329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4439326710984658812718219 6658990066476988219077329)
      ·
        refine ⟨4994242549857741164307997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6658990066476988219077329 4994242549857741164307997)
        ·
          refine ⟨1872840956196652936615499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4994242549857741164307997 1872840956196652936615499)
          ·
            refine ⟨2809261434294979404923249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872840956196652936615499 2809261434294979404923249)
            ·
              refine ⟨2106946075721234553692437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2809261434294979404923249 2106946075721234553692437)
              ·
                refine ⟨98763097299432869704333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2106946075721234553692437 98763097299432869704333)
                ·
                  rfl

theorem cell20_649149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_649149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649149 prefixEnd_649149 := by exact prefixLift 649149
  have htrace : WordTrace (prefixWord ++ tailWord_649149) baseStart_649149 baseEnd_649149 := by
    simpa [prefixWord, tailWord_649149, baseEnd_649149] using wordTrace_append hprefix tailTrace_649149
  have hstable : (prefixWord ++ tailWord_649149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649149).length < 2 ^ (prefixWord ++ tailWord_649149).sum := by decide
  have hdescent : baseEnd_649149 < baseStart_649149 := by decide
  rcases family_descends (prefixWord ++ tailWord_649149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649173 : List Nat := [1, 3, 2, 3, 2, 1, 1, 4, 3]
def baseStart_649173 : Nat := 118140960795 + 649173 * 2 ^ 59
def prefixEnd_649173 : Nat := 4983230072969 + 3 ^ 40 * 649173 * 2
def baseEnd_649173 : Nat := 296300246152261192312901

theorem tailTrace_649173 : CollatzResearch.WordTrace tailWord_649173 prefixEnd_649173 296300246152261192312901 := by
  unfold tailWord_649173
  simp only [CollatzResearch.WordTrace]
  refine ⟨23677284477164565766704173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15784856318109710511136115 23677284477164565766704173)
  ·
    refine ⟨8878981678936712162514065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23677284477164565766704173 8878981678936712162514065)
    ·
      refine ⟨6659236259202534121885549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8878981678936712162514065 6659236259202534121885549)
      ·
        refine ⟨2497213597200950295707081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6659236259202534121885549 2497213597200950295707081)
        ·
          refine ⟨1872910197900712721780311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2497213597200950295707081 1872910197900712721780311)
          ·
            refine ⟨2809365296851069082670467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872910197900712721780311 2809365296851069082670467)
            ·
              refine ⟨4214047945276603624005701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809365296851069082670467 4214047945276603624005701)
              ·
                refine ⟨790133989739363179501069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4214047945276603624005701 790133989739363179501069)
                ·
                  refine ⟨296300246152261192312901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790133989739363179501069 296300246152261192312901)
                  ·
                    rfl

theorem cell20_649173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_649173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649173 prefixEnd_649173 := by exact prefixLift 649173
  have htrace : WordTrace (prefixWord ++ tailWord_649173) baseStart_649173 baseEnd_649173 := by
    simpa [prefixWord, tailWord_649173, baseEnd_649173] using wordTrace_append hprefix tailTrace_649173
  have hstable : (prefixWord ++ tailWord_649173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649173).length < 2 ^ (prefixWord ++ tailWord_649173).sum := by decide
  have hdescent : baseEnd_649173 < baseStart_649173 := by decide
  rcases family_descends (prefixWord ++ tailWord_649173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649187 : List Nat := [1, 1, 1, 6, 1, 2, 3, 5]
def baseStart_649187 : Nat := 118140960795 + 649187 * 2 ^ 59
def prefixEnd_649187 : Nat := 4983230072969 + 3 ^ 40 * 649187 * 2
def baseEnd_649187 : Nat := 98768878711246455282059

theorem tailTrace_649187 : CollatzResearch.WordTrace tailWord_649187 prefixEnd_649187 98768878711246455282059 := by
  unfold tailWord_649187
  simp only [CollatzResearch.WordTrace]
  refine ⟨23677795099113846157713815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15785196732742564105142543 23677795099113846157713815)
  ·
    refine ⟨35516692648670769236570723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23677795099113846157713815 35516692648670769236570723)
    ·
      refine ⟨53275038973006153854856085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35516692648670769236570723 53275038973006153854856085)
      ·
        refine ⟨2497267451859663461946379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53275038973006153854856085 2497267451859663461946379)
        ·
          refine ⟨3745901177789495192919569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2497267451859663461946379 3745901177789495192919569)
          ·
            refine ⟨2809425883342121394689677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3745901177789495192919569 2809425883342121394689677)
            ·
              refine ⟨1053534706253295523008629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2809425883342121394689677 1053534706253295523008629)
              ·
                refine ⟨98768878711246455282059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1053534706253295523008629 98768878711246455282059)
                ·
                  rfl

theorem cell20_649187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_649187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649187 prefixEnd_649187 := by exact prefixLift 649187
  have htrace : WordTrace (prefixWord ++ tailWord_649187) baseStart_649187 baseEnd_649187 := by
    simpa [prefixWord, tailWord_649187, baseEnd_649187] using wordTrace_append hprefix tailTrace_649187
  have hstable : (prefixWord ++ tailWord_649187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649187).length < 2 ^ (prefixWord ++ tailWord_649187).sum := by decide
  have hdescent : baseEnd_649187 < baseStart_649187 := by decide
  rcases family_descends (prefixWord ++ tailWord_649187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649208 : List Nat := [2, 1, 2, 1, 1, 3, 2, 8]
def baseStart_649208 : Nat := 118140960795 + 649208 * 2 ^ 59
def prefixEnd_649208 : Nat := 4983230072969 + 3 ^ 40 * 649208 * 2
def baseEnd_649208 : Nat := 98772073701985542048697

theorem tailTrace_649208 : CollatzResearch.WordTrace tailWord_649208 prefixEnd_649208 98772073701985542048697 := by
  unfold tailWord_649208
  simp only [CollatzResearch.WordTrace]
  refine ⟨11839280516018883372114139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15785707354691844496152185 11839280516018883372114139)
  ·
    refine ⟨17758920774028325058171209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11839280516018883372114139 17758920774028325058171209)
    ·
      refine ⟨13319190580521243793628407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17758920774028325058171209 13319190580521243793628407)
      ·
        refine ⟨19978785870781865690442611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13319190580521243793628407 19978785870781865690442611)
        ·
          refine ⟨29968178806172798535663917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19978785870781865690442611 29968178806172798535663917)
          ·
            refine ⟨11238067052314799450873969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29968178806172798535663917 11238067052314799450873969)
            ·
              refine ⟨8428550289236099588155477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11238067052314799450873969 8428550289236099588155477)
              ·
                refine ⟨98772073701985542048697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8428550289236099588155477 98772073701985542048697)
                ·
                  rfl

theorem cell20_649208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_649208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649208 prefixEnd_649208 := by exact prefixLift 649208
  have htrace : WordTrace (prefixWord ++ tailWord_649208) baseStart_649208 baseEnd_649208 := by
    simpa [prefixWord, tailWord_649208, baseEnd_649208] using wordTrace_append hprefix tailTrace_649208
  have hstable : (prefixWord ++ tailWord_649208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649208).length < 2 ^ (prefixWord ++ tailWord_649208).sum := by decide
  have hdescent : baseEnd_649208 < baseStart_649208 := by decide
  rcases family_descends (prefixWord ++ tailWord_649208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649214 : List Nat := [4, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_649214 : Nat := 118140960795 + 649214 * 2 ^ 59
def prefixEnd_649214 : Nat := 4983230072969 + 3 ^ 40 * 649214 * 2
def baseEnd_649214 : Nat := 296318959669447271946067

theorem tailTrace_649214 : CollatzResearch.WordTrace tailWord_649214 prefixEnd_649214 296318959669447271946067 := by
  unfold tailWord_649214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959847483752003721118337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15785853246677353179297797 2959847483752003721118337)
  ·
    refine ⟨2219885612814002790838753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2959847483752003721118337 2219885612814002790838753)
    ·
      refine ⟨1664914209610502093129065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2219885612814002790838753 1664914209610502093129065)
      ·
        refine ⟨1248685657207876569846799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1664914209610502093129065 1248685657207876569846799)
        ·
          refine ⟨1873028485811814854770199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248685657207876569846799 1873028485811814854770199)
          ·
            refine ⟨2809542728717722282155299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873028485811814854770199 2809542728717722282155299)
            ·
              refine ⟨4214314093076583423232949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809542728717722282155299 4214314093076583423232949)
              ·
                refine ⟨395091946225929695928089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4214314093076583423232949 395091946225929695928089)
                ·
                  refine ⟨296318959669447271946067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395091946225929695928089 296318959669447271946067)
                  ·
                    rfl

theorem cell20_649214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_649214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649214 prefixEnd_649214 := by exact prefixLift 649214
  have htrace : WordTrace (prefixWord ++ tailWord_649214) baseStart_649214 baseEnd_649214 := by
    simpa [prefixWord, tailWord_649214, baseEnd_649214] using wordTrace_append hprefix tailTrace_649214
  have hstable : (prefixWord ++ tailWord_649214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649214).length < 2 ^ (prefixWord ++ tailWord_649214).sum := by decide
  have hdescent : baseEnd_649214 < baseStart_649214 := by decide
  rcases family_descends (prefixWord ++ tailWord_649214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649294 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_649294 : Nat := 118140960795 + 649294 * 2 ^ 59
def prefixEnd_649294 : Nat := 4983230072969 + 3 ^ 40 * 649294 * 2
def baseEnd_649294 : Nat := 296355473849322549279073

theorem tailTrace_649294 : CollatzResearch.WordTrace tailWord_649294 prefixEnd_649294 296355473849322549279073 := by
  unfold tailWord_649294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2960212213715775428982367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15787798473150802287905957 2960212213715775428982367)
  ·
    refine ⟨4440318320573663143473551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2960212213715775428982367 4440318320573663143473551)
    ·
      refine ⟨6660477480860494715210327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4440318320573663143473551 6660477480860494715210327)
      ·
        refine ⟨9990716221290742072815491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6660477480860494715210327 9990716221290742072815491)
        ·
          refine ⟨14986074331936113109223237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9990716221290742072815491 14986074331936113109223237)
          ·
            refine ⟨2809888937238021207979357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14986074331936113109223237 2809888937238021207979357)
            ·
              refine ⟨1053708351464257952992259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2809888937238021207979357 1053708351464257952992259)
              ·
                refine ⟨1580562527196386929488389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053708351464257952992259 1580562527196386929488389)
                ·
                  refine ⟨296355473849322549279073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1580562527196386929488389 296355473849322549279073)
                  ·
                    rfl

theorem cell20_649294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_649294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649294 prefixEnd_649294 := by exact prefixLift 649294
  have htrace : WordTrace (prefixWord ++ tailWord_649294) baseStart_649294 baseEnd_649294 := by
    simpa [prefixWord, tailWord_649294, baseEnd_649294] using wordTrace_append hprefix tailTrace_649294
  have hstable : (prefixWord ++ tailWord_649294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649294).length < 2 ^ (prefixWord ++ tailWord_649294).sum := by decide
  have hdescent : baseEnd_649294 < baseStart_649294 := by decide
  rcases family_descends (prefixWord ++ tailWord_649294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649301 : List Nat := [1, 3, 2, 2, 1, 4, 2, 5]
def baseStart_649301 : Nat := 118140960795 + 649301 * 2 ^ 59
def prefixEnd_649301 : Nat := 4983230072969 + 3 ^ 40 * 649301 * 2
def baseEnd_649301 : Nat := 98786222946687212015237

theorem tailTrace_649301 : CollatzResearch.WordTrace tailWord_649301 prefixEnd_649301 98786222946687212015237 := by
  unfold tailWord_649301
  simp only [CollatzResearch.WordTrace]
  refine ⟨23681953020700843627363757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15787968680467229084909171 23681953020700843627363757)
  ·
    refine ⟨8880732382762816360261409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23681953020700843627363757 8880732382762816360261409)
    ·
      refine ⟨6660549287072112270196057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8880732382762816360261409 6660549287072112270196057)
      ·
        refine ⟨4995411965304084202647043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6660549287072112270196057 4995411965304084202647043)
        ·
          refine ⟨7493117947956126303970565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4995411965304084202647043 7493117947956126303970565)
          ·
            refine ⟨1404959615241773681994481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7493117947956126303970565 1404959615241773681994481)
            ·
              refine ⟨1053719711431330261495861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404959615241773681994481 1053719711431330261495861)
              ·
                refine ⟨98786222946687212015237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1053719711431330261495861 98786222946687212015237)
                ·
                  rfl

theorem cell20_649301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_649301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649301 prefixEnd_649301 := by exact prefixLift 649301
  have htrace : WordTrace (prefixWord ++ tailWord_649301) baseStart_649301 baseEnd_649301 := by
    simpa [prefixWord, tailWord_649301, baseEnd_649301] using wordTrace_append hprefix tailTrace_649301
  have hstable : (prefixWord ++ tailWord_649301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649301).length < 2 ^ (prefixWord ++ tailWord_649301).sum := by decide
  have hdescent : baseEnd_649301 < baseStart_649301 := by decide
  rcases family_descends (prefixWord ++ tailWord_649301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649304 : List Nat := [2, 1, 2, 2, 1, 6, 2, 1, 3]
def baseStart_649304 : Nat := 118140960795 + 649304 * 2 ^ 59
def prefixEnd_649304 : Nat := 4983230072969 + 3 ^ 40 * 649304 * 2
def baseEnd_649304 : Nat := 296360038121806958945699

theorem tailTrace_649304 : CollatzResearch.WordTrace tailWord_649304 prefixEnd_649304 296360038121806958945699 := by
  unfold tailWord_649304
  simp only [CollatzResearch.WordTrace]
  refine ⟨11841031219844987569861483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15788041626459983426481977 11841031219844987569861483)
  ·
    refine ⟨17761546829767481354792225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11841031219844987569861483 17761546829767481354792225)
    ·
      refine ⟨13321160122325611016094169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17761546829767481354792225 13321160122325611016094169)
      ·
        refine ⟨9990870091744208262070627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13321160122325611016094169 9990870091744208262070627)
        ·
          refine ⟨14986305137616312393105941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9990870091744208262070627 14986305137616312393105941)
          ·
            refine ⟨702483053325764643426841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14986305137616312393105941 702483053325764643426841)
            ·
              refine ⟨526862289994323482570131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702483053325764643426841 526862289994323482570131)
              ·
                refine ⟨790293434991485223855197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526862289994323482570131 790293434991485223855197)
                ·
                  refine ⟨296360038121806958945699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790293434991485223855197 296360038121806958945699)
                  ·
                    rfl

theorem cell20_649304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_649304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649304 prefixEnd_649304 := by exact prefixLift 649304
  have htrace : WordTrace (prefixWord ++ tailWord_649304) baseStart_649304 baseEnd_649304 := by
    simpa [prefixWord, tailWord_649304, baseEnd_649304] using wordTrace_append hprefix tailTrace_649304
  have hstable : (prefixWord ++ tailWord_649304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649304).length < 2 ^ (prefixWord ++ tailWord_649304).sum := by decide
  have hdescent : baseEnd_649304 < baseStart_649304 := by decide
  rcases family_descends (prefixWord ++ tailWord_649304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649315 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 4]
def baseStart_649315 : Nat := 118140960795 + 649315 * 2 ^ 59
def prefixEnd_649315 : Nat := 4983230072969 + 3 ^ 40 * 649315 * 2
def baseEnd_649315 : Nat := 296365058821539809578987

theorem tailTrace_649315 : CollatzResearch.WordTrace tailWord_649315 prefixEnd_649315 296365058821539809578987 := by
  unfold tailWord_649315
  simp only [CollatzResearch.WordTrace]
  refine ⟨23682463642650124018373399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15788309095100082678915599 23682463642650124018373399)
  ·
    refine ⟨35523695463975186027560099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23682463642650124018373399 35523695463975186027560099)
    ·
      refine ⟨53285543195962779041340149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35523695463975186027560099 53285543195962779041340149)
      ·
        refine ⟨4995519674621510535125639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53285543195962779041340149 4995519674621510535125639)
        ·
          refine ⟨7493279511932265802688459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4995519674621510535125639 7493279511932265802688459)
          ·
            refine ⟨11239919267898398704032689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7493279511932265802688459 11239919267898398704032689)
            ·
              refine ⟨8429939450923799028024517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11239919267898398704032689 8429939450923799028024517)
              ·
                refine ⟨1580613647048212317754597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8429939450923799028024517 1580613647048212317754597)
                ·
                  refine ⟨296365058821539809578987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1580613647048212317754597 296365058821539809578987)
                  ·
                    rfl

theorem cell20_649315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_649315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649315 prefixEnd_649315 := by exact prefixLift 649315
  have htrace : WordTrace (prefixWord ++ tailWord_649315) baseStart_649315 baseEnd_649315 := by
    simpa [prefixWord, tailWord_649315, baseEnd_649315] using wordTrace_append hprefix tailTrace_649315
  have hstable : (prefixWord ++ tailWord_649315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649315).length < 2 ^ (prefixWord ++ tailWord_649315).sum := by decide
  have hdescent : baseEnd_649315 < baseStart_649315 := by decide
  rcases family_descends (prefixWord ++ tailWord_649315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649345 : List Nat := [1, 2, 4, 2, 3, 2, 2, 2, 2]
def baseStart_649345 : Nat := 118140960795 + 649345 * 2 ^ 59
def prefixEnd_649345 : Nat := 4983230072969 + 3 ^ 40 * 649345 * 2
def baseEnd_649345 : Nat := 296378751638993038578865

theorem tailTrace_649345 : CollatzResearch.WordTrace tailWord_649345 prefixEnd_649345 296378751638993038578865 := by
  unfold tailWord_649345
  simp only [CollatzResearch.WordTrace]
  refine ⟨23683557832541439141965489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15789038555027626094643659 23683557832541439141965489)
  ·
    refine ⟨17762668374406079356474117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23683557832541439141965489 17762668374406079356474117)
    ·
      refine ⟨3330500320201139879338897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17762668374406079356474117 3330500320201139879338897)
      ·
        refine ⟨2497875240150854909504173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3330500320201139879338897 2497875240150854909504173)
        ·
          refine ⟨936703215056570591064065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2497875240150854909504173 936703215056570591064065)
          ·
            refine ⟨702527411292427943298049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 936703215056570591064065 702527411292427943298049)
            ·
              refine ⟨526895558469320957473537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702527411292427943298049 526895558469320957473537)
              ·
                refine ⟨395171668851990718105153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526895558469320957473537 395171668851990718105153)
                ·
                  refine ⟨296378751638993038578865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395171668851990718105153 296378751638993038578865)
                  ·
                    rfl

theorem cell20_649345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 2].length) (baseStart_649345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649345 prefixEnd_649345 := by exact prefixLift 649345
  have htrace : WordTrace (prefixWord ++ tailWord_649345) baseStart_649345 baseEnd_649345 := by
    simpa [prefixWord, tailWord_649345, baseEnd_649345] using wordTrace_append hprefix tailTrace_649345
  have hstable : (prefixWord ++ tailWord_649345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649345).length < 2 ^ (prefixWord ++ tailWord_649345).sum := by decide
  have hdescent : baseEnd_649345 < baseStart_649345 := by decide
  rcases family_descends (prefixWord ++ tailWord_649345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649349 : List Nat := [1, 3, 1, 1, 5, 2, 1, 4, 2]
def baseStart_649349 : Nat := 118140960795 + 649349 * 2 ^ 59
def prefixEnd_649349 : Nat := 4983230072969 + 3 ^ 40 * 649349 * 2
def baseEnd_649349 : Nat := 296380577347986802445515

theorem tailTrace_649349 : CollatzResearch.WordTrace tailWord_649349 prefixEnd_649349 296380577347986802445515 := by
  unfold tailWord_649349
  simp only [CollatzResearch.WordTrace]
  refine ⟨23683703724526947825111101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15789135816351298550074067 23683703724526947825111101)
  ·
    refine ⟨8881388896697605434416663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23683703724526947825111101 8881388896697605434416663)
    ·
      refine ⟨13322083345046408151624995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8881388896697605434416663 13322083345046408151624995)
      ·
        refine ⟨19983125017569612227437493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13322083345046408151624995 19983125017569612227437493)
        ·
          refine ⟨1873417970397151146322265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19983125017569612227437493 1873417970397151146322265)
          ·
            refine ⟨1405063477797863359741699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1873417970397151146322265 1405063477797863359741699)
            ·
              refine ⟨2107595216696795039612549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405063477797863359741699 2107595216696795039612549)
              ·
                refine ⟨395174103130649069927353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2107595216696795039612549 395174103130649069927353)
                ·
                  refine ⟨296380577347986802445515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395174103130649069927353 296380577347986802445515)
                  ·
                    rfl

theorem cell20_649349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_649349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649349 prefixEnd_649349 := by exact prefixLift 649349
  have htrace : WordTrace (prefixWord ++ tailWord_649349) baseStart_649349 baseEnd_649349 := by
    simpa [prefixWord, tailWord_649349, baseEnd_649349] using wordTrace_append hprefix tailTrace_649349
  have hstable : (prefixWord ++ tailWord_649349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649349).length < 2 ^ (prefixWord ++ tailWord_649349).sum := by decide
  have hdescent : baseEnd_649349 < baseStart_649349 := by decide
  rcases family_descends (prefixWord ++ tailWord_649349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649353 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 4]
def baseStart_649353 : Nat := 118140960795 + 649353 * 2 ^ 59
def prefixEnd_649353 : Nat := 4983230072969 + 3 ^ 40 * 649353 * 2
def baseEnd_649353 : Nat := 296382403056980566312165

theorem tailTrace_649353 : CollatzResearch.WordTrace tailWord_649353 prefixEnd_649353 296382403056980566312165 := by
  unfold tailWord_649353
  simp only [CollatzResearch.WordTrace]
  refine ⟨23683849616512456508256713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15789233077674971005504475 23683849616512456508256713)
  ·
    refine ⟨17762887212384342381192535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23683849616512456508256713 17762887212384342381192535)
    ·
      refine ⟨26644330818576513571788803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17762887212384342381192535 26644330818576513571788803)
      ·
        refine ⟨39966496227864770357683205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26644330818576513571788803 39966496227864770357683205)
        ·
          refine ⟨7493718042724644442065601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39966496227864770357683205 7493718042724644442065601)
          ·
            refine ⟨5620288532043483331549201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7493718042724644442065601 5620288532043483331549201)
            ·
              refine ⟨4215216399032612498661901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5620288532043483331549201 4215216399032612498661901)
              ·
                refine ⟨1580706149637229686998213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4215216399032612498661901 1580706149637229686998213)
                ·
                  refine ⟨296382403056980566312165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1580706149637229686998213 296382403056980566312165)
                  ·
                    rfl

theorem cell20_649353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_649353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649353 prefixEnd_649353 := by exact prefixLift 649353
  have htrace : WordTrace (prefixWord ++ tailWord_649353) baseStart_649353 baseEnd_649353 := by
    simpa [prefixWord, tailWord_649353, baseEnd_649353] using wordTrace_append hprefix tailTrace_649353
  have hstable : (prefixWord ++ tailWord_649353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649353).length < 2 ^ (prefixWord ++ tailWord_649353).sum := by decide
  have hdescent : baseEnd_649353 < baseStart_649353 := by decide
  rcases family_descends (prefixWord ++ tailWord_649353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649397 : List Nat := [1, 3, 3, 4, 1, 2, 1, 2, 3]
def baseStart_649397 : Nat := 118140960795 + 649397 * 2 ^ 59
def prefixEnd_649397 : Nat := 4983230072969 + 3 ^ 40 * 649397 * 2
def baseEnd_649397 : Nat := 296402485855911968845319

theorem tailTrace_649397 : CollatzResearch.WordTrace tailWord_649397 prefixEnd_649397 296402485855911968845319 := by
  unfold tailWord_649397
  simp only [CollatzResearch.WordTrace]
  refine ⟨23685454428353052022858445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15790302952235368015238963 23685454428353052022858445)
  ·
    refine ⟨8882045410632394508571917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23685454428353052022858445 8882045410632394508571917)
    ·
      refine ⟨3330767028987147940714469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8882045410632394508571917 3330767028987147940714469)
      ·
        refine ⟨624518817935090238883963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3330767028987147940714469 624518817935090238883963)
        ·
          refine ⟨936778226902635358325945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624518817935090238883963 936778226902635358325945)
          ·
            refine ⟨702583670176976518744459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 936778226902635358325945 702583670176976518744459)
            ·
              refine ⟨1053875505265464778116689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702583670176976518744459 1053875505265464778116689)
              ·
                refine ⟨790406628949098583587517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1053875505265464778116689 790406628949098583587517)
                ·
                  refine ⟨296402485855911968845319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790406628949098583587517 296402485855911968845319)
                  ·
                    rfl

theorem cell20_649397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_649397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649397 prefixEnd_649397 := by exact prefixLift 649397
  have htrace : WordTrace (prefixWord ++ tailWord_649397) baseStart_649397 baseEnd_649397 := by
    simpa [prefixWord, tailWord_649397, baseEnd_649397] using wordTrace_append hprefix tailTrace_649397
  have hstable : (prefixWord ++ tailWord_649397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649397).length < 2 ^ (prefixWord ++ tailWord_649397).sum := by decide
  have hdescent : baseEnd_649397 < baseStart_649397 := by decide
  rcases family_descends (prefixWord ++ tailWord_649397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649408 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_649408 : Nat := 118140960795 + 649408 * 2 ^ 59
def prefixEnd_649408 : Nat := 4983230072969 + 3 ^ 40 * 649408 * 2
def baseEnd_649408 : Nat := 296407506555644819478607

theorem tailTrace_649408 : CollatzResearch.WordTrace tailWord_649408 prefixEnd_649408 296407506555644819478607 := by
  unfold tailWord_649408
  simp only [CollatzResearch.WordTrace]
  refine ⟨11842927815656600450754439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15790570420875467267672585 11842927815656600450754439)
  ·
    refine ⟨17764391723484900676131659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11842927815656600450754439 17764391723484900676131659)
    ·
      refine ⟨26646587585227351014197489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17764391723484900676131659 26646587585227351014197489)
      ·
        refine ⟨19984940688920513260648117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26646587585227351014197489 19984940688920513260648117)
        ·
          refine ⟨1873588189586298118185761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19984940688920513260648117 1873588189586298118185761)
          ·
            refine ⟨1405191142189723588639321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1873588189586298118185761 1405191142189723588639321)
            ·
              refine ⟨1053893356642292691479491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1405191142189723588639321 1053893356642292691479491)
              ·
                refine ⟨1580840034963439037219237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053893356642292691479491 1580840034963439037219237)
                ·
                  refine ⟨296407506555644819478607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1580840034963439037219237 296407506555644819478607)
                  ·
                    rfl

theorem cell20_649408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_649408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649408 prefixEnd_649408 := by exact prefixLift 649408
  have htrace : WordTrace (prefixWord ++ tailWord_649408) baseStart_649408 baseEnd_649408 := by
    simpa [prefixWord, tailWord_649408, baseEnd_649408] using wordTrace_append hprefix tailTrace_649408
  have hstable : (prefixWord ++ tailWord_649408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649408).length < 2 ^ (prefixWord ++ tailWord_649408).sum := by decide
  have hdescent : baseEnd_649408 < baseStart_649408 := by decide
  rcases family_descends (prefixWord ++ tailWord_649408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649432 : List Nat := [2, 1, 2, 2, 4, 3, 2, 4]
def baseStart_649432 : Nat := 118140960795 + 649432 * 2 ^ 59
def prefixEnd_649432 : Nat := 4983230072969 + 3 ^ 40 * 649432 * 2
def baseEnd_649432 : Nat := 98806153603202467559503

theorem tailTrace_649432 : CollatzResearch.WordTrace tailWord_649432 prefixEnd_649432 98806153603202467559503 := by
  unfold tailWord_649432
  simp only [CollatzResearch.WordTrace]
  refine ⟨11843365491613126500191275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15791153988817502000255033 11843365491613126500191275)
  ·
    refine ⟨17765048237419689750286913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11843365491613126500191275 17765048237419689750286913)
    ·
      refine ⟨13323786178064767312715185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17765048237419689750286913 13323786178064767312715185)
      ·
        refine ⟨9992839633548575484536389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13323786178064767312715185 9992839633548575484536389)
        ·
          refine ⟨1873657431290357903350573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9992839633548575484536389 1873657431290357903350573)
          ·
            refine ⟨702621536733884213756465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1873657431290357903350573 702621536733884213756465)
            ·
              refine ⟨526966152550413160317349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702621536733884213756465 526966152550413160317349)
              ·
                refine ⟨98806153603202467559503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 526966152550413160317349 98806153603202467559503)
                ·
                  rfl

theorem cell20_649432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_649432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649432 prefixEnd_649432 := by exact prefixLift 649432
  have htrace : WordTrace (prefixWord ++ tailWord_649432) baseStart_649432 baseEnd_649432 := by
    simpa [prefixWord, tailWord_649432, baseEnd_649432] using wordTrace_append hprefix tailTrace_649432
  have hstable : (prefixWord ++ tailWord_649432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649432).length < 2 ^ (prefixWord ++ tailWord_649432).sum := by decide
  have hdescent : baseEnd_649432 < baseStart_649432 := by decide
  rcases family_descends (prefixWord ++ tailWord_649432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649512 : List Nat := [2, 1, 5, 1, 11]
def baseStart_649512 : Nat := 118140960795 + 649512 * 2 ^ 59
def prefixEnd_649512 : Nat := 4983230072969 + 3 ^ 40 * 649512 * 2
def baseEnd_649512 : Nat := 3659937962833119506315

theorem tailTrace_649512 : CollatzResearch.WordTrace tailWord_649512 prefixEnd_649512 3659937962833119506315 := by
  unfold tailWord_649512
  simp only [CollatzResearch.WordTrace]
  refine ⟨11844824411468213331647395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15793099215290951108863193 11844824411468213331647395)
  ·
    refine ⟨17767236617202319997471093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11844824411468213331647395 17767236617202319997471093)
    ·
      refine ⟨1665678432862717499762915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17767236617202319997471093 1665678432862717499762915)
      ·
        refine ⟨2498517649294076249644373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1665678432862717499762915 2498517649294076249644373)
        ·
          refine ⟨3659937962833119506315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2498517649294076249644373 3659937962833119506315)
          ·
            rfl

theorem cell20_649512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 11].length) (baseStart_649512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649512 prefixEnd_649512 := by exact prefixLift 649512
  have htrace : WordTrace (prefixWord ++ tailWord_649512) baseStart_649512 baseEnd_649512 := by
    simpa [prefixWord, tailWord_649512, baseEnd_649512] using wordTrace_append hprefix tailTrace_649512
  have hstable : (prefixWord ++ tailWord_649512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649512).length < 2 ^ (prefixWord ++ tailWord_649512).sum := by decide
  have hdescent : baseEnd_649512 < baseStart_649512 := by decide
  rcases family_descends (prefixWord ++ tailWord_649512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649514 : List Nat := [3, 1, 4, 2, 3, 1, 2, 2, 2]
def baseStart_649514 : Nat := 118140960795 + 649514 * 2 ^ 59
def prefixEnd_649514 : Nat := 4983230072969 + 3 ^ 40 * 649514 * 2
def baseEnd_649514 : Nat := 296455887843979561944841

theorem tailTrace_649514 : CollatzResearch.WordTrace tailWord_649514 prefixEnd_649514 296455887843979561944841 := by
  unfold tailWord_649514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5922430442232295251216899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15793147845952787336578397 5922430442232295251216899)
  ·
    refine ⟨8883645663348442876825349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5922430442232295251216899 8883645663348442876825349)
    ·
      refine ⟨1665683561877833039404753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8883645663348442876825349 1665683561877833039404753)
      ·
        refine ⟨1249262671408374779553565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1665683561877833039404753 1249262671408374779553565)
        ·
          refine ⟨468473501778140542332587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1249262671408374779553565 468473501778140542332587)
          ·
            refine ⟨702710252667210813498881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468473501778140542332587 702710252667210813498881)
            ·
              refine ⟨527032689500408110124161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702710252667210813498881 527032689500408110124161)
              ·
                refine ⟨395274517125306082593121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527032689500408110124161 395274517125306082593121)
                ·
                  refine ⟨296455887843979561944841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395274517125306082593121 296455887843979561944841)
                  ·
                    rfl

theorem cell20_649514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_649514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649514 prefixEnd_649514 := by exact prefixLift 649514
  have htrace : WordTrace (prefixWord ++ tailWord_649514) baseStart_649514 baseEnd_649514 := by
    simpa [prefixWord, tailWord_649514, baseEnd_649514] using wordTrace_append hprefix tailTrace_649514
  have hstable : (prefixWord ++ tailWord_649514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649514).length < 2 ^ (prefixWord ++ tailWord_649514).sum := by decide
  have hdescent : baseEnd_649514 < baseStart_649514 := by decide
  rcases family_descends (prefixWord ++ tailWord_649514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649519 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 5]
def baseStart_649519 : Nat := 118140960795 + 649519 * 2 ^ 59
def prefixEnd_649519 : Nat := 4983230072969 + 3 ^ 40 * 649519 * 2
def baseEnd_649519 : Nat := 296458169980221766778153

theorem tailTrace_649519 : CollatzResearch.WordTrace tailWord_649519 prefixEnd_649519 296458169980221766778153 := by
  unfold tailWord_649519
  simp only [CollatzResearch.WordTrace]
  refine ⟨23689904133911066858799611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15793269422607377905866407 23689904133911066858799611)
  ·
    refine ⟨35534856200866600288199417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23689904133911066858799611 35534856200866600288199417)
    ·
      refine ⟨26651142150649950216149563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35534856200866600288199417 26651142150649950216149563)
      ·
        refine ⟨39976713225974925324224345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26651142150649950216149563 39976713225974925324224345)
        ·
          refine ⟨29982534919481193993168259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39976713225974925324224345 29982534919481193993168259)
          ·
            refine ⟨44973802379221790989752389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29982534919481193993168259 44973802379221790989752389)
            ·
              refine ⟨8432587946104085810578573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44973802379221790989752389 8432587946104085810578573)
              ·
                refine ⟨3162220479789032178966965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8432587946104085810578573 3162220479789032178966965)
                ·
                  refine ⟨296458169980221766778153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3162220479789032178966965 296458169980221766778153)
                  ·
                    rfl

theorem cell20_649519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_649519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649519 prefixEnd_649519 := by exact prefixLift 649519
  have htrace : WordTrace (prefixWord ++ tailWord_649519) baseStart_649519 baseEnd_649519 := by
    simpa [prefixWord, tailWord_649519, baseEnd_649519] using wordTrace_append hprefix tailTrace_649519
  have hstable : (prefixWord ++ tailWord_649519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649519).length < 2 ^ (prefixWord ++ tailWord_649519).sum := by decide
  have hdescent : baseEnd_649519 < baseStart_649519 := by decide
  rcases family_descends (prefixWord ++ tailWord_649519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649529 : List Nat := [1, 2, 1, 6, 1, 1, 3, 5]
def baseStart_649529 : Nat := 118140960795 + 649529 * 2 ^ 59
def prefixEnd_649529 : Nat := 4983230072969 + 3 ^ 40 * 649529 * 2
def baseEnd_649529 : Nat := 98820911417568725481593

theorem tailTrace_649529 : CollatzResearch.WordTrace tailWord_649529 prefixEnd_649529 98820911417568725481593 := by
  unfold tailWord_649529
  simp only [CollatzResearch.WordTrace]
  refine ⟨23690268863874838566663641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15793512575916559044442427 23690268863874838566663641)
  ·
    refine ⟨17767701647906128924997731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23690268863874838566663641 17767701647906128924997731)
    ·
      refine ⟨26651552471859193387496597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17767701647906128924997731 26651552471859193387496597)
      ·
        refine ⟨1249291522118399690038903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26651552471859193387496597 1249291522118399690038903)
        ·
          refine ⟨1873937283177599535058355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249291522118399690038903 1873937283177599535058355)
          ·
            refine ⟨2810905924766399302587533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873937283177599535058355 2810905924766399302587533)
            ·
              refine ⟨1054089721787399738470325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2810905924766399302587533 1054089721787399738470325)
              ·
                refine ⟨98820911417568725481593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1054089721787399738470325 98820911417568725481593)
                ·
                  rfl

theorem cell20_649529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_649529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649529 prefixEnd_649529 := by exact prefixLift 649529
  have htrace : WordTrace (prefixWord ++ tailWord_649529) baseStart_649529 baseEnd_649529 := by
    simpa [prefixWord, tailWord_649529, baseEnd_649529] using wordTrace_append hprefix tailTrace_649529
  have hstable : (prefixWord ++ tailWord_649529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649529).length < 2 ^ (prefixWord ++ tailWord_649529).sum := by decide
  have hdescent : baseEnd_649529 < baseStart_649529 := by decide
  rcases family_descends (prefixWord ++ tailWord_649529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649543 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 4]
def baseStart_649543 : Nat := 118140960795 + 649543 * 2 ^ 59
def prefixEnd_649543 : Nat := 4983230072969 + 3 ^ 40 * 649543 * 2
def baseEnd_649543 : Nat := 296469124234184349978055

theorem tailTrace_649543 : CollatzResearch.WordTrace tailWord_649543 prefixEnd_649543 296469124234184349978055 := by
  unfold tailWord_649543
  simp only [CollatzResearch.WordTrace]
  refine ⟨23690779485824118957673283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15793852990549412638448855 23690779485824118957673283)
  ·
    refine ⟨35536169228736178436509925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23690779485824118957673283 35536169228736178436509925)
    ·
      refine ⟨6663031730388033456845611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35536169228736178436509925 6663031730388033456845611)
      ·
        refine ⟨9994547595582050185268417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6663031730388033456845611 9994547595582050185268417)
        ·
          refine ⟨7495910696686537638951313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9994547595582050185268417 7495910696686537638951313)
          ·
            refine ⟨5621933022514903229213485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7495910696686537638951313 5621933022514903229213485)
            ·
              refine ⟨2108224883443088710955057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5621933022514903229213485 2108224883443088710955057)
              ·
                refine ⟨1581168662582316533216293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2108224883443088710955057 1581168662582316533216293)
                ·
                  refine ⟨296469124234184349978055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581168662582316533216293 296469124234184349978055)
                  ·
                    rfl

theorem cell20_649543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_649543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649543 prefixEnd_649543 := by exact prefixLift 649543
  have htrace : WordTrace (prefixWord ++ tailWord_649543) baseStart_649543 baseEnd_649543 := by
    simpa [prefixWord, tailWord_649543, baseEnd_649543] using wordTrace_append hprefix tailTrace_649543
  have hstable : (prefixWord ++ tailWord_649543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649543).length < 2 ^ (prefixWord ++ tailWord_649543).sum := by decide
  have hdescent : baseEnd_649543 < baseStart_649543 := by decide
  rcases family_descends (prefixWord ++ tailWord_649543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649566 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_649566 : Nat := 118140960795 + 649566 * 2 ^ 59
def prefixEnd_649566 : Nat := 4983230072969 + 3 ^ 40 * 649566 * 2
def baseEnd_649566 : Nat := 296479622060898492211295

theorem tailTrace_649566 : CollatzResearch.WordTrace tailWord_649566 prefixEnd_649566 296479622060898492211295 := by
  unfold tailWord_649566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2961452295592599235720069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15794412243160529257173701 2961452295592599235720069)
  ·
    refine ⟨555272305423612356697513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2961452295592599235720069 555272305423612356697513)
    ·
      refine ⟨416454229067709267523135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 555272305423612356697513 416454229067709267523135)
      ·
        refine ⟨624681343601563901284703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416454229067709267523135 624681343601563901284703)
        ·
          refine ⟨937022015402345851927055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624681343601563901284703 937022015402345851927055)
          ·
            refine ⟨1405533023103518777890583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937022015402345851927055 1405533023103518777890583)
            ·
              refine ⟨2108299534655278166835875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405533023103518777890583 2108299534655278166835875)
              ·
                refine ⟨3162449301982917250253813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108299534655278166835875 3162449301982917250253813)
                ·
                  refine ⟨296479622060898492211295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3162449301982917250253813 296479622060898492211295)
                  ·
                    rfl

theorem cell20_649566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_649566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649566 prefixEnd_649566 := by exact prefixLift 649566
  have htrace : WordTrace (prefixWord ++ tailWord_649566) baseStart_649566 baseEnd_649566 := by
    simpa [prefixWord, tailWord_649566, baseEnd_649566] using wordTrace_append hprefix tailTrace_649566
  have hstable : (prefixWord ++ tailWord_649566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649566).length < 2 ^ (prefixWord ++ tailWord_649566).sum := by decide
  have hdescent : baseEnd_649566 < baseStart_649566 := by decide
  rcases family_descends (prefixWord ++ tailWord_649566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649570 : List Nat := [3, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_649570 : Nat := 118140960795 + 649570 * 2 ^ 59
def prefixEnd_649570 : Nat := 4983230072969 + 3 ^ 40 * 649570 * 2
def baseEnd_649570 : Nat := 296481447769892256077945

theorem tailTrace_649570 : CollatzResearch.WordTrace tailWord_649570 prefixEnd_649570 296481447769892256077945 := by
  unfold tailWord_649570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5922941064181575642226541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15794509504484201712604109 5922941064181575642226541)
  ·
    refine ⟨2221102899068090865834953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5922941064181575642226541 2221102899068090865834953)
    ·
      refine ⟨1665827174301068149376215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2221102899068090865834953 1665827174301068149376215)
      ·
        refine ⟨2498740761451602224064323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1665827174301068149376215 2498740761451602224064323)
        ·
          refine ⟨3748111142177403336096485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498740761451602224064323 3748111142177403336096485)
          ·
            refine ⟨702770839158263125518091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3748111142177403336096485 702770839158263125518091)
            ·
              refine ⟨1054156258737394688277137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702770839158263125518091 1054156258737394688277137)
              ·
                refine ⟨790617194053046016207853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1054156258737394688277137 790617194053046016207853)
                ·
                  refine ⟨296481447769892256077945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790617194053046016207853 296481447769892256077945)
                  ·
                    rfl

theorem cell20_649570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_649570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649570 prefixEnd_649570 := by exact prefixLift 649570
  have htrace : WordTrace (prefixWord ++ tailWord_649570) baseStart_649570 baseEnd_649570 := by
    simpa [prefixWord, tailWord_649570, baseEnd_649570] using wordTrace_append hprefix tailTrace_649570
  have hstable : (prefixWord ++ tailWord_649570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649570).length < 2 ^ (prefixWord ++ tailWord_649570).sum := by decide
  have hdescent : baseEnd_649570 < baseStart_649570 := by decide
  rcases family_descends (prefixWord ++ tailWord_649570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649626 : List Nat := [3, 1, 1, 4, 1, 2, 8]
def baseStart_649626 : Nat := 118140960795 + 649626 * 2 ^ 59
def prefixEnd_649626 : Nat := 4983230072969 + 3 ^ 40 * 649626 * 2
def baseEnd_649626 : Nat := 32945223077311661134561

theorem tailTrace_649626 : CollatzResearch.WordTrace tailWord_649626 prefixEnd_649626 32945223077311661134561 := by
  unfold tailWord_649626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5923451686130856033236183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15795871163015616088629821 5923451686130856033236183)
  ·
    refine ⟨8885177529196284049854275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5923451686130856033236183 8885177529196284049854275)
    ·
      refine ⟨13327766293794426074781413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8885177529196284049854275 13327766293794426074781413)
      ·
        refine ⟨2498956180086454889021515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13327766293794426074781413 2498956180086454889021515)
        ·
          refine ⟨3748434270129682333532273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498956180086454889021515 3748434270129682333532273)
          ·
            refine ⟨2811325702597261750149205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3748434270129682333532273 2811325702597261750149205)
            ·
              refine ⟨32945223077311661134561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2811325702597261750149205 32945223077311661134561)
              ·
                rfl

theorem cell20_649626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 8].length) (baseStart_649626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649626 prefixEnd_649626 := by exact prefixLift 649626
  have htrace : WordTrace (prefixWord ++ tailWord_649626) baseStart_649626 baseEnd_649626 := by
    simpa [prefixWord, tailWord_649626, baseEnd_649626] using wordTrace_append hprefix tailTrace_649626
  have hstable : (prefixWord ++ tailWord_649626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649626).length < 2 ^ (prefixWord ++ tailWord_649626).sum := by decide
  have hdescent : baseEnd_649626 < baseStart_649626 := by decide
  rcases family_descends (prefixWord ++ tailWord_649626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649636 : List Nat := [2, 3, 1, 2, 1, 1, 2, 6, 2]
def baseStart_649636 : Nat := 118140960795 + 649636 * 2 ^ 59
def prefixEnd_649636 : Nat := 4983230072969 + 3 ^ 40 * 649636 * 2
def baseEnd_649636 : Nat := 296511571968289359877675

theorem tailTrace_649636 : CollatzResearch.WordTrace tailWord_649636 prefixEnd_649636 296511571968289359877675 := by
  unfold tailWord_649636
  simp only [CollatzResearch.WordTrace]
  refine ⟨11847085737243597920404381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15796114316324797227205841 11847085737243597920404381)
  ·
    refine ⟨4442657151466349220151643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11847085737243597920404381 4442657151466349220151643)
    ·
      refine ⟨6663985727199523830227465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4442657151466349220151643 6663985727199523830227465)
      ·
        refine ⟨4997989295399642872670599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6663985727199523830227465 4997989295399642872670599)
        ·
          refine ⟨7496983943099464309005899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4997989295399642872670599 7496983943099464309005899)
          ·
            refine ⟨11245475914649196463508849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7496983943099464309005899 11245475914649196463508849)
            ·
              refine ⟨8434106935986897347631637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11245475914649196463508849 8434106935986897347631637)
              ·
                refine ⟨395348762624385813170233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8434106935986897347631637 395348762624385813170233)
                ·
                  refine ⟨296511571968289359877675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395348762624385813170233 296511571968289359877675)
                  ·
                    rfl

theorem cell20_649636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_649636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649636 prefixEnd_649636 := by exact prefixLift 649636
  have htrace : WordTrace (prefixWord ++ tailWord_649636) baseStart_649636 baseEnd_649636 := by
    simpa [prefixWord, tailWord_649636, baseEnd_649636] using wordTrace_append hprefix tailTrace_649636
  have hstable : (prefixWord ++ tailWord_649636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649636).length < 2 ^ (prefixWord ++ tailWord_649636).sum := by decide
  have hdescent : baseEnd_649636 < baseStart_649636 := by decide
  rcases family_descends (prefixWord ++ tailWord_649636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649650 : List Nat := [3, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_649650 : Nat := 118140960795 + 649650 * 2 ^ 59
def prefixEnd_649650 : Nat := 4983230072969 + 3 ^ 40 * 649650 * 2
def baseEnd_649650 : Nat := 296517961949767533410951

theorem tailTrace_649650 : CollatzResearch.WordTrace tailWord_649650 prefixEnd_649650 296517961949767533410951 := by
  unfold tailWord_649650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5923670524109119057954601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15796454730957650821212269 5923670524109119057954601)
  ·
    refine ⟨4442752893081839293465951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5923670524109119057954601 4442752893081839293465951)
    ·
      refine ⟨6664129339622758940198927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4442752893081839293465951 6664129339622758940198927)
      ·
        refine ⟨9996194009434138410298391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6664129339622758940198927 9996194009434138410298391)
        ·
          refine ⟨14994291014151207615447587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9996194009434138410298391 14994291014151207615447587)
          ·
            refine ⟨22491436521226811423171381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14994291014151207615447587 22491436521226811423171381)
            ·
              refine ⟨2108572173865013570922317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22491436521226811423171381 2108572173865013570922317)
              ·
                refine ⟨790714565199380089095869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2108572173865013570922317 790714565199380089095869)
                ·
                  refine ⟨296517961949767533410951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790714565199380089095869 296517961949767533410951)
                  ·
                    rfl

theorem cell20_649650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_649650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649650 prefixEnd_649650 := by exact prefixLift 649650
  have htrace : WordTrace (prefixWord ++ tailWord_649650) baseStart_649650 baseEnd_649650 := by
    simpa [prefixWord, tailWord_649650, baseEnd_649650] using wordTrace_append hprefix tailTrace_649650
  have hstable : (prefixWord ++ tailWord_649650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649650).length < 2 ^ (prefixWord ++ tailWord_649650).sum := by decide
  have hdescent : baseEnd_649650 < baseStart_649650 := by decide
  rcases family_descends (prefixWord ++ tailWord_649650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649674 : List Nat := [3, 1, 2, 1, 2, 2, 2, 5, 2]
def baseStart_649674 : Nat := 118140960795 + 649674 * 2 ^ 59
def prefixEnd_649674 : Nat := 4983230072969 + 3 ^ 40 * 649674 * 2
def baseEnd_649674 : Nat := 296528916203730116610853

theorem tailTrace_649674 : CollatzResearch.WordTrace tailWord_649674 prefixEnd_649674 296528916203730116610853 := by
  unfold tailWord_649674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5923889362087382082673019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15797038298899685553794717 5923889362087382082673019)
  ·
    refine ⟨8885834043131073124009529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5923889362087382082673019 8885834043131073124009529)
    ·
      refine ⟨6664375532348304843007147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8885834043131073124009529 6664375532348304843007147)
      ·
        refine ⟨9996563298522457264510721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6664375532348304843007147 9996563298522457264510721)
        ·
          refine ⟨7497422473891842948383041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9996563298522457264510721 7497422473891842948383041)
          ·
            refine ⟨5623066855418882211287281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7497422473891842948383041 5623066855418882211287281)
            ·
              refine ⟨4217300141564161658465461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5623066855418882211287281 4217300141564161658465461)
              ·
                refine ⟨395371888271640155481137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4217300141564161658465461 395371888271640155481137)
                ·
                  refine ⟨296528916203730116610853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395371888271640155481137 296528916203730116610853)
                  ·
                    rfl

theorem cell20_649674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_649674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649674 prefixEnd_649674 := by exact prefixLift 649674
  have htrace : WordTrace (prefixWord ++ tailWord_649674) baseStart_649674 baseEnd_649674 := by
    simpa [prefixWord, tailWord_649674, baseEnd_649674] using wordTrace_append hprefix tailTrace_649674
  have hstable : (prefixWord ++ tailWord_649674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649674).length < 2 ^ (prefixWord ++ tailWord_649674).sum := by decide
  have hdescent : baseEnd_649674 < baseStart_649674 := by decide
  rcases family_descends (prefixWord ++ tailWord_649674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649729 : List Nat := [1, 2, 4, 1, 3, 2, 2, 3, 2]
def baseStart_649729 : Nat := 118140960795 + 649729 * 2 ^ 59
def prefixEnd_649729 : Nat := 4983230072969 + 3 ^ 40 * 649729 * 2
def baseEnd_649729 : Nat := 296554019702394369777295

theorem tailTrace_649729 : CollatzResearch.WordTrace tailWord_649729 prefixEnd_649729 296554019702394369777295 := by
  unfold tailWord_649729
  simp only [CollatzResearch.WordTrace]
  refine ⟨23697563463150272723944241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15798375642100181815962827 23697563463150272723944241)
  ·
    refine ⟨17773172597362704542958181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23697563463150272723944241 17773172597362704542958181)
    ·
      refine ⟨3332469862005507101804659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17773172597362704542958181 3332469862005507101804659)
      ·
        refine ⟨4998704793008260652706989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3332469862005507101804659 4998704793008260652706989)
        ·
          refine ⟨1874514297378097744765121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4998704793008260652706989 1874514297378097744765121)
          ·
            refine ⟨1405885723033573308573841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1874514297378097744765121 1405885723033573308573841)
            ·
              refine ⟨1054414292275179981430381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1405885723033573308573841 1054414292275179981430381)
              ·
                refine ⟨395405359603192493036393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1054414292275179981430381 395405359603192493036393)
                ·
                  refine ⟨296554019702394369777295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395405359603192493036393 296554019702394369777295)
                  ·
                    rfl

theorem cell20_649729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 2].length) (baseStart_649729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649729 prefixEnd_649729 := by exact prefixLift 649729
  have htrace : WordTrace (prefixWord ++ tailWord_649729) baseStart_649729 baseEnd_649729 := by
    simpa [prefixWord, tailWord_649729, baseEnd_649729] using wordTrace_append hprefix tailTrace_649729
  have hstable : (prefixWord ++ tailWord_649729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649729).length < 2 ^ (prefixWord ++ tailWord_649729).sum := by decide
  have hdescent : baseEnd_649729 < baseStart_649729 := by decide
  rcases family_descends (prefixWord ++ tailWord_649729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649740 : List Nat := [2, 2, 1, 2, 4, 2, 7]
def baseStart_649740 : Nat := 118140960795 + 649740 * 2 ^ 59
def prefixEnd_649740 : Nat := 4983230072969 + 3 ^ 40 * 649740 * 2
def baseEnd_649740 : Nat := 32951004489125246712287

theorem tailTrace_649740 : CollatzResearch.WordTrace tailWord_649740 prefixEnd_649740 32951004489125246712287 := by
  unfold tailWord_649740
  simp only [CollatzResearch.WordTrace]
  refine ⟨11848982333055210801297337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15798643110740281068396449 11848982333055210801297337)
  ·
    refine ⟨8886736749791408100973003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11848982333055210801297337 8886736749791408100973003)
    ·
      refine ⟨13330105124687112151459505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8886736749791408100973003 13330105124687112151459505)
      ·
        refine ⟨9997578843515334113594629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13330105124687112151459505 9997578843515334113594629)
        ·
          refine ⟨1874546033159125146298993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9997578843515334113594629 1874546033159125146298993)
          ·
            refine ⟨1405909524869343859724245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1874546033159125146298993 1405909524869343859724245)
            ·
              refine ⟨32951004489125246712287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1405909524869343859724245 32951004489125246712287)
              ·
                rfl

theorem cell20_649740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 7].length) (baseStart_649740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649740 prefixEnd_649740 := by exact prefixLift 649740
  have htrace : WordTrace (prefixWord ++ tailWord_649740) baseStart_649740 baseEnd_649740 := by
    simpa [prefixWord, tailWord_649740, baseEnd_649740] using wordTrace_append hprefix tailTrace_649740
  have hstable : (prefixWord ++ tailWord_649740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649740).length < 2 ^ (prefixWord ++ tailWord_649740).sum := by decide
  have hdescent : baseEnd_649740 < baseStart_649740 := by decide
  rcases family_descends (prefixWord ++ tailWord_649740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649747 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 5]
def baseStart_649747 : Nat := 118140960795 + 649747 * 2 ^ 59
def prefixEnd_649747 : Nat := 4983230072969 + 3 ^ 40 * 649747 * 2
def baseEnd_649747 : Nat := 296562235392866307177221

theorem tailTrace_649747 : CollatzResearch.WordTrace tailWord_649747 prefixEnd_649747 296562235392866307177221 := by
  unfold tailWord_649747
  simp only [CollatzResearch.WordTrace]
  refine ⟨23698219977085061798099495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15798813318056707865399663 23698219977085061798099495)
  ·
    refine ⟨35547329965627592697149243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23698219977085061798099495 35547329965627592697149243)
    ·
      refine ⟨53320994948441389045723865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35547329965627592697149243 53320994948441389045723865)
      ·
        refine ⟨39990746211331041784292899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53320994948441389045723865 39990746211331041784292899)
        ·
          refine ⟨59986119316996562676439349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39990746211331041784292899 59986119316996562676439349)
          ·
            refine ⟨5623698685968427750916189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59986119316996562676439349 5623698685968427750916189)
            ·
              refine ⟨2108887007238160406593571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5623698685968427750916189 2108887007238160406593571)
              ·
                refine ⟨3163330510857240609890357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108887007238160406593571 3163330510857240609890357)
                ·
                  refine ⟨296562235392866307177221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3163330510857240609890357 296562235392866307177221)
                  ·
                    rfl

theorem cell20_649747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_649747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649747 prefixEnd_649747 := by exact prefixLift 649747
  have htrace : WordTrace (prefixWord ++ tailWord_649747) baseStart_649747 baseEnd_649747 := by
    simpa [prefixWord, tailWord_649747, baseEnd_649747] using wordTrace_append hprefix tailTrace_649747
  have hstable : (prefixWord ++ tailWord_649747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649747).length < 2 ^ (prefixWord ++ tailWord_649747).sum := by decide
  have hdescent : baseEnd_649747 < baseStart_649747 := by decide
  rcases family_descends (prefixWord ++ tailWord_649747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649760 : List Nat := [2, 1, 1, 6, 2, 1, 3, 1, 3]
def baseStart_649760 : Nat := 118140960795 + 649760 * 2 ^ 59
def prefixEnd_649760 : Nat := 4983230072969 + 3 ^ 40 * 649760 * 2
def baseEnd_649760 : Nat := 296568168947096039743835

theorem tailTrace_649760 : CollatzResearch.WordTrace tailWord_649760 prefixEnd_649760 296568168947096039743835 := by
  unfold tailWord_649760
  simp only [CollatzResearch.WordTrace]
  refine ⟨11849347063018982509161367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15799129417358643345548489 11849347063018982509161367)
  ·
    refine ⟨17774020594528473763742051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11849347063018982509161367 17774020594528473763742051)
    ·
      refine ⟨26661030891792710645613077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17774020594528473763742051 26661030891792710645613077)
      ·
        refine ⟨1249735823052783311513113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26661030891792710645613077 1249735823052783311513113)
        ·
          refine ⟨937301867289587483634835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1249735823052783311513113 937301867289587483634835)
          ·
            refine ⟨1405952800934381225452253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937301867289587483634835 1405952800934381225452253)
            ·
              refine ⟨527232300350392959544595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1405952800934381225452253 527232300350392959544595)
              ·
                refine ⟨790848450525589439316893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527232300350392959544595 790848450525589439316893)
                ·
                  refine ⟨296568168947096039743835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790848450525589439316893 296568168947096039743835)
                  ·
                    rfl

theorem cell20_649760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_649760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649760 prefixEnd_649760 := by exact prefixLift 649760
  have htrace : WordTrace (prefixWord ++ tailWord_649760) baseStart_649760 baseEnd_649760 := by
    simpa [prefixWord, tailWord_649760, baseEnd_649760] using wordTrace_append hprefix tailTrace_649760
  have hstable : (prefixWord ++ tailWord_649760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649760).length < 2 ^ (prefixWord ++ tailWord_649760).sum := by decide
  have hdescent : baseEnd_649760 < baseStart_649760 := by decide
  rcases family_descends (prefixWord ++ tailWord_649760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649780 : List Nat := [2, 5, 1, 3, 2, 1, 1, 3, 2]
def baseStart_649780 : Nat := 118140960795 + 649780 * 2 ^ 59
def prefixEnd_649780 : Nat := 4983230072969 + 3 ^ 40 * 649780 * 2
def baseEnd_649780 : Nat := 296577297492064859077087

theorem tailTrace_649780 : CollatzResearch.WordTrace tailWord_649780 prefixEnd_649780 296577297492064859077087 := by
  unfold tailWord_649780
  simp only [CollatzResearch.WordTrace]
  refine ⟨11849711792982754217025397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15799615723977005622700529 11849711792982754217025397)
  ·
    refine ⟨1110910480592133207846131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11849711792982754217025397 1110910480592133207846131)
    ·
      refine ⟨1666365720888199811769197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110910480592133207846131 1666365720888199811769197)
      ·
        refine ⟨624887145333074929413449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1666365720888199811769197 624887145333074929413449)
        ·
          refine ⟨468665358999806197060087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624887145333074929413449 468665358999806197060087)
          ·
            refine ⟨702998038499709295590131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468665358999806197060087 702998038499709295590131)
            ·
              refine ⟨1054497057749563943385197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702998038499709295590131 1054497057749563943385197)
              ·
                refine ⟨395436396656086478769449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1054497057749563943385197 395436396656086478769449)
                ·
                  refine ⟨296577297492064859077087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395436396656086478769449 296577297492064859077087)
                  ·
                    rfl

theorem cell20_649780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_649780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649780 prefixEnd_649780 := by exact prefixLift 649780
  have htrace : WordTrace (prefixWord ++ tailWord_649780) baseStart_649780 baseEnd_649780 := by
    simpa [prefixWord, tailWord_649780, baseEnd_649780] using wordTrace_append hprefix tailTrace_649780
  have hstable : (prefixWord ++ tailWord_649780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649780).length < 2 ^ (prefixWord ++ tailWord_649780).sum := by decide
  have hdescent : baseEnd_649780 < baseStart_649780 := by decide
  rcases family_descends (prefixWord ++ tailWord_649780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649785 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 7]
def baseStart_649785 : Nat := 118140960795 + 649785 * 2 ^ 59
def prefixEnd_649785 : Nat := 4983230072969 + 3 ^ 40 * 649785 * 2
def baseEnd_649785 : Nat := 296579579628307063910399

theorem tailTrace_649785 : CollatzResearch.WordTrace tailWord_649785 prefixEnd_649785 296579579628307063910399 := by
  unfold tailWord_649785
  simp only [CollatzResearch.WordTrace]
  refine ⟨23699605950947394287982809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15799737300631596191988539 23699605950947394287982809)
  ·
    refine ⟨17774704463210545715987107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23699605950947394287982809 17774704463210545715987107)
    ·
      refine ⟨26662056694815818573980661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17774704463210545715987107 26662056694815818573980661)
      ·
        refine ⟨2499567815138982991310687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26662056694815818573980661 2499567815138982991310687)
        ·
          refine ⟨3749351722708474486966031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2499567815138982991310687 3749351722708474486966031)
          ·
            refine ⟨5624027584062711730449047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749351722708474486966031 5624027584062711730449047)
            ·
              refine ⟨8436041376094067595673571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624027584062711730449047 8436041376094067595673571)
              ·
                refine ⟨12654062064141101393510357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8436041376094067595673571 12654062064141101393510357)
                ·
                  refine ⟨296579579628307063910399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12654062064141101393510357 296579579628307063910399)
                  ·
                    rfl

theorem cell20_649785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_649785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649785 prefixEnd_649785 := by exact prefixLift 649785
  have htrace : WordTrace (prefixWord ++ tailWord_649785) baseStart_649785 baseEnd_649785 := by
    simpa [prefixWord, tailWord_649785, baseEnd_649785] using wordTrace_append hprefix tailTrace_649785
  have hstable : (prefixWord ++ tailWord_649785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649785).length < 2 ^ (prefixWord ++ tailWord_649785).sum := by decide
  have hdescent : baseEnd_649785 < baseStart_649785 := by decide
  rcases family_descends (prefixWord ++ tailWord_649785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649792 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_649792 : Nat := 118140960795 + 649792 * 2 ^ 59
def prefixEnd_649792 : Nat := 4983230072969 + 3 ^ 40 * 649792 * 2
def baseEnd_649792 : Nat := 296582774619046150677037

theorem tailTrace_649792 : CollatzResearch.WordTrace tailWord_649792 prefixEnd_649792 296582774619046150677037 := by
  unfold tailWord_649792
  simp only [CollatzResearch.WordTrace]
  refine ⟨11849930630961017241743815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15799907507948022988991753 11849930630961017241743815)
  ·
    refine ⟨17774895946441525862615723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11849930630961017241743815 17774895946441525862615723)
    ·
      refine ⟨26662343919662288793923585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17774895946441525862615723 26662343919662288793923585)
      ·
        refine ⟨19996757939746716595442689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26662343919662288793923585 19996757939746716595442689)
        ·
          refine ⟨14997568454810037446582017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19996757939746716595442689 14997568454810037446582017)
          ·
            refine ⟨11248176341107528084936513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14997568454810037446582017 11248176341107528084936513)
            ·
              refine ⟨8436132255830646063702385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11248176341107528084936513 8436132255830646063702385)
              ·
                refine ⟨6327099191872984547776789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8436132255830646063702385 6327099191872984547776789)
                ·
                  refine ⟨296582774619046150677037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6327099191872984547776789 296582774619046150677037)
                  ·
                    rfl

theorem cell20_649792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_649792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649792 prefixEnd_649792 := by exact prefixLift 649792
  have htrace : WordTrace (prefixWord ++ tailWord_649792) baseStart_649792 baseEnd_649792 := by
    simpa [prefixWord, tailWord_649792, baseEnd_649792] using wordTrace_append hprefix tailTrace_649792
  have hstable : (prefixWord ++ tailWord_649792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649792).length < 2 ^ (prefixWord ++ tailWord_649792).sum := by decide
  have hdescent : baseEnd_649792 < baseStart_649792 := by decide
  rcases family_descends (prefixWord ++ tailWord_649792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649805 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 4]
def baseStart_649805 : Nat := 118140960795 + 649805 * 2 ^ 59
def prefixEnd_649805 : Nat := 4983230072969 + 3 ^ 40 * 649805 * 2
def baseEnd_649805 : Nat := 296588708173275883243651

theorem tailTrace_649805 : CollatzResearch.WordTrace tailWord_649805 prefixEnd_649805 296588708173275883243651 := by
  unfold tailWord_649805
  simp only [CollatzResearch.WordTrace]
  refine ⟨23700335410874937703710869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15800223607249958469140579 23700335410874937703710869)
  ·
    refine ⟨1110953222384762704861447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23700335410874937703710869 1110953222384762704861447)
    ·
      refine ⟨1666429833577144057292171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110953222384762704861447 1666429833577144057292171)
      ·
        refine ⟨2499644750365716085938257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1666429833577144057292171 2499644750365716085938257)
        ·
          refine ⟨1874733562774287064453693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2499644750365716085938257 1874733562774287064453693)
          ·
            refine ⟨703025086040357649170135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1874733562774287064453693 703025086040357649170135)
            ·
              refine ⟨1054537629060536473755203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703025086040357649170135 1054537629060536473755203)
              ·
                refine ⟨1581806443590804710632805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054537629060536473755203 1581806443590804710632805)
                ·
                  refine ⟨296588708173275883243651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581806443590804710632805 296588708173275883243651)
                  ·
                    rfl

theorem cell20_649805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_649805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649805 prefixEnd_649805 := by exact prefixLift 649805
  have htrace : WordTrace (prefixWord ++ tailWord_649805) baseStart_649805 baseEnd_649805 := by
    simpa [prefixWord, tailWord_649805, baseEnd_649805] using wordTrace_append hprefix tailTrace_649805
  have hstable : (prefixWord ++ tailWord_649805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649805).length < 2 ^ (prefixWord ++ tailWord_649805).sum := by decide
  have hdescent : baseEnd_649805 < baseStart_649805 := by decide
  rcases family_descends (prefixWord ++ tailWord_649805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649809 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 4]
def baseStart_649809 : Nat := 118140960795 + 649809 * 2 ^ 59
def prefixEnd_649809 : Nat := 4983230072969 + 3 ^ 40 * 649809 * 2
def baseEnd_649809 : Nat := 296590533882269647110301

theorem tailTrace_649809 : CollatzResearch.WordTrace tailWord_649809 prefixEnd_649809 296590533882269647110301 := by
  unfold tailWord_649809
  simp only [CollatzResearch.WordTrace]
  refine ⟨23700481302860446386856481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15800320868573630924570987 23700481302860446386856481)
  ·
    refine ⟨17775360977145334790142361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23700481302860446386856481 17775360977145334790142361)
    ·
      refine ⟨13331520732859001092606771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17775360977145334790142361 13331520732859001092606771)
      ·
        refine ⟨19997281099288501638910157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13331520732859001092606771 19997281099288501638910157)
        ·
          refine ⟨7498980412233188114591309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19997281099288501638910157 7498980412233188114591309)
          ·
            refine ⟨2812117654587445542971741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7498980412233188114591309 2812117654587445542971741)
            ·
              refine ⟨1054544120470292078614403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2812117654587445542971741 1054544120470292078614403)
              ·
                refine ⟨1581816180705438117921605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054544120470292078614403 1581816180705438117921605)
                ·
                  refine ⟨296590533882269647110301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581816180705438117921605 296590533882269647110301)
                  ·
                    rfl

theorem cell20_649809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_649809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_649809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_649809 prefixEnd_649809 := by exact prefixLift 649809
  have htrace : WordTrace (prefixWord ++ tailWord_649809) baseStart_649809 baseEnd_649809 := by
    simpa [prefixWord, tailWord_649809, baseEnd_649809] using wordTrace_append hprefix tailTrace_649809
  have hstable : (prefixWord ++ tailWord_649809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649809).length < 2 ^ (prefixWord ++ tailWord_649809).sum := by decide
  have hdescent : baseEnd_649809 < baseStart_649809 := by decide
  rcases family_descends (prefixWord ++ tailWord_649809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
